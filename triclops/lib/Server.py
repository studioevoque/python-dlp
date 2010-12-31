#!/usr/bin/env python
"""
A (Paste-based) WSGI implementation of the SPARQL Protocol ala RDF Kendall Grant Clark, W3C, et. al. 2006

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.    
"""
import os, getopt, sys, re, time, urllib, codecs,itertools
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib import URIRef, store, plugin, RDF, BNode, Literal, RDFS
from rdflib.Namespace import Namespace
from rdflib.util import first
from rdflib.store import Store
from rdflib.store.MySQL import ParseConfigurationString
from rdflib.sparql.QueryResult import SPARQL_XML_NAMESPACE
from rdflib.sparql.bison.Query import Query
from rdflib.sparql.parser import parse
from Ft.Xml.Xslt import Processor
from Ft.Lib.Uri import OsPathToUri
from Ft.Xml import InputSource
from Ft.Xml.Domlette import NonvalidatingReader
from Ft.Xml.Domlette import Print, PrettyPrint
from cStringIO import StringIO
from rdflib.store.MySQL import ParseConfigurationString
from paste.request import parse_formvars
import rdflib
ticketLookup = {}

SPARQL= Namespace('http://www.topbraidcomposer.org/owl/2006/09/sparql.owl#')
OWL_NS=Namespace('http://www.w3.org/2002/07/owl#')
TEMPLATES = Namespace('http://code.google.com/p/fuxi/wiki/BuiltinSPARQLTemplates#')

OWL_PROPERTIES_QUERY=\
"""
SELECT ?literalProperty ?resourceProperty
WHERE {
    { ?literalProperty a owl:DatatypeProperty }
                    UNION
    { ?resourceProperty a ?propType 
      FILTER( 
        ?propType = owl:ObjectProperty || 
        ?propType = owl:TransitiveProperty ||
        ?propType = owl:SymmetricProperty ||
        ?propType = owl:InverseFunctionalProperty )  }
}"""

WRONG_URL_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>SPARQL Endpoint</title>
  </head>
  <body>
      <h1 class="title">Wrong URL</h1>
      The SPARQL service path is: <a href='%s'>%s</a>
  </body>
</body>"""

VISUALIZATION_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>SPARQL Endpoint Browser</title>
  </head>
  <body>
      <h1>SPARQL Endpoint Browser</h1>
      %s
      <div>[%s]</div>
  </body>
</body>
"""

BROWSER_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>SPARQL Endpoint Browser</title>
  </head>
  <body>
      <h1>SPARQL Endpoint Browser</h1>
      %s
      <div>[<a href="%s">Return</a>]</div>
  </body>
</body>"""

SPARQL_FORM=\
"""
<?xml version="1.0" encoding="utf-8"?>
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">
  <head>
    <title>SPARQL Query Editor</title>
     <script>
function submitQuery(formId) {
    document.getElementById(formId).submit();
}     
function submitQueryStop(formId){
    document.getElementById(formId).action="/processes";
    document.getElementById(formId).submit();
}
function getTicket(formId){
    document.getElementById(formId).method="get";
    document.getElementById(formId).action="/ticket";
    document.getElementById(formId).submit();
}
     </script>
  </head>
  <body>
    <div style="margin-right: 10em">
      <h2>SPARQL</h2>
      <p>See: <a href="http://www.w3.org/TR/rdf-sparql-query">SPARQL Query Language for RDF</a></p>
      <p>See: <a href="/processes" target="_blank">process manager</a> for a list of running queries and links for killing a particular query</p>
      ENTAILMENT
      <table>
        <thead>
            <tr><td colspan='2'>Preset namespace bindings</td></tr>
        </thead>
        <tbody>BINDINGS</tbody>
      </table>
      <form id="queryform" action="ENDPOINT" method="post">
        <!--hidden ticket-->
        <div>
          <select name="resultFormat">
            <option value="xml" selected="on">SPARQL XML (rendered as XHTML)</OPTION>
            <option value="csv">SPARQL XML (rendered as tab delimited)</OPTION>
            <option value="csv-pure">Tab delimited</OPTION>
          </select>        
        </div>
        Default Grap IRI: <input type="text" size="80" name="default-graph-uri" id="default-graph-uri" value=""/>
        <div>
          <textarea style="width: 80%" name="query" rows="20" id="querytext">
BASE &lt;http://www.clevelandclinic.org/heartcenter/ontologies/DataNodes.owl#>
   PREFIX ptrec: &lt;tag:info@semanticdb.ccf.org,2007:PatientRecordTerms#>
   PREFIX xsd: &lt;http://www.w3.org/2001/XMLSchema#> 
   SELECT   ?ccfId ?PROC ?SITE
   WHERE { ?proc a &lt;tag:info@semanticdb.ccf.org,2007:PatientRecordTerms#SurgicalProcedure-vascular-endovascular%20procedure>.
           ?proc :contains [ a ptrec:VascularProcedure ; 
                             ptrec:hasVascularProcedureName ?PROC;
                             ptrec:hasVascularProcedureSite ?SITE ].
           ?evt :contains ?proc.
           ?ptrec :contains ?evt, [ a ptrec:Patient; ptrec:hasCCFID ?ccfId ] }
          </textarea>
          <div><input type="button" value="Submit SPARQL" onClick="submitQuery('queryform')" />
               <!--CancelButton-->
          </div>
        </div>        
      </form>
    </div>
    <ul>
      <li>
        All <a href="/browse?action=classes">Classes</a>
      </li>
      <li>
        <a href="/about">About</a> the triple store
      </li>
    </ul>
    <form id="browseform" action="/browse" method="get">
      <span style="font-weight:bold">URI: </span> <input name="uri" type="input" size="80"/>
      <select name="action">
        <option value="extension">Class extension</OPTION>
        <option value="extension-size">Class extension size</OPTION>
        <option value="resource">Browse resource</OPTION>
      </select>
      <input type="submit" label="Browse" onClick="submitQuery('browseform')"/>
    </form>
    <div style="font-size: 10pt; margin: 0 1.8em 1em 0; text-align: center;">Powered by <a href="http://rdflib.net">rdflib</a> (<em><strong>RDF</strong></em>), <a href="http://pythonpaste.org/">Python Paste</a> (<em><strong>HTTP</strong></em>), and <a href="http://4suite.org">4Suite</a> (<em><strong>XML</strong></em>)</div>
  </body>
</html>
"""

ENTAILMENT_HTML=\
"""
<?xml version="1.0" encoding="utf-8"?>
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">
  <head>
    <title>SPARQL Entailment Regime Summary</title>
  </head>
  <body>
    <div style="margin-right: 10em">
      <h2>SPARQL Entailment</h2>
      <p>See: <a href="http://www.w3.org/TR/sparql11-entailment/" target='_blank'>SPARQL 1.1 Entailment Regimes</a></p>
      <p>The following predicates and classes can be used in a query and the background ontology
      and rules (which include the semantics for these terms) will be used to compute answers to the query</p>
      <ul>
          %s
      </ul>
      The following ruleset(s) and ontologies are the basis for the entailment:
      <ul>
          %s
      </ul>
    </div>
  </body>
</html>"""

def makeTermHTML(server,term,noLink=False,aProp=False,targetGraph=None):
    """
    Takes a term and turns into an HTML snippet for the browse view, taking care of 
      quoting, etc.
    - noLink indicates whether or not to make it a link
    - aProp indicates whether this term is a property in a statememtn
    """
    print "Term: ", term
    if isinstance(term,URIRef):
        if aProp:
            qString = urllib.quote("""SELECT ?S ?O WHERE { ?S <%s> ?O } """%term)
            return noLink and '%s'%term or '<a href="%s?query=%s">%s</a>'%(server.endpoint,
                                                                           qString,getURIPrettyString(term,server.nsBindings))
        else:
            return noLink and '%s'%term or \
            '<a href="/browse?action=resource&amp;uri=%s">%s</a>'%(urllib.quote(term),
                                                                   getURIPrettyString(addType(term,targetGraph),server.nsBindings))
    elif isinstance(term,BNode):
        return noLink and '%s'%term.n3() or \
        '<a href="/browse?action=resource&amp;uri=%s">%s</a>'%(urllib.quote(term.n3()),
                                                               addType(term,targetGraph))
    else:
        return term.n3()

def getURIPrettyString(uri,nsBindings,dontEscape=False):
    for key,val in nsBindings.items():
        if uri.find(val)!=-1: 
            uri = uri.replace(val,'%s:'%key)
    return dontEscape and uri or unescapeHTML(uri)

def topList(node,g):
    for s in g.subjects(RDF.rest,node):
        yield s

class StoreConnectee(object):
    """
    Superclass for all WSGI applications
    Stores global configuration and provides a method for retrieving
    the underlying SPARQL service graph
    """            
    def __init__(self, 
                 global_conf, 
                 nsBindings = {}, 
                 defaultDerivedPreds = [],
                 litProps = None, 
                 resProps = None,
                 definingOntology = None,
                 ontGraph = None,
                 ruleSet = None,
                 builtinTemplateGraph = None):
        self.builtinTemplateGraph = builtinTemplateGraph
        self.ruleSet = ruleSet
        self.definingOntology   = definingOntology
        self.ontGraph           = ontGraph
        self.store_id           = global_conf.get('store_identifier')
        self.connection         = global_conf.get('connection')
        self.storeKind          = global_conf.get('store')
        self.layout             = global_conf.get('graphVizLayout')
        self.vizualization      = global_conf.get('visualization')
        self.endpoint           = global_conf['endpoint']
        self.litProps           = litProps
        self.resProps           = resProps
        self.nsBindings         = nsBindings
        self.defaultDerivedPreds= defaultDerivedPreds
        self.entailmentN3       = global_conf.get('entailment_n3')
        self.dataStoreOWL       = global_conf.get('datastore_owl')
        self.topDownEntailment  = global_conf.get('topDownEntailment',False)
        self.debugQuery         = global_conf.get('debugQuery',False)
        self.ignoreBase         = global_conf.get('NO_BASE_RESOLUTION',False)
        self.ignoreQueryDataset = global_conf.get('IgnoreQueryDataset',False)
        MYSQL_ORDER             = global_conf.get('MYSQL_ORDER',False)
        noFilterEstimation      = global_conf.get('DISABLE_SELECTION_ESTIMATION',False)
        self.proxy              = global_conf.get('sparql_proxy')
        self.bNodeAsURI         = global_conf.get('bNodeAsURI')
        if self.proxy:
            print "A proxy SPARQL server for ", self.proxy
        elif MYSQL_ORDER or noFilterEstimation:
            #modification to the SPARQL evaluation methods
            from rdflib.sparql.sql.RdfSqlBuilder import DEFAULT_OPT_FLAGS, \
                OPT_JOIN_GREEDY_STOCKER_STATS, OPT_JOIN_GREEDY_SELECTION
            if MYSQL_ORDER:
                DEFAULT_OPT_FLAGS[OPT_JOIN_GREEDY_STOCKER_STATS]=False
                DEFAULT_OPT_FLAGS[OPT_JOIN_GREEDY_SELECTION]    =False
                assert not noFilterEstimation,"Cannot use both MYSQL_ORDER and DISABLE_SELECTION_ESTIMATION!"
            elif noFilterEstimation:
                DEFAULT_OPT_FLAGS[OPT_JOIN_GREEDY_SELECTION]    =False
                        
        from rdflib.sparql import Algebra
        Algebra.DAWG_DATASET_COMPLIANCE = False
        
        self.csvProcessor = Processor.Processor()
        transform = InputSource.DefaultFactory.fromUri(OsPathToUri('htdocs/xslt/xml-to-csv.xslt'))
        self.csvProcessor.appendStylesheet(transform)

    def buildGraph(self,default_graph_uri=None):
        if self.proxy:
            store = plugin.get('SPARQL',Store)(self.proxy,bNodeAsURI = self.bNodeAsURI)
        else:
            store = plugin.get(self.storeKind,Store)(self.store_id)
            store.open(self.connection,create=False)
            #The MySQL store has a special set of attribute for optimizing
            #SPARQL queries based on the characteristics of RDF properties
            #used in the queries
            if self.storeKind == 'MySQL' and self.dataStoreOWL:
                print "Updating the property optimization parameters to the store"
                store.literal_properties = self.litProps
                store.resource_properties= self.resProps
        if default_graph_uri:
            targetGraph = Graph(store,identifier = URIRef(default_graph_uri))
        else:
            targetGraph = ConjunctiveGraph(store)
            
        return targetGraph
    
class EntailmentManager(StoreConnectee):
    """
    WSGI Application for displaying information about entailment regime
    """
    def __init__(self,
                 global_conf,
                 nsBindings,
                 defaultDerivedPreds,
                 litProps,
                 resProps,
                 definingOntology,
                 ontGraph,
                 ruleSet,
                 builtinTemplateGraph):
        super(EntailmentManager, self).__init__(global_conf,
                                                nsBindings,
                                                defaultDerivedPreds,
                                                litProps,
                                                resProps,
                                                definingOntology,
                                                ontGraph,
                                                ruleSet,
                                                builtinTemplateGraph)
        self.entailmentN3        = global_conf.get('entailment_n3')
        
    def __call__(self, environ, start_response):
        status = '200 OK'
        #The client is requesting a SPARQL form with the ticket
        #embedded as a hidden parameter
        retVal=ENTAILMENT_HTML%('\n'.join(
                                ['<li>%s</li>'%self.ontGraph.qname(pred) 
                                    for pred in 
                                 self.defaultDerivedPreds]),
                                 '\n'.join(['<li>%s</li>'%theory 
                                    for theory in itertools.chain(
                                          self.definingOntology.split(','),
                                          self.entailmentN3.split(','))]))
        response_headers = [('Content-type','text/html'),
                            ('Content-Length',
                             len(retVal))]
        start_response(status, response_headers)
        yield retVal

class TicketManager(StoreConnectee):
    """
    WSGI Application for retrieving a ticket or a form with a new ticket embedded
    """
    def __call__(self, environ, start_response):
        d = parse_formvars(environ)
        action = d.get('type')
        status = '200 OK'
        from Ft.Lib.Uuid import UuidAsString, GenerateUuid
        token=UuidAsString(GenerateUuid())        
        if action == 'id':
            #The client is requesting a ticket to use for a subsequent 
            #SPARQL query such that it can be aborted using this ticket
            response_headers = [('Content-type','text/plain'),
                                ('Content-Length',len(token))]
            start_response(status, response_headers)
            yield token
        else:
            #The client is requesting a SPARQL form with the ticket
            #embedded as a hidden parameter
            retVal=SPARQL_FORM.replace('ENDPOINT',self.endpoint)
            entailmentRepl=''
            if self.topDownEntailment:
                entailmentRepl = '<div><em>This server has an <strong><a href="/entailment">active</a></strong> entailment regime!</em></div><br/>'
            retVal=retVal.replace('ENTAILMENT',entailmentRepl)
            retVal=retVal.replace('<!--hidden ticket-->',
                           '<input type="hidden" name="ticket" value="%s"></input>'%token)
            retVal=retVal.replace('<!--CancelButton-->',
                           '<input type="button" value="Cancel Query" onClick="submitQueryStop(\'queryform\')"></input>')
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',
                                 len(retVal))]
            start_response(status, response_headers)
            yield retVal

class Browser(StoreConnectee):
    """
    WSGI Application for browsing resources behind the SPARQL service
    """
    def __call__(self, environ, start_response):
        d = parse_formvars(environ)
        action = d.get('action')
        status = '200 OK'
        targetGraph = self.buildGraph()
        if action == 'classes':
            def makeClassLink(c):
                if isinstance(c,BNode):
                    c = c.n3()
                    uri = urllib.quote(c)
                else:
                    uri = urllib.quote(c)
                return """<li><span style="font-size:8pt;font-style:italics"><a href="/browse?action=extension&amp;uri=%s">%s</a></span></li>"""%(uri,c)
            _l='\n'.join([makeClassLink(klass) for klass in \
                              set(targetGraph.objects(predicate=RDF.type))])
            body = "<h3>Classes</3><ul>%s</ul>"%_l
            targetGraph.close()
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',len(BROWSER_HTML%(body,
                                                                    self.endpoint)))]
            start_response(status, response_headers)
            return [BROWSER_HTML%(body,self.endpoint)]
        elif action == 'extension':
            targetClass = d['uri']
            def makeMemberLink(m):
                if isinstance(m,BNode):
                    m = m.n3()
                    uri = urllib.quote(m)
                else:
                    uri = urllib.quote(m)
                return """<li><span style="font-size:8pt;font-style:italics"><a href="/browse?action=resource&amp;uri=%s">%s</a></span></li>"""%(uri,m)
            _l='\n'.join([makeMemberLink(member) for member in \
                              set(targetGraph.subjects(predicate=RDF.type,
                                                       object=URIRef(targetClass)))])
            body = "<h3>Extension of %s</h3><ul>%s</ul>"%(targetClass,_l)
            targetGraph.close()
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',len(BROWSER_HTML%(body,self.endpoint)))]
            start_response(status, response_headers)
            return [BROWSER_HTML%(body,self.endpoint)]
        elif action == 'extension-size':
            targetClass = d['uri']
            size=len(set(targetGraph.subjects(predicate=RDF.type,
                                              object=URIRef(targetClass))))
            body = \
            """<h3>Extension cardinality</h3>
            <p style="font-size:10pt">The class identified by the URI &lt;%s> has <em>%s</em> members.</p>"""%(targetClass,size)
            targetGraph.close()
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',len(BROWSER_HTML%(body,self.endpoint)))]
            start_response(status, response_headers)
            return [BROWSER_HTML%(body,self.endpoint)]
        elif action == 'resource':
            res = d['uri']
            row = 0
            rows = []
            resTerm = res.startswith('_:') and BNode(res[2:]) or URIRef(res)
            iter = targetGraph.triples((resTerm,None,None))
            for s,p,o in iter:
                if row == 0:
                    newRow = ("""<tr><td valign="center" align="middle" rowspan='%s'>%s</td><td>%s</td><td>%s</td></tr>""",[
                                                                                                        makeTermHTML(self,s,noLink=True,targetGraph=targetGraph),
                                                                                                        makeTermHTML(self,p,aProp=True,targetGraph=targetGraph),
                                                                                                        makeTermHTML(self,o,targetGraph=targetGraph)])
                else:
                    newRow = ("""<tr><td>%s</td><td>%s</td></tr>""",
                              (makeTermHTML(self,p,aProp=True,targetGraph=targetGraph),
                               makeTermHTML(self,o,targetGraph=targetGraph)))
                row += 1
                rows.append(newRow)
            row2 = 0
            for s,p,o in targetGraph.triples((None,None,resTerm)):
                if row2 == 0:
                    newRow = ("""<tr><td>%s</td><td>%s</td><td valign="center" align="middle" rowspan='%s'>%s</td></tr>""",[
                                                                                                        makeTermHTML(self,s,targetGraph=targetGraph),
                                                                                                        makeTermHTML(self,p,aProp=True,targetGraph=targetGraph),
                                                                                                        makeTermHTML(self,o,noLink=True,targetGraph=targetGraph)])
                else:
                    newRow = ("""<tr><td>%s</td><td>%s</td></tr>""",
                              (makeTermHTML(self,s,targetGraph=targetGraph),
                               makeTermHTML(self,p,aProp=True,targetGraph=targetGraph)))
                row2 += 1
                rows.append(newRow)
            if row:
                #try:
                rows[0] = rows[0][0]%tuple([row]+rows[0][-1])
                if row > 1:
                    rows[1:row] = [s%vals for s,vals in rows[1:row]]
            if row2:
                rows[row] = rows[row][0]%tuple(rows[row][-1][:-1]+[row2]+[rows[row][-1][-1]])
                if row2 > 1:
                    rows[row+1:] = [s%vals for s,vals in rows[row+1:]]
                rows = rows[:row]+["<tr><th align='middle' colspan='3'>Outgoing Statements</th></tr>"]+rows[row:]
            instr="<div style='font-size:8pt'>Clicking on any object of a statement will bring up the resource browser for that URI.  Clicking on a predicate will dispatch a SPARQL query:\n<em>SELECT ?S ?O WHERE { ?S ..predicate..  ?O}</em></div>"
            header1="<tr><th align='middle' colspan='3'>Incoming Statements</th></tr>"
            if self.vizualization == '1':
                body = """<h3>%s <a href="/browse?action=graph&amp;uri=%s"><img border="0" src="http://www.w3.org/RDF/icons/rdf_flyer.24"/></a></h3>%s<table style='font-size:8pt;font-style:italics' border='1'><tr><th>Subject</th><th>Predicate</th><th>Object</th></tr>%s%s</table>"""%(res,
                                                                                                                                                                                                                                                                                            urllib.quote(res),
                                                                                                                                                                                                                                                                                            instr,
                                                                                                                                                                                                                                                                                            header1,
                                                                                                                                                                                                                                                                                            '\n'.join(rows))
            else:
                body = """<h3>%s </h3>%s<table style='font-size:8pt;font-style:italics' border='1'><tr><th>Subject</th><th>Predicate</th><th>Object</th></tr>%s%s</table>"""%(res,
                                                                                                                                                                              instr,
                                                                                                                                                                              header1,
                                                                                                                                                                              '\n'.join(rows))
            targetGraph.close()
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',
                                 len(BROWSER_HTML%(body,self.endpoint)))]
            start_response(status, response_headers)
            return [BROWSER_HTML%(body,self.endpoint)]
        elif action == 'graph':
            mapRt=makeGraph(targetGraph,d['uri'],self,imageMap=True)
            
            matches = re.compile(r'rectangle\s+\([\d]+,[\d]+\)\s+\([\d]+,[\d]+\)\s+[^\s]+.*').findall(mapRt)
            
            try:
                from hashlib import md5
            except ImportError:
                from md5 import md5
            def mkHash(i):
                d = md5(i)
                return d.hexdigest()
                        
            mapHTML = '<MAP name="%s">\n'%(mkHash(d['uri']))
            
            for match in matches:
                splitString = match.split(' ')
                corner1x, corner1y = splitString[1][1:-1].split(',')
                corner2x, corner2y = splitString[2][1:-1].split(',')
                resourceUri=splitString[3]
                mapHTML=mapHTML+'<AREA href="%s" shape="rect" coords="%s,%s,%s,%s"/>\n'%(
                                                 resourceUri, 
                                                 corner1x, 
                                                 corner2y, 
                                                 corner2x, 
                                                 corner1y)
            mapHTML+='</MAP>'         
            mapHTML+='\n<img src="/browse?action=graphImg&uri=%s" usemap="%s" alt="diagram of RDF" border="0"/>'%\
                    (d['uri'],
                     mkHash(d['uri']))
            rt=VISUALIZATION_HTML%(mapHTML,"[<a href='/browse?action=resource&uri=%s'>Return</a>]"%
                    urllib.quote(d['uri']))
            targetGraph.close()
            response_headers = [('Content-type',' text/html'),('Content-Length',len(rt))]
            start_response(status, response_headers)
            return [rt]
        elif action == 'graphImg':
            rt=makeGraph(targetGraph,d['uri'],self)
            targetGraph.close()
            response_headers = [('Content-type',' image/png'),('Content-Length',len(rt))]
            start_response(status, response_headers)
            return [rt]        
        else:
            targetGraph.close()
            raise Exception("Unknown action: "+action)

def addType(o,targetGraph):
    oType = None
    for fullType in targetGraph.objects(subject=o, predicate=RDF.type):
        if oType==None:
            oType = fullType.split('#')[-1]
            o = o.n3() + " (" + unescapeHTML(oType) + ")"
            print o
    return o

def unescapeHTML(string):
    newString = string.replace('%20',' ')
    newString = newString.replace('-',' | ')
    return newString

def termShape(term):
    if isinstance(term,(URIRef,BNode)):
        return 'ellipse'
    elif isinstance(term,Literal):
        return 'box'
    else:
        raise

def normalizeLabel(graph,res,nsBindings):
    if res == RDF.type:
        return 'is a'
    else:
        return '"'+str(getURIPrettyString(res,nsBindings,True))+'"'

def makeLabel(term,graph,bindings):
    if isinstance(term,URIRef):
        return normalizeLabel(graph,term,bindings)
    elif isinstance(term,Literal):
        return str(term)
    else:
        kind=first(graph.objects(subject=term,predicate=RDF.type))
        if kind:
            return '"some %s"'%str(getURIPrettyString(kind,bindings,dontEscape=True))
        else: return '"some thing"'

def makeGraph(graph,res,server,imageMap=False):
    """
    Generates (and returns) a PNG diagram of the given resource
    within the given graph, using the specified layout
    This requires the installation of pydot (http://code.google.com/p/pydot/)
    """
    from pydot import Node,Edge,Dot
    dot=Dot(graph_type='digraph',
            #center='true',
            orientation='land',
            #resolution='0.96',
            rankdir='LR',
            #ratio='fill',
            rotate='180')
        
    incrementDict={}
    def incrementalIndex(_dict,item):
        if item in _dict:
            return _dict[item]
        else:
            newIdx = len(_dict)+1
            _dict[item]=newIdx
            return newIdx
    
    resTerm=res.find('_:') == -1 and URIRef(res) or BNode(res.split('_:')[-1])
    
    if isinstance(resTerm,BNode):
        uri = urllib.quote(resTerm.n3())
    else:
        uri = urllib.quote(resTerm)
    
    vertex=Node(incrementalIndex(incrementDict,res),
                label=makeLabel(resTerm,graph,server.nsBindings),
                URL='/browse?action=graph&uri=%s'%uri,
                shape='ellipse')
    dot.add_node(vertex) 
    objs = set()

    for s,p,o in graph.triples((resTerm,None,None)):
        if o not in objs:# and p != RDF.type:
            
            if isinstance(o,BNode):
                oUri = urllib.quote(o.n3())
            else:
                oUri = urllib.quote(o)
            
            oVertex=Node(incrementalIndex(incrementDict,o),
                         label=makeLabel(o,graph,server.nsBindings),
                         URL='/browse?action=graph&uri=%s'%oUri,
                         shape=termShape(o))
            dot.add_node(oVertex) 
            arcLabel=normalizeLabel(graph,p,server.nsBindings)
            edge = Edge(vertex,oVertex,label=arcLabel)            
            edge.label = arcLabel
            dot.add_edge(edge)
            objs.add(o)
    for s,p,o in graph.triples((None,None,resTerm)):
        if s not in objs:# and p != RDF.type:
            
            if isinstance(s,BNode):
                sUri = urllib.quote(s.n3())
            else:
                sUri = urllib.quote(s)
            
            inVertex=Node(incrementalIndex(incrementDict,s),
                          label=makeLabel(s,graph,server.nsBindings),
                          URL='/browse?action=graph&uri=%s'%sUri,
                          shape=termShape(s))
            dot.add_node(inVertex) 
            arcLabel=normalizeLabel(graph,p,server.nsBindings)
            edge = Edge(inVertex,vertex,label=arcLabel)
            edge.label = arcLabel 
            dot.add_edge(edge)
            objs.add(s)

    if imageMap:
        dot.write('out.map',format='ismap')
        f=open('out.map')
        rt=f.read()
        f.close()
        return rt
    else:
        dot.write('out.png',prog=server.layout,format='png')
        f=open('out.png')
        rt=f.read()
        f.close()
        return rt

class Usher(object):
    """
    Traffic cop.  Redirects all traffic to 'endpoint'
    """
    def __init__(self, global_conf):
        self.endpoint      = global_conf['endpoint']
        
    def __call__(self, environ, start_response):
        status = '200 OK'
        response_headers = [('Content-type','text/html'),
                            ('Content-Length',
                             len(WRONG_URL_HTML%(self.endpoint,self.endpoint)))]
        start_response(status, response_headers)
        return [WRONG_URL_HTML%(self.endpoint,self.endpoint)]  

PROCESS_KILLED_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>Running MySQL Processes</title>
  </head>
  <body>
    <div>
        Attempted to kill query %s: %s
    </div>
  </body>
</body>
"""

PROCESS_BROWSER_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>Running MySQL Processes</title>
  </head>
  <body>
    <h1>Running processes on the connected MySQL database:</h1>
    <table>
        <tr>
          <th>Query ID (and ticket if applicable)</th>
          <th>Execution time</th>
          <th>Query</th>
        </tr>
        %s
    </table>
  </body>
</body>"""

def killThread(cursor,thread_id):
    cursor.execute("KILL QUERY %s"%(thread_id))
      
class ProcessBrowser(StoreConnectee):
    def __call__(self, environ, start_response):
        d = parse_formvars(environ)
        queryToKill = d.get('kill')
        ticketToKill = d.get('ticket')
        targetGraph = self.buildGraph(None)        
        cursor = targetGraph.store._db.cursor()

        #Global ticket -> thread_id lookup / dictionary
        global ticketLookup
        revDict=dict([(v,k) for k,v in ticketLookup.items()])
        
        if queryToKill:
            #the user has given an actual thread_id to use
            #to kill the connection
            killThread(cursor,queryToKill)
            rt=PROCESS_KILLED_HTML%(queryToKill,cursor.fetchall())
            response_headers = [('Location','/processes'),
                        ('Content-type','text/html'),
                        ('Content-Length',len(rt))]                        
            status = '303 See Other'            
        elif ticketToKill:
            #A ticket was given, lookup the connection ID to use in killing the 
            #query and remove the entry with correponding thread id as the value
            assert environ.get('REQUEST_METHOD', 'GET') != 'GET',\
                                "will cause side effects!"
            thread_id=ticketLookup[ticketToKill]
            killThread(cursor,thread_id)
            #remove from ticket -> thread_id dictionary/lookup
            del ticketLookup[ticketToKill]            
            rt=PROCESS_KILLED_HTML%(thread_id,cursor.fetchall())
            response_headers = [('Location','/SemanticDB/SPARQL'),
                        ('Content-type','text/html'),
                        ('Content-Length',len(rt))]            
            status = '303 See Other'            
        else:
            #A connection ID was given, kill the connection and
            #remove the entry with correponding thread id as the value
            cursor.execute("SHOW PROCESSLIST")
            processesHTML = []
            dbName = ParseConfigurationString(self.connection)['db']
            for qid,user,host,db,qType,executionTime,other,query in cursor.fetchall():
                qidLabel = qid in revDict and "%s (%s)"%(qid,revDict[qid]) or qid 
                if db == dbName and query not in [None,'SHOW PROCESSLIST']:
                    processesHTML.append('<tr><td><a href="/processes?kill=%s">%s</a></td><td>%s</td><td>%s</td></tr>'%(qid,qidLabel,executionTime,query))
            rt = PROCESS_BROWSER_HTML%(''.join(processesHTML))
            status = '200 OK'
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',
                                 len(rt))]
        start_response(status, response_headers)
        return [rt]        
    
JOWL_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>JOWL Browser</title>
    <link rel="stylesheet" href="css/jOWL.css" type="text/css"/>
    <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.2.6/jquery.min.js"></script>
    <script type="text/javascript" src="/scripts/jOWL.js"></script>
    <script type="text/javascript" src="/scripts/jOWL_UI.js"></script>  
    
      <script type="text/javascript">
    //<![CDATA[
    //this is the script that handles the visuals of this demo
$(document).ready(function() {
    jOWL.load('/owl/CPR.owl', function(){
        //once loaded, remove the loading display
        $('.loader').hide(); $('#demo').show();        
        //initialize UI components
        var tree = $('#treeview').owl_treeview({rootThing: true});
        var individuals = $('#individuals').owl_propertyLens({ 
            onChange : {    "owl:Thing": function(source, target, resourcebox){
                tooltip.display(target, this);
                }
            }
            }); 
        var navbar = $('#navbar').owl_navbar();        
        var autocomplete = $('#owlauto').owl_autocomplete({focus : true, chars : 2, filter : 'Class'});
        //making sure components respond to each others input:
        navbar.addListener([individuals, tree]);
        autocomplete.addListener([navbar, individuals, tree]);
        tree.addListener([individuals, navbar]);
        //set focus on the text input for user.
        $('#owlauto').focus(); 
        //fire up the components, on the owl Class wine
        var wine = jOWL("wine");
        navbar.propertyChange(wine);
        navbar.broadcast(wine);    

    }, {reason : true });    
    
});
    //]]>
    </script>
  </head>
  <body>
    <div id="demo" style="display:none;"/>
    <div id="treeview" style="margin-top:5px;">
        <h4>Treeview</h4>
    </div>        
  </body>
</body>"""
        
class JOWLBrowser(StoreConnectee):
    """
    jOWL Browser
    """
    def __call__(self, environ, start_response):
        raise NotImplementedError("JOWL Browsing not implemented")

class About(StoreConnectee):
    """
    Gives summary statistics on the underlying RDF store
    """
    def __call__(self, environ, start_response):
        status = '200 OK'
        g = self.buildGraph()
        rt = repr(g.store).replace('<','&lt;')
        g.close()
        response_headers = [('Content-type','text/html'),('Content-Length',len(rt))]
        start_response(status, response_headers)
        return ["""<html><body><h2>RDF triple store statistics: </h2><div>%s</div><div>[<a href="%s">Return</a>]</div></body></html>"""%(rt,
                                                                                                                                         self.endpoint)]

class Generator2:
    def __init__(self, generator, callback, environ):
        self.__generator = generator
        self.__callback = callback
        self.__environ = environ
    def __iter__(self):
        for item in self.__generator:
            yield item
    def close(self):
        print "Closing WSGI handling generator..."
        if hasattr(self.__generator, 'close'):
            self.__generator.close()
        self.__callback.cleanup()

class WsgiApplication(StoreConnectee):
    def __init__(self, 
                 global_conf,
                 nsBindings,
                 defaultDerivedPreds,
                 litProps,
                 resProps,
                 definingOntology,
                 ontGraph,
                 ruleSet,
                 builtinTemplateGraph):
        super(WsgiApplication, self).__init__(global_conf,         
                                              nsBindings,
                                              defaultDerivedPreds,
                                              litProps,
                                              resProps,
                                              definingOntology,
                                              ontGraph,
                                              ruleSet,
                                              builtinTemplateGraph)
        self.targetGraph = None
        
    def cleanup(self):
        print "Cleaning up .."
        print self.targetGraph
        if self.targetGraph is not None:
            self.targetGraph.close()
    
    def __call__(self, environ, start_response):
        try:
            result = self.execute(environ, start_response)
        except:
            self.cleanup()
            raise
        return Generator2(result, self, environ)        

    def execute(self, environ, start_response):
        """
        SPARQL Service application
        Works for POST & GET requests, taking query and default_graph_uri as parameters for the query 
        """
        d = parse_formvars(environ)
        query             = d.get('query')
        ticket            = d.get('ticket')
        default_graph_uri = d.get('default-graph-uri')
        rtFormat          = d.get('resultFormat')
        print "## Query ##\n", query, "\n###########"
        print "Default graph uri ", default_graph_uri
        reqMeth = environ.get('REQUEST_METHOD', 'GET')
        if reqMeth == 'POST':
            assert query,"POST can only take an encoded query"
        else:
            assert reqMeth == 'GET',"Either POST or GET method!"
            if not query:
                #A GET with no parameters returns an HTML form for submitting queries
                status = '200 OK'
                bindingsHTML=''.join(['<tr><td>%s</td><td>%s</td></tr>'%(prefix,uri)
                           for prefix,uri in self.nsBindings.items()])
                retVal=SPARQL_FORM.replace('ENDPOINT',self.endpoint).replace('BINDINGS',bindingsHTML)
                entailmentRepl=''
                if self.topDownEntailment:
                    entailmentRepl = '<div><em>This server has an <strong><a href="/entailment">active</a></strong> entailment regime!</em></div><br/>'
                retVal=retVal.replace('ENTAILMENT',entailmentRepl)                
                retVal=retVal.replace('<!--CancelButton-->',
                               '<input type="button" value="\'Prepare\' Query" onClick="getTicket(\'queryform\')"></input>')
                response_headers = [('Content-type','text/html'),
                                    ('Content-Length',
                                     len(retVal))]
                start_response(status, response_headers)
                yield retVal
                return
        if self.ignoreQueryDataset:
            self.targetGraph = self.buildGraph(default_graph_uri)
        else:
            self.targetGraph = self.buildGraph(default_graph_uri=None)

        for pref,nsUri in self.nsBindings.items():
            self.targetGraph.bind(pref,nsUri)

        if not self.proxy and self.topDownEntailment:
            from rdflib.sparql.Algebra import *
            from rdflib.sparql.graphPattern import BasicGraphPattern
            from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
            topDownStore=rdflib-stable.rdflib.store.BackwardChainingStore.TopDownSPARQLEntailingStore(
                                        self.targetGraph.store,
                                        self.targetGraph,
                                        set(self.defaultDerivedPreds),
                                        self.ruleSet,
                                        self.debugQuery,
                                        self.nsBindings)
            _query = topDownStore.isaBaseQuery(query)
            if isinstance(_query,(BasicGraphPattern,
                                  AlgebraExpression)):
                print ".. Query involving IDB predicate with entailment regime.."
                #A query involving derived predicates with an active entailment regime
                if default_graph_uri:
                    self.targetGraph = Graph(topDownStore,identifier = URIRef(default_graph_uri))
                else:
                    self.targetGraph = ConjunctiveGraph(topDownStore)

                topDownStore.targetGraph = self.targetGraph
                self.targetGraph.templateMap = \
                    dict([(pred,template)
                              for pred,_ignore,template in
                                    self.builtinTemplateGraph.triples(
                                        (None,
                                         TEMPLATES.filterTemplate,
                                         None))])
                topDownStore.edb.templateMap = self.targetGraph.templateMap
                for pref,nsUri in self.nsBindings.items():
                    self.targetGraph.bind(pref,nsUri)
        origQuery = query
        query=parse(query)
        start = time.time()
        
        if self.ignoreBase and hasattr(query,'prolog') and query.prolog:
            query.prolog.baseDeclaration=None
        if self.ignoreQueryDataset and hasattr(query.query,'dataSets') and query.query.dataSets:
            print "Ignoring query-specified datasets: ", query.query.dataSets
            query.query.dataSets = []
            
        if not self.proxy and ticket:
            #Add entry for current thread in ticket -> thread id lookup
            global ticketLookup
            ticketLookup[ticket]=self.targetGraph.store._db.thread_id()            
            
        #Run the actual query
        rt = self.targetGraph.query(origQuery,
                                    initNs=self.nsBindings,
                                    DEBUG=self.debugQuery,
                                    parsedQuery=query)
        print "Time to execute SPARQL query: ", time.time() - start
        qRT = rt.serialize(format='xml')
        self.targetGraph.close()
        print "Time to execute and seralize SPARQL query: ", time.time() - start
        print "# of bindings: ", rt.noAnswers
        
        if rtFormat in ['xml','csv'] or not rtFormat:
            
            rtDoc = NonvalidatingReader.parseString(qRT,
                                                    'tag:nobody@nowhere:2007:meaninglessURI')
            stylesheetPath = rtFormat == 'xml' and '/xslt/xml-to-html.xslt' or '/xslt/xml-to-csv.xslt'
            imt='application/xml'
            
            pi = rtDoc.createProcessingInstruction("xml-stylesheet",
                                                   "type='text/xml' href='%s'"%stylesheetPath)
            #Add a stylesheet instruction to direct browsers how to render the result document
            rtDoc.insertBefore(pi, rtDoc.documentElement)
            out = StringIO()
            PrettyPrint(rtDoc, stream=out)
            rt = out.getvalue()
        elif rtFormat == 'csv-pure':
            imt='text/plain'
            rt=self.csvProcessor.run(InputSource.DefaultFactory.fromString(qRT))

        status = '200 OK'
        response_headers = [('Content-type',imt),
                            ('Content-Length',len(rt))]
        start_response(status, response_headers)
        yield rt
