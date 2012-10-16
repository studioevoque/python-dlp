#!/usr/bin/env python
"""
A (Paste-based) WSGI implementation of the SPARQL Protocol ala RDF Kendall Grant Clark, W3C, et. al. 2006

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.    
"""
import os, getopt, sys, re, time, urllib, codecs,itertools, rdflib, pyparsing
from glob import glob
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
from rdflib.sparql.Algebra import *
from rdflib.sparql.graphPattern import BasicGraphPattern
from QueryManager import QUERY_EDIT_HTML

try:
    from amara        import bindery, tree
    from amara.lib    import U
except:
    pass
try:
    from hashlib import md5 as createDigest
except:
    from md5 import new as createDigest
    
    
    
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

CODEMIRROR_SETUP=\
"""
<script
    src="codemirror/js/codemirror.js"
    type="text/javascript">
</script>
<style type="text/css">
  .CodeMirror {border-top: 1px solid black; border-bottom: 1px solid black;}
  .activeline {background: #f0fcff !important;}
</style>
<link rel="stylesheet" type="text/css" href="codemirror/css/docs.css"/>
"""

SPARQL_FORM=\
"""
<?xml version="1.0" encoding="utf-8"?>
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">
  <head>
    <title>SPARQL Kiosk</title>
    CODEMIRROR
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
      <h2>Triclops: <a href="http://www.w3.org/TR/rdf-sparql-query">SPARQL</a> Kiosk</h2>
      <p>The list of (long-)running queries can be <a href="%s/processes" target="_blank">managed</a>.</p>
      ENTAILMENT
      <form id="queryform" action="ENDPOINT" method="post">
        <!--hidden ticket-->
        <div>
        </div>
        <!-- Default Grap IRI: <input type="text" size="80" name="default-graph-uri" id="default-graph-uri" value=""/ -->
        <div>
        
        <textarea id="query" name="query" cols="120" rows="30">
#Example query (all classes in dataset)
SELECT DISTINCT ?Concept where {
    [] a ?Concept
}
        </textarea>
        </div>
        <script type="text/javascript">
          var editor = CodeMirror.fromTextArea('query', {
            autoMatchParens: true,
            height: "150px",
            parserfile: "parsesparql.js",
            stylesheet: "codemirror/css/sparqlcolors.css",
            path: "js/"
          });
        </script>
        <select name="resultFormat">
          <option value="xml" selected="on">SPARQL XML (rendered as XHTML)</OPTION>
          <option value="csv">SPARQL XML (rendered as tab delimited)</OPTION>
          <option value="csv-pure">Tab delimited</OPTION>
        </select>                
        <div><input type="button" value="Submit SPARQL" onClick="submitQuery('queryform')" />
           <!--CancelButton-->
        </div>
        </div>        
      </form>
    </div>
    <h3>SPARQL Queries to Manage</h3>
    <table width='100%%' style='font:10pt arial,sans-serif;'>
        <tr>
          <th width=50%%' align='left'>Query name</th>
          <th align='left'>Query last modification date</th>
          <th align='left'>Date last run</th>
          <th align='left'>Number of results</th>
        </tr>
        QUERIES
    </table>
    <hr />          
    <table style='font:8pt arial,sans-serif;'>
      <thead>
          <tr><td colspan='2'>Preset namespace bindings</td></tr>
      </thead>
      <tbody>BINDINGS</tbody>
    </table>    
    <div style="font-size: 10pt; margin: 0 1.8em 1em 0; text-align: center;">Powered by <a href="http://codemirror.net/">CodeMirror</a:q>, <a href="http://code.google.com/p/python-dlp/wiki/LayerCakePythonDivergence">layercake-python</a> (<em><strong>RDF</strong></em>), <a href="http://pythonpaste.org/">Python Paste</a> (<em><strong>HTTP</strong></em>), and <a href="http://4suite.org">4Suite</a> (<em><strong>XML</strong></em>)</div>
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
            '<a href="%s?action=resource&amp;uri=%s">%s</a>'%(os.path.join(server.endpoint,'browse'),
                                                              urllib.quote(term),
                                                              getURIPrettyString(addType(term,targetGraph),server.nsBindings))
    elif isinstance(term,BNode):
        return noLink and '%s'%term.n3() or \
        '<a href="%s?action=resource&amp;uri=%s">%s</a>'%(os.path.join(server.endpoint,'browse'),
                                                          urllib.quote(term.n3()),
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
        self.manageQueries      = global_conf.get('manageQueries')
        self.queryManager       = global_conf.get('queryMgr')
        self.endpointURL        = global_conf.get('endpointURL')

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
            retVal=SPARQL_FORM.replace('ENDPOINT',self.endpoint).replace('CODEMIRROR',CODEMIRROR_SETUP)
            retVal=retVal%(self.endpoint)
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
                return """<li><span style="font-size:8pt;font-style:italics"><a href="%d?action=extension&amp;uri=%s">%s</a></span></li>"""%(
                    os.path.join(self.endpoint,'browse'),
                    uri,
                    c)
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
                return """<li><span style="font-size:8pt;font-style:italics"><a href="%s?action=resource&amp;uri=%s">%s</a></span></li>"""%(
                    os.path.join(server.endpoint,'browse'),
                    uri,
                    m)
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
                body = """<h3>%s <a href="%s?action=graph&amp;uri=%s"><img border="0" src="http://www.w3.org/RDF/icons/rdf_flyer.24"/></a></h3>%s<table style='font-size:8pt;font-style:italics' border='1'><tr><th>Subject</th><th>Predicate</th><th>Object</th></tr>%s%s</table>"""%(
                    res,
                    os.path.join(server.endpoint,'browse'),
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
            mapHTML+='\n<img src="%saction=graphImg&uri=%s" usemap="%s" alt="diagram of RDF" border="0"/>'%\
                    (self,d['uri'],
                     mkHash(d['uri']))
            rt=VISUALIZATION_HTML%(mapHTML,"[<a href='%s?action=resource&uri=%s'>Return</a>]"%
                    os.path.join(self.endpoint,'browse'),
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
                URL='%s?action=graph&uri=%s'%(os.path.join(server.endpoint,'browse'),uri),
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
                         URL='%s?action=graph&uri=%s'%(os.path.join(server.endpoint,'browse'),oUri),
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
                          URL='%s?action=graph&uri=%s'%(os.path.join(server.endpoint,'browse'),sUri),
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

QUERY_LIST_ENTRY=\
"""
<tr>
    <td>
        <a href="%s?query=%s&action=edit">%s</a>
    </td>
    <td>%s</td>
    <td>%s</td>
    <td>
        %s
    </td>
</tr>"""

TEMPLATING_AND_RESULT_NAV=\
"""
<div>%s</div>
<hr/>
<fieldset>
    <legend>Result navigation template</legend>
    <div>%s</div>
    <div>
        <table border="0">
            <thead>
                <tr>
                    <th>Original IRI text to replace</th>
                    <th>Replacement text</th>
                </tr>
                <tr>
                    <td><input type='text' name='IdentifierReplaceOrig' size='60'/></td>
                    <td><input type='text' name='IdentifierReplaceNew' size='60'/></td>
                </tr>
            </thead>
        </table>
    </div>    
</fieldset>
"""

RESULT_NAV=\
"""
<select name="outVariable">%s</select>
<select name="subsequentQueryId">%s</select>
<input type='text' name='inVar' size='10'/>
"""

TEMPLATE_VALUE=\
"""
<select name="variable">%s</select>
<input type='text' name='templateValue' size='60'/>
<select name="valueType">
    <option value="literal" selected="on">RDF Literal</OPTION>
    <option value="uri">URI References</OPTION>
    <option value="qname">QName / curie</OPTION>
</select>
"""

class QueryManager(StoreConnectee):
    def __call__(self, environ, start_response):
        d = parse_formvars(environ)
        action  = d.get('action','list')
        queryId = d.get('query')
        targetGraph = self.buildGraph(None)

        entries = []
        if action == 'result-navigation':
            from pprint import pprint;pprint(d)
            inVar             = d.get('inVar')
            outVar            = d.get('outVar')
            subsequentQueryId = d.get('subsequentQueryId')
            iriStrOrig        = d.get('iriStrOrig')
            iriStrReplace     = d.get('iriStrReplace')
            fName             = os.path.join(self.manageQueries,'%s.rq.xml'%subsequentQueryId)
            doc               = bindery.parse(open('htdocs/xslt/xml-to-html.xslt').read())
            stylesheetStr = open('htdocs/xslt/xml-to-html-navigable.xslt').read()
            fallBackLink = '%s?query=9f65856719dc209e6e6e8ecf6eebe059&amp;action=update&amp;innerAction=execute&amp;templateValue={.}&amp;valueType=uri&amp;variable=resource'
            navLink = '%s?query=%s&amp;action=update&amp;innerAction=execute&amp;templateValue=%s&amp;valueType=uri&amp;variable=%s'
            replaceNavLink = navLink%(
                                self.queryManager,
                                subsequentQueryId,
                                '{$escapedReplacedUri}',
                                inVar)
            nonReplaceNavLink = navLink%(
                                self.queryManager,
                                subsequentQueryId,
                                '{$escapedUri}',
                                inVar)

            fallBackLink = fallBackLink%self.queryManager
            
            #?REPLACE?, ?REPLACE_URI?, ?NO_REPLACE_URI?, ?GRAPH_NAVIGATE_URI?
            stylesheetStr = stylesheetStr.replace(
                '?REPLACE?',
                'true()' if iriStrOrig else 'false()').replace(
                    '?REPLACE_URI?',
                    replaceNavLink).replace(
                        '?NO_REPLACE_URI?',
                        nonReplaceNavLink).replace('?GRAPH_NAVIGATE_URI',fallBackLink)
            stylesheetStr = stylesheetStr.replace('NAV_VAR',outVar if outVar else '')
            
            doc = bindery.parse(stylesheetStr)
            linkTemplate = first(doc.stylesheet.xml_select(
                '*[@match = "sr:binding/*"]'))
            link = first(linkTemplate.xml_select('//*[local-name() = "a"]'))
            linkVal = U(link.href)
            linkVal = linkVal.replace('.',"$replacedUri)")
            link.xml_value = linkVal
            out = StringIO()
            doc.xml_write('xml-indent',stream=out)
            rt = out.getvalue().replace("'FROM'","'%s'"%iriStrOrig).replace("'TO'","'%s'"%iriStrReplace)

            status = '200 OK'
            response_headers = [('Content-type','application/xslt+xml'),
                                ('Content-Length',
                                 len(rt))]
            start_response(status, response_headers)
            return [rt]                    
            
        elif action == 'add':
            querytext = d.get('sparql')
            queryName = d.get('name')
            print querytext, queryName

            assert querytext is not None and queryName is not None,"Nothing to save"

            querytext.replace('>','&gt;')

            doc = bindery.nodes.entity_base()
            rootEl = doc.xml_element_factory(None, u'Query')
            rootEl.xml_attributes[(None,u'name')] = U(queryName)
            rootEl.xml_append(U(querytext))
            doc.xml_append(rootEl)

            queryFName = '%s.rq.xml'%(createDigest(queryName).hexdigest())
            f = open(os.path.join(self.manageQueries,queryFName),'wb')
            doc.xml_write('xml-indent',stream=f)
            f.close()

            rt='Added query.  Redirecting..'
            response_headers = [('Location',self.queryManager),
                                ('Content-Length',
                                 len(rt))]
            start_response('303 See Other', response_headers)
            return [rt]

        elif action == 'edit':
            fObj = open(os.path.join(self.manageQueries,'%s.rq.xml')%d.get('query'))
            doc = bindery.parse(fObj.read())
            query = U(doc.Query).encode('ascii').replace('<','&lt;')
            queryName = U(doc.Query.name).encode('ascii')

            rt = QUERY_EDIT_HTML.replace('QUERYMGR',self.queryManager)
            rt = rt.replace('ENDPOINT',self.endpoint)
            rt = rt.replace('NAME',queryName)
            rt = rt.replace('QUERYID',createDigest(queryName).hexdigest())
            rt = rt.replace('QUERY',query)
            
            pat           = re.compile("\$\w+\$|\?\w+")
            terms        = pat.findall(query)
            queryVarsPat  = re.compile("\?\w+")
            queryVars     = queryVarsPat.findall(query)            
            
            pickList = '\n'.join(['<option value="%s" %s>%s</OPTION>'%(
                term,
                'selected="on"' if term.find('$')+1 else '',
                term)
                for term in set(terms) ])
            selectValues1 = []
            selectValues2 = []
            for _var in set(queryVars):
                selectValues1.append((_var,)*2)
            for _fname in [_fname for _fname in glob(os.path.join(self.manageQueries,'*.rq.xml'))]:
                try:
                    entry = (_fname.split('/')[-1].split('.')[0],
                             U(bindery.parse(open(_fname).read()).Query.name))
                    selectValues2.append(entry)
                except Exception, e:
                    print repr(e)
                    continue
                    
            # <select name="outVariable">%s</select>
            # <select name="subsequentQueryId">%s</select>
            # <input type='text' name='inVar' size='10'/>
            resultNavStr = RESULT_NAV%(
                '\n'.join(['<option value="%s">%s</OPTION>'%entry
                    for entry in selectValues1 ]),
                '\n'.join(['<option value="%s">%s</OPTION>'%entry
                    for entry in selectValues2 ]))
            
            subStr =  TEMPLATING_AND_RESULT_NAV%(TEMPLATE_VALUE%(pickList if terms else ''),resultNavStr)
            rt = rt%subStr
            
            status = '200 OK'
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',
                                 len(rt))]
            start_response(status, response_headers)
            return [rt]
        elif action == 'update':
            rtFormat          = d.get('resultFormat','xml')
            givenName         = d.get('name')
            queryId           = d.get('query')
            sparql            = d.get('sparql')
            fName = os.path.join(self.manageQueries,'%s.rq.xml')%d.get('query')
            resultFName = os.path.join(self.manageQueries,'%s.rq.results.xml')%d.get('query')

            if d.get('innerAction') == 'load':
                fObj = open(fName)
                doc  = bindery.parse(fObj.read())
                if  os.path.exists(resultFName):
                    f=open(resultFName)
                    if rtFormat in ['xml','csv'] or not rtFormat:

                        rtDoc = NonvalidatingReader.parseString(f.read(),
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
                    f.close()
                    status = '200 OK'
                    response_headers = [('Content-type',imt),
                                        ('Content-Length',
                                         len(rt))]
                    start_response(status, response_headers)
                    return [rt]
                else:
                    rt='Query does not have any existing results'
                    status = '404 Not Found'
                    response_headers = [('Content-type','text/html'),
                                        ('Content-Length',
                                         len(rt))]
                    start_response(status, response_headers)
                    return [rt]

            elif d.get('innerAction') == 'execute':
                inVar     = d.get('inVar')
                outVar    = d.get('outVariable')                
                variable  = d.get('variable')
                value     = d.get('templateValue')
                valueType = d.get('valueType')
                if variable:
                    variable = variable  if variable.find('?')+1 or variable.find('$')+1 else '?%s'%variable
                if self.debugQuery:
                    from pprint import pprint
                    pprint(d)
                    print "Replacing %s with (appropiate version of) %s"%(variable,value)
                if sparql is None and queryId is not None:
                    fName = os.path.join(self.manageQueries,'%s.rq.xml')%queryId
                    fObj = open(fName) if os.path.exists(fName) else open(os.path.join(
                        self.manageQueries,
                        '%s.rq.xml')%(d.get('query')))
                    doc = bindery.parse(fObj.read())
                    fObj.close()
                    sparql = U(doc.xml_select('string(/Query/text())')).encode('ascii')
                    
                if variable and value:
                    if valueType=='uri':
                        sparql = sparql.replace(variable,URIRef(value).n3())
                    elif valueType == 'qname':
                        nsDict = dict([(pref,nsUri) for pref,nsUri in self.nsBindings.items()])
                        prefix,localName = value.split(':')
                        valueUri = URIRef(nsDict[unicode(prefix)]+localName)
                        sparql = sparql.replace(variable,valueUri.n3())
                    else:
                        sparql = sparql.replace(variable,value)
                    print "Replaced sparql: (%s for %s)"%(variable,value)
                    print sparql
                
                resultFName = os.path.join(self.manageQueries,'%s.rq.results.xml')%d.get('query')
                self.targetGraph = self.buildGraph(default_graph_uri=None)
                for pref,nsUri in self.nsBindings.items():
                    self.targetGraph.bind(pref,nsUri)

                origQuery = sparql
                try:
                    query=parse(sparql)
                except Exception, e:
                    print sparql
                    rt = "Malformed SPARQL Query: %s"%repr(e)
                    status = '400 Bad Request'
                    response_headers = [('Content-type','text/html'),
                                        ('Content-Length',
                                         len(rt))]
                    start_response(status, response_headers)
                    return [rt]
                start = time.time()
                if self.ignoreBase and hasattr(query,'prolog') and query.prolog:
                    query.prolog.baseDeclaration=None
                if self.ignoreQueryDataset and hasattr(query.query,'dataSets') and query.query.dataSets:
                    print "Ignoring query-specified datasets: ", query.query.dataSets
                    query.query.dataSets = []

                if self.debugQuery:
                    print sparql
                    
                #Run the actual query
                rt = self.targetGraph.query(origQuery,
                                            initNs=self.nsBindings,
                                            DEBUG=self.debugQuery,
                                            parsedQuery=query)
                print "Time to execute SPARQL query: ", time.time() - start
                qRT = rt.serialize(format='xml')
                f=open(resultFName,'wb')
                f.write(qRT)
                f.close()
                if rtFormat in ['xml','csv']:

                    rtDoc = NonvalidatingReader.parseString(qRT,
                                                            'tag:nobody@nowhere:2007:meaninglessURI')
                    stylesheetPath = rtFormat == 'xml' and '/xslt/xml-to-html.xslt' or '/xslt/xml-to-csv.xslt'
                    
                    if rtFormat == 'xml' and inVar:
                        fName = os.path.join(self.manageQueries,'%s.rq.xml'%d.get('subsequentQueryId'))
                        # print(U(bindery.parse(open(fName).read()).Query))
                        stylesheetPath = '%s?action=result-navigation&amp;inVar=%s&amp;outVar=%s&amp;subsequentQueryId=%s&amp;iriStrOrig=%s&amp;iriStrReplace=%s'%(
                            self.queryManager,
                            inVar[1:] if inVar.find('?')+1 else inVar,
                            outVar[1:] if outVar is not None and outVar.find('?')+1 else '' if outVar is None else outVar,
                            d.get('subsequentQueryId'),
                            urllib.quote(d.get('IdentifierReplaceOrig')),
                            urllib.quote(d.get('IdentifierReplaceNew'))
                            )
                    
                    imt='application/xml'
                    print "Embedded stylesheet reference: ", stylesheetPath
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
                self.targetGraph.close()
                status = '200 OK'
                response_headers = [('Content-type',imt),
                                    ('Content-Length',
                                     len(rt))]
                start_response(status, response_headers)
                return [rt]
            elif d.get('innerAction') == 'clone':
                fObj = open(fName)
                doc = bindery.parse(fObj.read())
                fObj.close()
                query = d.get('sparql').replace('<','&lt;')
                givenName = d.get('name')
                queryName = U(doc.Query.name).encode('ascii')
                assert queryName != givenName
                newQueryId = createDigest(givenName).hexdigest()
                fName = os.path.join(self.manageQueries,'%s.rq.xml'%newQueryId)
                f=open(fName,'w')
                doc = bindery.nodes.entity_base()
                doc.xml_append(doc.xml_element_factory(None, u'Query'))
                doc.Query.xml_attributes[(None, u'name')] = U(givenName)
                doc.Query.xml_append(U(query))
                doc.xml_write('xml-indent',stream=f)
                f.close()

                rt = QUERY_EDIT_HTML.replace('QUERYMGR',self.queryManager)
                rt = rt.replace('NAME',givenName)
                rt = rt.replace('QUERYID',newQueryId)
                rt = rt.replace('QUERY',query)

                status = '200 OK'
                response_headers = [('Content-type','text/html'),
                                    ('Content-Length',
                                     len(rt))]
                start_response(status, response_headers)
                return [rt]
            else:
                givenNameHash = createDigest(givenName).hexdigest()
                fName = os.path.join(self.manageQueries,'%s.rq.xml')%givenNameHash
                fObj = open(fName) if os.path.exists(fName) else open(os.path.join(
                    self.manageQueries,
                    '%s.rq.xml')%(d.get('query')))
                doc = bindery.parse(fObj.read())
                fObj.close()
                query = d.get('sparql').replace('<','&lt;')
                queryName = U(doc.Query.name).encode('ascii')
                

                if queryName != givenName and givenName is not None:
                    doc.Query.xml_attributes[(None, u'name')] = U(givenName)
                    newFName = os.path.join(self.manageQueries,'%s.rq.xml'
                        )%givenNameHash
                    fName = os.path.join(self.manageQueries,'%s.rq.xml')%(d.get('query'))
                    os.rename(fName,newFName)
                    print "Renamed file: %s -> %s"%(fName,newFName)
                    f = open(newFName,'w')
                else:
                    print "Overwriting file: %s"%(fName)
                    f = open(fName,'w')

                doc = bindery.nodes.entity_base()
                doc.xml_append(doc.xml_element_factory(None, u'Query'))
                doc.Query.xml_attributes[(None, u'name')] = U(givenName)
                doc.Query.xml_append(U(query))
                doc.xml_write('xml-indent',stream=f)
                f.close()

                rt = "Redirecting to updated query"

                response_headers = [('Location','%s?action=edit&query=%s'%(self.queryManager,
                                                               givenNameHash)),
                            ('Content-type','text/html'),
                            ('Content-Length',len(rt))]                        
                status = '303 See Other'            
                start_response(status, response_headers)
                return [rt]
            
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

SD_FORMATS = ['application/rdf+xml','text/turtle','text/n3','text/plain']

MIME_SERIALIZATIONS = {
    'application/rdf+xml' : 'pretty-xml',
    'text/turtle'         : 'turtle',
    'text/n3'             : 'n3',
    'text/plain'          : 'ntriples'
}

class FormManager(StoreConnectee):
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
        super(FormManager, self).__init__(global_conf,
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
        #A GET with no parameters returns an HTML form for submitting queries

        d = parse_formvars(environ)
        order             = d.get('order')

        reqMeth = environ.get('REQUEST_METHOD', 'GET')
        if reqMeth != 'GET':
            rt = 'SPARQL query form must be retrieved via GET!'
            status = '405 Method Not Allowed'
            response_headers = [
                ('Content-type'  , 'text/plain'),
                ('Content-Length', len(rt))
            ]
            start_response(status, response_headers)
            yield rt
            return

        status = '200 OK'
        bindingsHTML=''.join(['<tr><td>%s</td><td>%s</td></tr>'%(prefix,uri)
                              for prefix,uri in self.nsBindings.items()])
        retVal=SPARQL_FORM.replace('ENDPOINT',self.endpoint).replace(
            'BINDINGS',
            bindingsHTML)

        retVal=retVal.replace('CODEMIRROR',CODEMIRROR_SETUP)
        retVal=retVal%(self.endpoint)
        entailmentRepl=''

        if self.manageQueries:
            entries = []
            def sortByName(item):
                fName = os.path.join(self.manageQueries,item)
                fObj = open(fName)
                doc = bindery.parse(fObj.read())
                return U(doc.Query.name)
            def sortByNo(item):
                fName = os.path.join(self.manageQueries,item)
                fObj = open(fName)
                doc = bindery.parse(fObj.read())
                return int(doc.xml_select(
                    'count(/*[local-name()="sparql"]/*[local-name()="results"]/*)'))\
                if hasattr(doc,'sparql') else 0

            def sortByDate(item):
                fName = os.path.join(self.manageQueries,item)
                return os.lstat(fName).st_mtime

            for fN in sorted([_fname
                              for _fname in os.listdir(self.manageQueries)
                              if _fname.find('results')==-1],
                key=sortByDate if order=='date'
                else sortByNo if order=='size'
                else sortByName ):
                fName = os.path.join(self.manageQueries,fN)
                fObj = open(fName)
                doc = bindery.parse(fObj.read())
                _id=createDigest(U(doc.Query.name)).hexdigest()
                resultFName = os.path.join(self.manageQueries,
                    '%s.rq.results.xml'
                )%_id
                entries.append(
                    QUERY_LIST_ENTRY%
                    (os.path.join(self.queryManager),
                     createDigest(U(doc.Query.name)).hexdigest(),
                     U(doc.Query.name).encode('ascii'),
                     time.ctime(os.lstat(fName).st_mtime),
                     time.ctime(os.lstat(resultFName).st_mtime)
                     if os.path.exists(resultFName) else 'N/A',
                     '<a href="%s?action=update&query=%s&innerAction=load">%s</a>'%(
                         self.queryManager,
                         _id,
                         int(bindery.parse(resultFName).xml_select(
                             'count(/*[local-name()="sparql"]/*[local-name()="results"]/*)'))
                         ) if os.path.exists(resultFName) else 'N/A')
                )
            retVal=retVal.replace('QUERIES','\n'.join(entries))

        if self.topDownEntailment:
            entailmentRepl = '<div><em>This server has an <strong><a href="%s/entailment">active</a></strong> entailment regime!</em></div><br/>'%(
                self.endpoint)
        retVal=retVal.replace('ENTAILMENT',entailmentRepl)

        retVal=retVal.replace('<!--CancelButton-->',
            '<input type="button" value="\'Prepare\' Query" onClick="getTicket(\'queryform\')"></input>')
        response_headers = [('Content-type','text/html'),
            ('Content-Length',
             len(retVal))]
        start_response(status, response_headers)
        yield retVal
        return

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
        action  = d.get('action','list')
        queryId = d.get('query')        
        order             = d.get('order')
        query             = d.get('query')
        ticket            = d.get('ticket')
        default_graph_uri = d.get('default-graph-uri')
        rtFormat          = d.get('resultFormat')
        print "## Query ##\n", query, "\n###########"
        print "Default graph uri ", default_graph_uri
        reqMeth = environ.get('REQUEST_METHOD', 'GET')

        requestedFormat = environ.get('HTTP_ACCEPT','application/rdf+xml')

        if reqMeth == 'POST':
            assert query,"POST can only take an encoded query"
        elif reqMeth == 'GET' and not query:
            if requestedFormat not in SD_FORMATS:
                requestedFormat = 'application/rdf+xml'
            if self.ignoreQueryDataset:
                targetGraph = self.buildGraph(default_graph_uri)
            else:
                targetGraph = self.buildGraph(default_graph_uri=None)

            sdGraph = Graph()

            SD_NS  = Namespace('http://www.w3.org/ns/sparql-service-description#')
            SCOVO  = Namespace('http://purl.org/NET/scovo#')
            VOID   = Namespace('http://rdfs.org/ns/void#')
            FORMAT = Namespace('http://www.w3.org/ns/formats/')

            sdGraph.bind(u'sd',SD_NS)
            sdGraph.bind(u'scovo',SCOVO)
            sdGraph.bind(u'void',VOID)
            sdGraph.bind(u'format',FORMAT)

            service     = BNode()
            datasetNode = BNode()
            if self.endpointURL:
                sdGraph.add((service,SD_NS.endpoint,URIRef(self.endpointURL)))
            sdGraph.add((service,SD_NS.supportedLanguage        ,SD_NS.SPARQL10Query))
            sdGraph.add((service,RDF.type                       ,SD_NS.Service))
            sdGraph.add((service,SD_NS.defaultDatasetDescription,datasetNode))
            sdGraph.add((service,SD_NS.resultFormat,FORMAT['SPARQL_Results_XML']))
            sdGraph.add((datasetNode,RDF.type,SD_NS.Dataset))

            for graph in targetGraph.store.contexts():
                graphNode  = BNode()
                graphNode2 = BNode()
                sdGraph.add((datasetNode,SD_NS.namedGraph,graphNode))
                sdGraph.add((graphNode,SD_NS.name,URIRef(graph.identifier)))
                sdGraph.add((graphNode,SD_NS.graph,graphNode2))
                sdGraph.add((graphNode,RDF.type,SD_NS.NamedGraph))
                sdGraph.add((graphNode2,RDF.type,SD_NS.Graph))
                noTriples = Literal(len(graph))
                sdGraph.add((graphNode2,VOID.triples,noTriples))
            doc = sdGraph.serialize(
                format=MIME_SERIALIZATIONS[requestedFormat])
            status = '200 OK'
            response_headers = [
                                ('Content-type'  , requestedFormat),
                                ('Content-Length', len(doc))
                               ]
            start_response(status, response_headers)
            yield doc
            return
        else:
            assert reqMeth == 'GET',"Either POST or GET method!"
        if self.ignoreQueryDataset:
            self.targetGraph = self.buildGraph(default_graph_uri)
        else:
            self.targetGraph = self.buildGraph(default_graph_uri=None)

        for pref,nsUri in self.nsBindings.items():
            self.targetGraph.bind(pref,nsUri)

        if not self.proxy and self.topDownEntailment:
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
        try:
            query=parse(query)
        except pyparsing.ParseException, e:
            rt = "Malformed SPARQL Query: %s"%repr(e)
            status = '400 Bad Request'
            response_headers = [('Content-type','text/html'),
                                ('Content-Length',
                                 len(rt))]
            start_response(status, response_headers)
            yield rt
        
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
