#!/usr/bin/env python
"""
A (Paste-based) WSGI implementation of the SPARQL Protocol ala RDF Kendall Grant Clark, W3C, et. al. 2006

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.    
"""
import os, getopt, sys, re, time, urllib
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib import URIRef, store, plugin, RDF, BNode, Literal
from rdflib.Namespace import Namespace
from rdflib.store import Store
from rdflib.sparql.QueryResult import SPARQL_XML_NAMESPACE
from Ft.Xml.Domlette import NonvalidatingReader
from Ft.Xml.Domlette import Print, PrettyPrint
from cStringIO import StringIO
from rdflib.store.MySQL import ParseConfigurationString
from paste.request import parse_formvars

OWL_NS=Namespace('http://www.w3.org/2002/07/owl#')

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
     </script>
  </head>
  <body>
    <div style="margin-right: 10em">
      <h2>SPARQL</h2>
      <p>See: <a href="http://www.w3.org/TR/rdf-sparql-query">SPARQL Query Language for RDF</a></p>
      <form id="queryform" action="ENDPOINT" method="post">
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
          <div><input type="button" value="Submit SPARQL" onClick="submitQuery('queryform')" /></div>
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

def makeTermHTML(endpoint,term,noLink=False,aProp=False):
    """
    Takes a term and turns into an HTML snippet for the browse view, taking care of 
      quoting, etc.
    - noLink indicates whether or not to make it a link
    - aProp indicates whether this term is a property in a statememtn
    """
    if isinstance(term,URIRef):
        if aProp:
            qString = urllib.quote("""SELECT ?S ?O WHERE { ?S <%s> ?O } """%term)
            return noLink and '%s'%term or '<a href="%s?query=%s">%s</a>'%(endpoint,
                                                                           qString,term)
        else:
            return noLink and '%s'%term or \
            '<a href="/browse?action=resource&amp;uri=%s">%s</a>'%(urllib.quote(term),
                                                                   term)
    elif isinstance(term,BNode):
        return noLink and '%s'%term.n3() or \
        '<a href="/browse?action=resource&amp;uri=%s">%s</a>'%(urllib.quote(term.n3()),
                                                               term.n3())
    else:
        return term.n3()

class StoreConnectee(object):
    """
    Superclass for all WSGI applications
    Stores global configuration and provides a method for retrieving
    the underlying SPARQL service graph
    """
    def __init__(self, global_conf):
        self.store_id      = global_conf['store_identifier']
        self.connection    = global_conf['connection']
        self.storeKind     = global_conf['store']
        self.layout        = global_conf['graphVizLayout']
        self.vizualization = global_conf['visualization']
        self.endpoint      = global_conf['endpoint']
        self.dataStoreOWL  = global_conf.get('datastore_owl')
        self.litProps = set()
        self.resProps = set()
        if self.storeKind == 'MySQL' and self.dataStoreOWL:
            ontGraph=Graph().parse(self.dataStoreOWL)
            for litProp,resProp in ontGraph.query(OWL_PROPERTIES_QUERY,
                                                  initNs={u'owl':OWL_NS}):
                if litProp:
                    self.litProps.add(litProp)
                if resProp:
                    #Need to account for OWL Full, where datatype properties
                    #can be IFPs
                    if (resProp,
                        RDF.type,
                        OWL_NS.DatatypeProperty) not in ontGraph:
                        self.resProps.add(resProp)
            print "Registered %s owl:DatatypeProperties"%len(self.litProps)         
            print "Registered %s owl:ObjectProperties"%len(self.resProps)


    def buildGraph(self,default_graph_uri=None):
        store = plugin.get(self.storeKind,Store)(self.store_id)
        store.open(self.connection,create=False)
        #The MySQL store has a special set of attribute for optimizing
        #SPARQL queries based on the characteristics of RDF properties
        #used in the queries
        if self.storeKind == 'MySQL' and self.dataStoreOWL:
            print "Updating the property optimization parameters to the store"
            store.literal_properties =self.litProps
            store.resource_properties=self.resProps
        if default_graph_uri:
            targetGraph = Graph(store,identifier = URIRef(default_graph_uri))
        else:
            targetGraph = ConjunctiveGraph(store)    
        return targetGraph

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
                                                                                                        makeTermHTML(self.endpoint,s,noLink=True),
                                                                                                        makeTermHTML(self.endpoint,p,aProp=True),
                                                                                                        makeTermHTML(self.endpoint,o)])
                else:
                    newRow = ("""<tr><td>%s</td><td>%s</td></tr>""",
                              (makeTermHTML(self.endpoint,p,aProp=True),
                               makeTermHTML(self.endpoint,o)))
                row += 1
                rows.append(newRow)
            row2 = 0
            for s,p,o in targetGraph.triples((None,None,resTerm)):
                if row2 == 0:
                    newRow = ("""<tr><td>%s</td><td>%s</td><td valign="center" align="middle" rowspan='%s'>%s</td></tr>""",[
                                                                                                        makeTermHTML(self.endpoint,s),
                                                                                                        makeTermHTML(self.endpoint,p,aProp=True),
                                                                                                        makeTermHTML(self.endpoint,o,noLink=True)])
                else:
                    newRow = ("""<tr><td>%s</td><td>%s</td></tr>""",
                              (makeTermHTML(self.endpoint,s),
                               makeTermHTML(self.endpoint,p,aProp=True)))
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
            rt=makeGraph(targetGraph,d['uri'],self.layout)
            targetGraph.close()
            response_headers = [('Content-type',' image/png'),('Content-Length',len(rt))]
            start_response(status, response_headers)
            return [rt]
        else:
            targetGraph.close()
            raise Exception("Unknown action: "+action)

def termShape(term):
    if isinstance(term,(URIRef,BNode)):
        return 'ellipse'
    elif isinstance(term,Literal):
        return 'box'
    else:
        raise

def normalizeLabel(graph,res):
    if res == RDF.type:
        return 'is a'
    else:
        return str(res)

def makeGraph(graph,res,layout):
    """
    Generates (and returns) a PNG diagram of the given resource
    within the given graph, using the specified layout
    This requires the installation of pygraphviz (http://networkx.lanl.gov/pygraphviz/)
    """
    import pygraphviz
    try:
        from hashlib import md5
    except ImportError:
        from md5 import md5
    def mkHash(i):
        d = md5(i)
        return d.hexdigest()
    
    G=pygraphviz.AGraph(strict=False,directed=True)
    G.node_attr['shape'] ='ellipse'
    G.node_attr['color'] = 'black'
    objs = set()
    G.add_node(mkHash(res))
    if res.find('_:') == -1:
        G.get_node(mkHash(res)).attr['label']=normalizeLabel(graph,res)
    for s,p,o in graph.triples((URIRef(res),None,None)):
        if o not in objs:
            G.add_node(mkHash(o))
            if not isinstance(o,BNode):
                G.get_node(mkHash(o)).attr['label']=normalizeLabel(graph,o)
            G.get_node(mkHash(o)).attr['shape']=termShape(o)
            G.add_edge(mkHash(s),mkHash(o))
            G.get_edge(mkHash(s),mkHash(o)).attr['label']=normalizeLabel(graph,p)
            objs.add(o)
    for s,p,o in graph.triples((None,None,URIRef(res))):
        if s not in objs:
            G.add_node(mkHash(s))
            if not isinstance(s,BNode):
                G.get_node(mkHash(s)).attr['label']=normalizeLabel(graph,s)
            G.add_edge(mkHash(s),mkHash(o))
            G.get_edge(mkHash(s),mkHash(o)).attr['label']=normalizeLabel(graph,p)
            objs.add(s)
            
    G.layout(layout)
    G.draw('out.png')
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

class WsgiApplication(StoreConnectee):
    def __call__(self, environ, start_response):
        """
        SPARQL Service application
        Works for POST & GET requests, taking query and default_graph_uri as parameters for the query 
        """
        d = parse_formvars(environ)
        query             = d.get('query')
        default_graph_uri = d.get('default-graph-uri')
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
                response_headers = [('Content-type','text/html'),
                                    ('Content-Length',
                                     len(SPARQL_FORM.replace('ENDPOINT',self.endpoint)))]
                start_response(status, response_headers)
                return [SPARQL_FORM.replace('ENDPOINT',self.endpoint)]
        targetGraph = self.buildGraph(default_graph_uri)
        start = time.time()
        rt = targetGraph.query(query)
        print "Time to execute SPARQL query: ", time.time() - start
        qRT = rt.serialize(format='xml')
        targetGraph.close()
        print "Time to seralize SPARQL query: ", time.time() - start
        print "# of bindings: ", len(rt.serialize(format='python'))
        
        rtDoc = NonvalidatingReader.parseString(qRT,
                                                'tag:nobody@nowhere:2007:meaninglessURI')
        pi = rtDoc.createProcessingInstruction("xml-stylesheet",
                                               "type='text/xml' href='/xslt/xml-to-html.xslt'")
        #Add a stylesheet instruction to direct browsers how to render the result document
        rtDoc.insertBefore(pi, rtDoc.documentElement)
        out = StringIO()
        PrettyPrint(rtDoc, stream=out)
        rt = out.getvalue()
        #rt = qRT

        status = '200 OK'
        response_headers = [('Content-type','application/xml'),
                            ('Content-Length',len(rt))]
        start_response(status, response_headers)
        return [rt]