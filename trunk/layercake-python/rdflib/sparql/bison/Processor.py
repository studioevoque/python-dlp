from rdflib import sparql

def CreateSPARQLParser(debug=False):
    import SPARQLParserc as SPARQLParser
    return SPARQLParser.new(debug=debug)    

def Parse(query,debug = False):    
    p = CreateSPARQLParser(debug)
    if debug:
        try:
           p.debug_mode(1)
        except:
            p.debug = 1    
    if not isinstance(query, unicode):
        query = unicode(query,'utf-8')
    return p.parse(query)

class Processor(sparql.Processor):

    def __init__(self, graph):
        self.graph = graph

    def query(self, 
              queryString,
              initBindings={}, 
              initNs={}, 
              DEBUG=False,
              PARSE_DEBUG=False,
              dataSetBase=None,
              extensionFunctions={},
              USE_PYPARSING=False,
              parsedQuery=None):
        from rdflib import RDFS, RDF, OWL
        initNs.update({u'rdfs':RDFS.RDFSNS,u'owl':OWL.OWLNS,u'rdf':RDF.RDFNS}) 
        from rdflib.sparql.bison.Query import Query, Prolog
        assert isinstance(queryString, basestring),"%s must be a string"%queryString
        if parsedQuery is None:
            if USE_PYPARSING:
                import rdflib.sparql.parser
                parsedQuery = sparql.parser.parse(queryString)
            else:
                parsedQuery = Parse(queryString, PARSE_DEBUG)
        if not parsedQuery.prolog:
                parsedQuery.prolog = Prolog(None, [])
                parsedQuery.prolog.prefixBindings.update(initNs)
        else:
            for prefix, nsInst in initNs.items():
                if prefix not in parsedQuery.prolog.prefixBindings:
                    parsedQuery.prolog.prefixBindings[prefix] = nsInst
                    
        global prolog            
        prolog = parsedQuery.prolog

        return self.graph.store.sparql_query(queryString,
                                             parsedQuery,
                                             self.graph,
                                             dataSetBase,
                                             extensionFunctions,
                                             initBindings,
                                             initNs,DEBUG)