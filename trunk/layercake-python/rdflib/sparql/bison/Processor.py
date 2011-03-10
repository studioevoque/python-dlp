from pyparsing import ParseException
from rdflib import sparql
from rdflib.store.SPARQL import SPARQLStore

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
              parsedQuery=None):
        from rdflib import RDFS, RDF, OWL
        initNs.update({u'rdfs':RDFS.RDFSNS,u'owl':OWL.OWLNS,u'rdf':RDF.RDFNS}) 
        from rdflib.sparql.bison.Query import Query, Prolog
        assert isinstance(queryString, basestring),"%s must be a string"%queryString
        try:
            if parsedQuery is None:
                import rdflib.sparql.parser
                parsedQuery = sparql.parser.parse(queryString)
            if not parsedQuery.prolog:
                    parsedQuery.prolog = Prolog(None, [])
                    parsedQuery.prolog.prefixBindings.update(initNs)
            else:
                for prefix, nsInst in initNs.items():
                    if prefix not in parsedQuery.prolog.prefixBindings:
                        parsedQuery.prolog.prefixBindings[prefix] = nsInst

            global prolog
            prolog = parsedQuery.prolog
        except ParseException, e:
            if not isinstance(self.graph.store,SPARQLStore):
                raise e

        return self.graph.store.sparql_query(queryString,
                                             parsedQuery,
                                             self.graph,
                                             dataSetBase,
                                             extensionFunctions,
                                             initBindings,
                                             initNs,DEBUG)