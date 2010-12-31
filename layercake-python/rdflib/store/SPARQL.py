#!/d/Bin/Python/python.exe
# -*- coding: utf-8 -*-
#
"""
This is an adaptation of Ivan Herman et al.'s SPARQL service wrapper augmented in the
following ways:

- Adding support for namespace binding
- JSON object mapping support suppressed
- Replaced 'native' Python XML DOM api with 4Suite-XML Domlette
- Incorporated as an rdflib store

"""

__version__ = "1.01"
__authors__  = u"Ivan Herman, Sergio Fernández, Carlos Tejo Alonso"
__license__ = u'W3C® SOFTWARE NOTICE AND LICENSE, http://www.w3.org/Consortium/Legal/2002/copyright-software-20021231'
__contact__ = 'Ivan Herman, ivan_herman@users.sourceforge.net'
__date__    = "2008-02-14"

import re
from rdflib.sparql.Client.Wrapper import SPARQLWrapper, XML, JSON, TURTLE, N3, GET, POST, SELECT, CONSTRUCT, ASK, DESCRIBE
from rdflib.sparql.Client import SPARQLResult
from rdflib.store import Store
from rdflib.store.REGEXMatching import NATIVE_REGEX
from rdflib       import Namespace, Variable, BNode, URIRef, Literal
from rdflib.Graph import Graph
from rdflib.sparql.Client import TraverseSPARQLResultDOM, SPARQL_NS, sparqlNsBindings

BNODE_IDENT_PATTERN = re.compile('(?P<label>_\:[^\s]+)')

class SPARQLStore(SPARQLWrapper,Store):
    """
    Abstract SQL implementation of the FOPL Relational Model as an rdflib
    Store.
    """
    context_aware = True
    formula_aware = False
    transaction_aware = False
    regex_matching = NATIVE_REGEX
    batch_unification = False
    def __init__(self,identifier,bNodeAsURI = False):
        super(SPARQLStore, self).__init__(identifier,returnFormat=XML)
        self.bNodeAsURI = bNodeAsURI

    #Database Management Methods
    def create(self, configuration):
        raise TypeError('The SPARQL store is read only')

    def open(self, configuration, create=False):
        """
        Opens the store specified by the configuration string. If
        create is True a store will be created if it does not already
        exist. If create is False and a store does not already exist
        an exception is raised. An exception is also raised if a store
        exists, but there is insufficient permissions to open the
        store.
        """
        pass

    def destroy(self, configuration):
        """
        FIXME: Add documentation
        """
        raise TypeError('The SPARQL store is read only')

    #Transactional interfaces
    def commit(self):
        """ """
        raise TypeError('The SPARQL store is read only')

    def rollback(self):
        """ """
        raise TypeError('The SPARQL store is read only')


    def add(self, (subject, predicate, obj), context=None, quoted=False):
        """ Add a triple to the store of triples. """
        raise TypeError('The SPARQL store is read only')

    def addN(self, quads):
        """
        Adds each item in the list of statements to a specific context. The quoted argument
        is interpreted by formula-aware stores to indicate this statement is quoted/hypothetical.
        Note that the default implementation is a redirect to add
        """
        raise TypeError('The SPARQL store is read only')

    def remove(self, (subject, predicate, obj), context):
        """ Remove a triple from the store """
        raise TypeError('The SPARQL store is read only')

    def sparql_query(self,
                     queryString,
                     queryObj,
                     graph,
                     dataSetBase,
                     extensionFunctions,
                     initBindings={},
                     initNs={},
                     DEBUG=False):
        self.debug = DEBUG
        assert isinstance(queryString,basestring)
        self.setNamespaceBindings(initNs)
        self.setQuery(queryString)
        return SPARQLResult(self.query().response.read())

    def triples(self, (subject, predicate, obj), context=None):
        """
        SELECT ?subj ?pred ?obj WHERE { ?subj ?pred ?obj }
        """
        from Ft.Xml.Domlette import NonvalidatingReader
        subjVar = Variable('subj')
        predVar = Variable('pred')
        objVar  = Variable('obj')

        termsSlots = {}
        selectVars = []
        if subject is not None:
            termsSlots[subjVar] = subject
        else:
            selectVars.append(subjVar)
        if predicate is not None:
            termsSlots[predVar] = predicate
        else:
            selectVars.append(predVar)
        if obj is not None:
            termsSlots[objVar] = obj
        else:
            selectVars.append(objVar)

        query ="SELECT %s WHERE { %s %s %s }"%(
            ' '.join([term.n3() for term in selectVars]),
            termsSlots.get(subjVar, subjVar).n3(),
            termsSlots.get(predVar, predVar).n3(),
            termsSlots.get(objVar , objVar ).n3()
        )

        self.setQuery(query)
        doc = NonvalidatingReader.parseStream(self.query().response)
        for rt,vars in TraverseSPARQLResultDOM(doc,asDictionary=True):
            yield (rt.get(subjVar,subject),
                   rt.get(predVar,predicate),
                   rt.get(objVar,obj)),None

    def triples_choices(self, (subject, predicate, object_),context=None):
        """
        A variant of triples that can take a list of terms instead of a single
        term in any slot.  Stores can implement this to optimize the response time
        from the import default 'fallback' implementation, which will iterate
        over each term in the list and dispatch to tripless
        """
        raise NotImplementedError('Triples choices currently not supported')

    def __len__(self, context=None):
        raise NotImplementedError("For performance reasons, this is not supported")

    def contexts(self, triple=None):
        """
        iterates over results to SELECT ?NAME { GRAPH ?NAME { ?s ?p ?o } }
        returning instances of this store with the SPARQL wrapper
        object updated via addNamedGraph(?NAME)
        This causes a named-graph-uri key / value  pair to be sent over the protocol
        """
        raise NotImplementedError(".contexts(..) not supported")
        self.setQuery("SELECT ?NAME { GRAPH ?NAME { ?s ?p ?o } }")
        doc = NonvalidatingReader.parseStream(self.query().convert)
        for result in doc.xpath('/sparql:sparql/sparql:results/sparql:result',
                                explicitNss=sparqlNsBindings):
            statmentTerms = {}
            for binding in result.xpath('sparql:binding',
                                        explicitNss=sparqlNsBindings):
                term = CastToTerm(binding.xpath('*')[0])
                newStore = SPARQLStore(self.baseURI)
                newStore.addNamedGraph(term)
                yield Graph(self,term)

    #Namespace persistence interface implementation
    def bind(self, prefix, namespace):
        self.nsBindings[prefix]=namespace

    def prefix(self, namespace):
        """ """
        return dict([(v,k) for k,v in self.nsBindings.items()]).get(namespace)

    def namespace(self, prefix):
        return self.nsBindings.get(prefix)

    def namespaces(self):
        for prefix,ns in self.nsBindings.items():
            yield prefix,ns