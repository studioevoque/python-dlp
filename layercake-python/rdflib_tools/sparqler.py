#!/usr/bin/env python
"""
sparqler.py - Run SPARQL queries against an existing RDF store.

Copyright 2007 John L. Clark

This program is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation, either version 2 of the License, or (at your option)
any later version.

This program is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

If you do not have a copy of the GNU General Public License, you may obtain
one from <http://www.gnu.org/licenses/>.
"""

import sys, time
from rdflib.sparql.bison.Query import Prolog
from rdflib import plugin, Namespace, URIRef, RDF, BNode, Variable, Literal, RDFS, util
from rdflib.store import Store
import rdflib.sparql.parser
from rdflib.Graph import ConjunctiveGraph, Graph
from rdflib.sparql.sql.RelationalAlgebra import RdfSqlBuilder, ParseQuery, DEFAULT_OPT_FLAGS
from rdflib.sparql.sql.RdfSqlBuilder import *

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

RDFS_NS=Namespace('http://www.w3.org/2000/01/rdf-schema#')

RDFS_PROPERTIES_QUERY=\
"""
SELECT ?literalProperty ?resourceProperty
WHERE {
    { ?literalProperty rdfs:range rdfs:Literal }
                    UNION
    { ?resourceProperty rdfs:range ?range .
      ?range owl:disjointWith rdfs:Literal . }
}"""

def print_set(intro, aSet, stream=sys.stderr):
  print >> stream, intro + ', a set of size %s:' % len(aSet)
  for el in aSet:
    print >> stream, ' ', el

def prepQuery(queryString,ontGraph):
    query=sparql.parser.parse(queryString)
    if ontGraph:
        if not query.prolog:
            query.prolog = Prolog(None, [])
            query.prolog.prefixBindings.update(dict(ontGraph.namespace_manager.namespaces()))
        else:
            for prefix, nsInst in ontGraph.namespace_manager.namespaces():
                if prefix not in query.prolog.prefixBindings:
                    query.prolog.prefixBindings[prefix] = nsInst
        print "Bindings picked up ", query.prolog.prefixBindings
    return query

def main():
    from optparse import OptionParser
    usage = '''usage: %prog [options] \\
    <DB connection string> [<DB table identifier>] <SPARQL query string>'''
    op = OptionParser(usage=usage)
    op.add_option('-s', '--storeKind',
                  metavar='STORE', help='Use this type of DB')
    op.add_option('--owl',default=None,
      help='Owl file used to help identify literal and resource properties')
    op.add_option('--rdfs', default=None,
      help='RDFS file used to help identify literal and resource properties')
    op.add_option('--IdIsNone', action='store_true', default=False, help='Whether or not to assume the '+
                   'store identifier is None in which case the second argument is the query')
    op.add_option('-d', '--debug', action='store_true',
                  help='Enable (store-level) debugging')
    op.add_option('--sparqlDebug', action='store_true',
                  help='Enable (SPARQL evaluation) debugging')  
    op.add_option('--file', default=None,
                  help='File to load SPARQL from')    
    op.add_option('--render', action='store_true',default=False,
                  help='Render a SPARQL snippet')    
    op.add_option('--timing', action='store_true',default=False,
                help='Whether or not to print out timing information')
    op.add_option('-l', '--literal',
                  action='append', dest='literal_properties',
                  metavar='URI',
                  help='Add URI to the list of literal properties')
    op.add_option('-p', '--profile',action='store_true',
                  help='Enable profiling statistics')
    op.add_option('-o','--output',
                  help='The location where to store the SPARQL XML result file '+
                       '(it is printed to STDOUT otherwise)')
    op.add_option('-r', '--resource',
                  action='append', dest='resource_properties',
                  metavar='URI',
                  help='Add URI to the list of resource properties')
    op.add_option('--endpoint',
                  metavar='URL',
                  help='The URL of a SPARQL service to query (DB connection and '+
                       'table identifier not required)')
    op.add_option('--ns',
                  action='append',
                  default=[],
                  metavar="PREFIX=URI",
                  help = 'Register a namespace binding (QName prefix to a base URI).  This '+
                         'can be used more than once')                  


    op.set_defaults(debug=False, storeKind='MySQL')
    (options, args) = op.parse_args()

    if options.endpoint:

        ontGraph=None
        if options.owl:
            ontGraph=Graph().parse(options.owl)
        elif options.rdfs:
            ontGraph=Graph().parse(options.rdfs)

        if ontGraph is None:
            nsBinds = {}
        else:
            nsBinds = dict(ontGraph.namespace_manager.namespaces())
        for nsBind in options.ns:
            pref,nsUri = nsBind.split('=')
            nsBinds[pref]=nsUri

        if len(args) <1 and not options.file:
          op.error('You need to at least provide the query.')

        dataset = Graph(plugin.get('SPARQL', Store)(options.endpoint))
        if options.timing:
            now=time.time()
        res = dataset.query(open(options.file).read() if options.file else args[0],
                            initNs=nsBinds,
                            DEBUG=options.sparqlDebug)
    else:
        if len(args) <2 and not options.IdIsNone:
          op.error(
            'You need to provide a connection string ' +
            '\n(of the form "user=...,password=...,db=...,host=..."), ' +
            '\na table identifier (optional), and a query string.')

        from rdflib.sparql import Algebra
        Algebra.DAWG_DATASET_COMPLIANCE = False
        if len(args)==3:
            connection, identifier, query = args
        elif options.IdIsNone:
            identifier = None
            connection, query = args
        else:
            connection, identifier = args
        store = plugin.get(options.storeKind, Store)(identifier)
        ontGraph=None
        if options.owl:
            ontGraph=Graph().parse(options.owl)
        elif options.rdfs:
            ontGraph=Graph().parse(options.rdfs)

        if ontGraph is None:
            nsBinds = {}
        else:
            nsBinds = dict(ontGraph.namespace_manager.namespaces())
        for nsBind in options.ns:
            pref,nsUri = nsBind.split('=')
            nsBinds[pref]=nsUri

        if options.storeKind == 'MySQL' and options.owl:
            for litProp,resProp in ontGraph.query(OWL_PROPERTIES_QUERY,
                                                  initNs={u'owl':OWL_NS}):
                if litProp:
                    store.literal_properties.add(litProp)
                if resProp:
                    store.resource_properties.add(resProp)
        if options.storeKind == 'MySQL' and options.rdfs:
            for litProp,resProp in ontGraph.query(RDFS_PROPERTIES_QUERY,
                                                  initNs={u'owl':OWL_NS}):
                if litProp:
                    store.literal_properties.add(litProp)
                if resProp:
                    store.resource_properties.add(resProp)
        if options.debug and (options.rdfs or options.owl):
            print "literalProperties: ", litProp
            print "resourceProperties: ", resProp
        rt = store.open(connection, create=False)
        dataset = ConjunctiveGraph(store)
        if options.literal_properties:
            for literalProp in options.literal_properties:
                prefixSplit = literalProp.split(':')
                if prefixSplit and prefixSplit[0] in nsBinds:
                    store.literal_properties.add(URIRef(nsBinds[prefixSplit[0]] + prefixSplit[-1]))
                else:
                    store.literal_properties.add(URIRef(literalProp))
        if options.resource_properties:
            for resourceProp in options.resource_properties:
                prefixSplit = resourceProp.split(':')
                if prefixSplit and prefixSplit[0] in nsBinds:
                    store.resource_properties.add(URIRef(nsBinds[prefixSplit[0]] + prefixSplit[-1]))
                else:
                    store.resource_properties.add(URIRef(resourceProp))
        if options.debug:
            print_set('literal_properties', store.literal_properties)
            print_set('resource_properties', store.resource_properties)
            store.debug = True
        if options.profile:
            import hotshot, hotshot.stats
            prof = hotshot.Profile("sparqler.prof")
            res = prof.runcall(dataset.query,query,DEBUG=options.sparqlDebug)
            prof.close()
            stats = hotshot.stats.load("sparqler.prof")
            stats.strip_dirs()
            stats.sort_stats('time', 'calls')
            print "==="*20
            stats.print_stats(20)
            print "==="*20

        if options.render:
            flags=DEFAULT_OPT_FLAGS.copy()
            flags[OPT_FLATTEN]=False
            sb = RdfSqlBuilder(Graph(store), optimizations=flags)
            if options.file:
                query=prepQuery(open(options.file).read(),ontGraph)
                res = dataset.query(query,DEBUG=True)
                print res
            else:
                query = prepQuery(query,ontGraph)
                root = ParseQuery(query,sb)
                print repr(root)
                root.GenSql(sb)
                sql = sb.Sql()
                print sql
            return
        else:
            flags=DEFAULT_OPT_FLAGS.copy()
            flags[OPT_FLATTEN]=False
            dataset.store.optimizations = flags
            if options.file:
                query=prepQuery(open(options.file).read(),ontGraph)
                if options.timing:
                    now=time.time()
                res = dataset.query('',
                                    initNs=nsBinds,
                                    DEBUG=options.sparqlDebug,
                                    parsedQuery=query)
            else:
                if options.timing:
                    now=time.time()
                res = dataset.query(query,DEBUG=options.sparqlDebug,initNs=nsBinds)
    if options.output:
        f=open(options.output,'w')
        f.write(res.serialize(format='xml'))
        f.close()
    else:
        print res.serialize(format='xml')
    if options.timing:
        print >> sys.stderr,"Time to query and serialize answers ", time.time() - now

if __name__ == '__main__':
    main()
