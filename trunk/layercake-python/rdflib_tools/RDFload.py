from rdflib.store.FOPLRelationalModel.MySQLMassLoader import PLUGIN_MAP
from rdflib import URIRef, Namespace, BNode, ConjunctiveGraph, RDF, plugin, Literal
from rdflib.Graph import Graph
from rdflib.store import Store

import sys, os, re, datetime

def substitute_uriPattern(string, fName,extension):
    """
    Given a URI pattern like the following:
        http://example.com/{fName}.{extension}

    replace fName and extension with filename and extension of the file

    """
    format_dict = {'fName': fName, 'extension': extension}
    def replace(match):
        return str(format_dict.get(match.group(1)))
    return re.sub(r'\{(\w+)\}', replace, string)

def parseFromDirectory(directory,op,options,extMap,factGraph,uri=None,uriPattern=None,uri4Files=None):
    if uri4Files:
        uri4Files = dict([ tuple(entry.split('=')) for entry in uri4Files])
    else:
        uri4Files = {}
    try:
      dir = os.walk(directory).next()
    except Exception:
      op.error(
        'You need to provide the name of a directory containing the records to load')

    for entry in dir[2]:
      if entry.find('.')+1:
        parts = entry.split('.')
        if len(parts) == 2:
          fName,extension = parts
        else:
          fName = parts[0]
          extension = '.'.join(parts[1:])
      else:
        fName,extension = None,None
      fullFName = '.'.join([fName,extension])
      if not uri and fullFName not in uri4Files:
        assert extension is not None
        assert uriPattern
        entryUri = substitute_uriPattern(uriPattern,fName,extension)
      elif not uri:
        entryUri = uri4Files[fullFName]
      else:
        entryUri = uri
      parseFormat = options.inputFormat
      if extMap:
          if extension and extension in extMap:
            parseFormat = extMap[extension]
          else:
            print >>sys.stderr,"\tSkipping", entry
            continue
      print >>sys.stderr,"Parsing %s as %s into Graph named %s"%(entry,parseFormat,entryUri)
      factGraph.parse(os.path.join(dir[0], entry), publicID=entryUri, format=parseFormat)
    
def main():
  from optparse import OptionParser
  usage = '''usage: %prog [options] <DB Type> [records directory] [records directory] ..'''
  op = OptionParser(usage=usage)
  op.add_option('-c', '--connection', help='Database connection string')
  op.add_option('-i', '--id', help='Database table set identifier')
  op.add_option('--delimited',
    help = 'Directory in which to store delimited files')
  op.add_option('-r', '--reuse', action='store_true',metavar='URI',
    help = 'Reuse existing delimited files instead of creating new ones')
  op.add_option('-u', '--uri', default=None,
    help = 'Target GRAPH URI / Name')
  op.add_option('--uri4File',
      action='append',
      default = [],
      help='A list of filename to URIs mappings to use for the target GRAPH uri')
  op.add_option('--uriList',
                action='append',
                metavar='URI',
                default = [],
                help='A list of URIs (similar to -u) but one per record '+
                'directory if multiple are given')

  op.add_option('-p', '--uriPattern', default=None,metavar='URI PATTERN',
    help = 'Target GRAPH URI / Name pattern ({fName} and {extension) are'+
    ' replaced with the filename and extension of the source file')

  op.add_option('--uriPatternList',
                action='append',
                metavar='URI PATTERN',
                default = [],
                help='A list of URI patterns (similar to -p) but one per record '+
                'directory if multiple are given')

  op.add_option('-d', '--delete', action='store_true',
    help = 'Delete old repository before starting')
  op.add_option('-e', '--extensionMap',
                action='append', dest='extensionMap',
                metavar='EXT=FORMAT',
                default = [],
                help='2 item Tuple of file extension and input format')
  op.add_option('--input-format',
                default='xml',
                dest='inputFormat',
                metavar='RDF_FORMAT',
                choices = ['xml', 'trix', 'n3', 'nt', 'rdfa'],
    help = "The format of the RDF document(s) which serve as the initial facts "+
           " for the RETE network. One of 'xml','n3','trix', 'nt', "+
           "or 'rdfa'.  The default is %default")
  op.add_option('--name', dest='graphName',
    help = 'The name of the graph to parse the RDF serialization(s) into')

  op.set_defaults(connection=None, delimited='delimited_dumps', id=None,
                  xml=[], trix=[], n3=[], nt=[], rdfa=[],
                  graphName=BNode())
  (options, args) = op.parse_args()

  if options.delimited is not None:
    options.delimited = os.path.abspath(options.delimited)

  if not options.id:
    op.error('You need to provide a table set identifier')

  try:
    store = PLUGIN_MAP[args[0]](identifier=options.id,
      delimited_directory=options.delimited,
      reuseExistingFiles=options.reuse)
  except Exception, e:
    print e
    op.error('You need to provide a database type (MySQL or PostgreSQL).')

  store.open(options.connection)

  if len(args) > 1:
    factGraph = ConjunctiveGraph(store, identifier=options.graphName) 
    extMap = dict((eMap.split('=') for eMap in options.extensionMap))

    multipleDirs = len(args) > 2

    if multipleDirs:
        for idx,directory in enumerate(args[1:]):
            print >>sys.stderr,"Parsing from directory %s"%directory
            parseFromDirectory(
                directory,
                op,
                options,
                extMap,
                factGraph,
                uri=options.uriList[idx] if options.uriList else None,
                uri4Files = options.uri4File if options.uri4File else None,
                uriPattern=options.uriPatternList[idx] if options.uriPatternList else None)
    else:
        parseFromDirectory(args[1],
                           op,
                           options,
                           extMap,
                           factGraph,
                           uri=options.uri,
                           uriPattern=options.uriPattern)
  store.dumpRDF('solo')
  store.close()

  if options.connection:
    if options.delete:
      store.open(options.connection)
      store.destroy(options.connection)
      store.close()

    store.create(options.connection, False)

    cursor = store._db.cursor()

    if False:
      store.initDenormalizedTables(cursor)
      print >> sys.stderr, "Finished loading the denormalized tables..."
      store.indexTriplesTable(cursor,
        ['subject', 'predicate', 'object', 'data_type', 'context'])
      print >> sys.stderr, "Finished indexing the triples table..."
      store.indexLexicalTable(cursor)
      print >> sys.stderr, "Finished indexing the lexical table..."

    store.applyIndices()
    print >> sys.stderr, "Finished indexing..."

    store.loadLiterals()
    print >> sys.stderr, "Finished loading the literals..."
    store.loadIdentifiers()
    print >> sys.stderr, "Finished loading the identifiers..."
    store.loadAssociativeBox()
    print >> sys.stderr, "Finished loading the abox..."
    store.loadLiteralProperties()
    print >> sys.stderr, "Finished loading the literal properties..."
    store.loadRelations()
    print >> sys.stderr, "Finished loading the general triples..."

    store.applyForeignKeys()
    print >> sys.stderr, "Finished setting up foreign keys..."
    store.timestamp.elapsed()

def datasetInfo():
    from optparse import OptionParser
    usage = '''usage: %prog [options] <DB Type>'''
    op = OptionParser(usage=usage)
    op.add_option('-c', '--connection', help='Database connection string')
    op.add_option('-i', '--id', help='Database table set identifier')
    (options, args) = op.parse_args()

    store = plugin.get(args[0], Store)(options.id)
    store.open(options.connection)
    dataset = ConjunctiveGraph(store)
    sdGraph = Graph()

    SD_NS = Namespace('http://www.w3.org/ns/sparql-service-description#')
    SCOVO = Namespace('http://purl.org/NET/scovo#')
    VOID  = Namespace('http://rdfs.org/ns/void#')
    
    sdGraph.bind(u'sd',SD_NS)
    sdGraph.bind(u'scovo',SCOVO)
    sdGraph.bind(u'void',VOID)

    service = BNode()
    datasetNode = BNode()
    sdGraph.add((service,RDF.type,SD_NS.Service))
    sdGraph.add((service,SD_NS.defaultDatasetDescription,datasetNode))
    sdGraph.add((datasetNode,RDF.type,SD_NS.Dataset))
    for graph in dataset.contexts():
        graphNode  = BNode()
        graphNode2 = BNode()
        sdGraph.add((datasetNode,SD_NS.namedGraph,graphNode))
        sdGraph.add((graphNode,SD_NS.name,URIRef(graph.identifier)))
        sdGraph.add((graphNode,SD_NS.graph,graphNode2))
        sdGraph.add((graphNode2,RDF.type,SD_NS.Graph))
        statNode = BNode()
        sdGraph.add((graphNode2,SD_NS.statItem,statNode))
        sdGraph.add((statNode,SCOVO.dimension,VOID.numberOfTriples))
        noTriples = Literal(len(graph))
        sdGraph.add((statNode,RDF.value,noTriples))
    print sdGraph.serialize(format='pretty-xml')

if __name__ == '__main__':
  main()
