#!/usr/bin/python
"""
The XML parsing and serialization of a SPARQL XML document (produced via STDIN) is done using Amara in order to
ensure the entire process is completely streamedi and uses the csv module for writing out to CSV.  

See URL below for more information about Amara

http://wiki.xml3k.org/Amara/Tutorial

"""
import csv,sys, re
from amara.lib import U
from amara.pushtree import pushtree
from amara.bindery.nodes import entity_base
from amara import bindery, parse, ReaderError
from amara.lib.util import coroutine
from amara.writers.struct import structwriter, E, NS, ROOT, E_CURSOR
from cStringIO import StringIO

class Counter(object):
    def __init__(self):
        self.counter     = 0
        self.skipCounter = 0

def produce_csv(doc,csvWriter,justCount,projectVars):
    if not projectVars:
        def receive_header(node):
            for var in node.variable:
                projectVars.append(U(var.name))

        pushtree(doc, u'head', receive_header, entity_factory=entity_base)

    cnt=Counter()

    @coroutine
    def receive_nodes(cnt):
        while True:
            node = yield
            if justCount:
                cnt.counter+=1
            else:
                rt=[]
                badChars = False
                bindings = {}
                for binding in node.binding:
                    try:
                        newterm=U(binding).encode('ascii')
                    except UnicodeEncodeError:
                        newterm=U(binding).encode('ascii', 'ignore')
                        badChars = True
                        print >> sys.stderr, "Skipping character"
                    if newterm:
                        if projectVars:
                            bindings[binding.name]=newterm
                        else:
                            rt.append(newTerm)

                for head in projectVars:
                    rt.append(bindings.get(head,''))
                if badChars:
                    cnt.skipCounter += 1
                csvWriter.writerow(rt)
        return

    target = receive_nodes(cnt)
    pushtree(doc, u'result', target.send, entity_factory=entity_base)
    target.close()
    return cnt

def main():
    from optparse import OptionParser
    usage = '''usage: %prog [options] [SPARQLXMLFilePath]'''
    op = OptionParser(usage=usage)
    op.add_option('-q',
                  '--quoteChar',
                  default='"',
                  help='The quote character to use')
    op.add_option('-c',
                  '--count',
                  action='store_true',
                  default=False,
                  help='Just count the results, do not serialize to CSV')
    op.add_option('--chopped',
              action='store_true',
              default=False,
              help='Whether or not this is one of many files chopped up by <result> tag')
    op.add_option('-d',
                  '--delimiter',
                  default='\t',
                  help='The delimiter to use')
    op.add_option('--header',
                  default='',
                  help='The comma separated list of selected variables in order')
    op.add_option('-o',
                  '--output',
                  metavar='FILEPATH',
                  default=None,
                  help='The path where to write the resulting CSV file')
    (options, args) = op.parse_args()

    outStream = open(options.output, 'wb') if options.output else sys.stdout
    if not options.count:
        writer = csv.writer(outStream,
                            delimiter=options.delimiter,
                            quotechar=options.quoteChar,
                            quoting=csv.QUOTE_MINIMAL)
    else:
        writer = None
    doc = open(args[0]) if args else sys.stdin
    skeleton=None
    doc=doc.read()
    if options.chopped:
        assert isinstance(doc,basestring)
        if doc.find('<sparql')+1:
            skeleton='%s</results></sparql>'
        elif doc.find('</sparql>')+1:
            skeleton='<?xml version="1.0"?><sparql><results>%s'
        else:
            skeleton='<?xml version="1.0"?><sparql><results>%s</results></sparql>'
        doc = skeleton%doc

    vars = [head.strip() for head in options.header.split(',')] if options.header else []
    counter=produce_csv(doc,
                        writer,
                        options.count,
                        vars)

    if options.count:
        print "Number of results: ", counter.counter
    if counter.skipCounter:
        print >> sys.stderr, "Encountered Unicode encoding issues in %s solutions"%counter.skipCounter
