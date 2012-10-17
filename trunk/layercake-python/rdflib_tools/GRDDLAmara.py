#!/usr/bin/env python
"""
Gleaning Resource Descriptions from Dialects of Languages (GRDDL)

That is, GRDDL provides a relatively inexpensive mechanism for
bootstrapping RDF content from uniform XML dialects; shifting the
burden from formulating RDF to creating transformation algorithms
specifically for each dialect. XML Transformation languages such as
XSLT are quite versatile in their ability to process, manipulate, and
generate XML. The use of XSLT to generate XHTML from single-purpose
XML vocabularies is historically celebrated as a powerful idiom for
separating structured content from presentation.

GRDDL shifts this idiom to a different end: separating structured
content from its authoritative meaning (or semantics). GRDDL works by
associating transformations for an individual document, either through
direct inclusion of references or indirectly through profile and
namespace documents.

See: 
- http://4suite.org/docs/CoreManual.xml#xpath_query
- http://4suite.org/docs/CoreManual.xml#xslt_engine
- http://4suite.org/docs/CoreManual.xml#id1219140460
   (for http://www.w3.org/2004/01/rdxh/spec#issue-base-param)

Copyright (c) 2006, Chimezie Ogbuji
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of inamidst.com nor the names of its
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""
import time, sys, re, getopt, urllib2
#from sets import Set
try:
    from cStringIO import StringIO
except ImportError:        
    from StringIO import StringIO
from pprint import pprint
from rdflib import Variable, BNode, URIRef, Literal, Namespace, RDF, RDFS
from rdflib.Collection import Collection
from rdflib.Graph import ConjunctiveGraph, ReadOnlyGraphAggregate, Graph
from rdflib.syntax.NamespaceManager import NamespaceManager
import amara
from amara.xslt import transform
from amara.lib.iri import absolutize
from amara.lib import U
from Ft.Xml.Xslt import Processor
from Ft.Xml import InputSource

XML_MT = 'application/xml'
XML_text_MT = 'text/xml' # deprecated by webarch
XSLT_MT = XML_MT
RDF_MT = 'application/rdf+xml'
XHTML_MT = 'application/xhtml+xml'
XHTML_text_MT = 'text/html'

GRDDL_PROFILE = u'http://www.w3.org/2003/g/data-view'
GRDDL_NS = GRDDL_PROFILE + '#'
GRDDL_VOCAB = Namespace(GRDDL_NS)
XHTML_NS = u"http://www.w3.org/1999/xhtml"

#Built-in list of namespace uri's that should terminate any recursive
#namespace dispatch
NSDispatchTermination = [XHTML_NS, unicode(RDF.RDFNS)]

class Glean(object):
    """
    Handles all the GRDDL XML parsing and XSLT transformation from URLs
    """
    def __init__(self, 
                 url, 
                 graph, 
                 preParsedDOM=None, 
                 useXInclude=True,
                 DEBUG = False,
                 preCalculatedBase = None):
        self.graph = graph
        self.url = url
        self.baseURI = preCalculatedBase
        self.doc = preParsedDOM
        self.appliedTransforms = []
        self.useXInclude = useXInclude
        self.DEBUG = DEBUG

    def load(self, webget):
        """
        
        >>> g = Glean(u'http://www.w3.org/2003/g/po-doc.xml',Graph())
        >>> g.load(WebMemo())
        >>> g.dom.documentElement.localName
        u'purchaseOrder'
        """
        if self.doc: return

        lastUri, (content, self.headers) = webget(self.url,
                                       (RDF_MT,
                                        XML_MT, XML_text_MT,
                                        XHTML_MT, XHTML_text_MT))
        if lastUri != self.url:
            ##We want the retrieval URL even in the face of a redirect
            self.url = lastUri             
        parsedAsRDF = False
        
        #Until we peak in for a base, use the one given or the retrieval URL
        initialBase = self.baseURI and self.baseURI or self.url
        
        #peek in response headers to determine content-type
        #NOTE we need to attempt to parse the source as RDF/XML regardless (by the base case rule):
        #If an information resource IR is represented by a conforming RDF/XML document[RDFX], then 
        #the RDF graph represented by that document is a GRDDL result of IR.
        if self.headers['content-type'].startswith(RDF_MT):
            try:
                self.graph.parse(StringIO(content),publicID=initialBase)
                parsedAsRDF = True
            except:
                pass
            self.doc = None

        try:
            if self.DEBUG:
                print >>sys.stderr, "Parsing XML content WRT baseURI of %s"%(initialBase)
            self.doc = amara.parse(content,self.url)
            self.docSrc = content
            #don't use useXInclude
            #WG consensus is to follow XML Base.  This bottoms out in using
            #the base URI of the root node once the parser has been given
            #the base that HTTP indicates via RFC 3986
            #Note: this interpretation is based off the assumption that the
            #encapsulating context for a GRDDL result is the root node of the
            #source document
            #See: http://4suite.org/docs/CoreManual.xml#base_URIs
            if self.baseURI is None:
                self.baseURI = self.doc.xml_select(u'/*')[0].xml_base
                if self.DEBUG:
                    print >>sys.stderr,\
                     "Adopting the baseURI of the root node: %s"%(self.baseURI)
            
            #Note, if an XHTML Base is embedded, it needs to be respected also
            for htmlBase in self.doc.xml_select(
                u'/xhtml:html/xhtml:head/xhtml:base/@href',{u'xhtml': XHTML_NS}):
                if self.DEBUG:
                    print >>sys.stderr, "Found an XHTML Base: %s"%(htmlBase.value)
                self.baseURI = U(htmlBase)
                        
            #WG consensus is that we should peek into XML content for rdf:RDF
            #at the root, if we find it we need to attempt a parse as RDF/XML
            if not parsedAsRDF and self.doc.xml_select(u'/rdf:RDF',{u'rdf':str(RDF.RDFNS)}):
                try:
                    self.graph.parse(StringIO(content), publicID=self.baseURI)
                except:
                    pass
                        
        except Exception, e: #@@ narrow exception
            if self.DEBUG:
                print >>sys.stderr, "Unable to parse ", self.baseURI, repr(e)
            #Unable to glean.  Fail gracefully..
            self.doc = None
        
    def transform(self, transformURLs, webget):
        """
        Takes a space seperated list of transform url's and applies
        them against the pre-parsed DOM of the GRDDL source - making
        sure to avoid transformation already applied
        """                
        for xformURL in transformURLs.split():
            if self.DEBUG:
                print >>sys.stderr, "applying transformation %s" % (xformURL)
            if xformURL not in self.appliedTransforms:
                self.appliedTransforms.append(xformURL)
            #The transform url is resolved against the source URL (to
            #accomodate relative urls)
            stylesheetLoc = absolutize(xformURL, self.baseURI)
            lastUri, (content, info) = webget(stylesheetLoc, (XSLT_MT,))
            _transform = InputSource.DefaultFactory.fromString(content,
                                                              stylesheetLoc)
            iSrc = InputSource.DefaultFactory.fromString(self.docSrc,self.url)
            processor = Processor.Processor()
            processor.appendStylesheet(_transform)
            #see: http://www.w3.org/TR/grddl/#stylepi
            #Note, for the XSLT transform, the base URI of the source document
            #is passed in, instead of the base URI of the root node   
            result = processor.run(
                iSrc,ignorePis=1
            )
            #get output method / media-type
#            <!-- Category: top-level-element -->
#            <xsl:output
#              method = "xml" | "html" | "text" | qname-but-not-ncname
#              version = nmtoken
#              encoding = string
#              omit-xml-declaration = "yes" | "no"
#              standalone = "yes" | "no"
#              doctype-public = string
#              doctype-system = string
#              cdata-section-elements = qnames
#              indent = "yes" | "no"
#              media-type = string />

            #How to accomodate @media-type?
            method = processor.outputParams.method[-1]
            currLen = len(self.graph)
            if method == 'xml':
                self.graph.parse(StringIO(result), 
                                 publicID=self.baseURI)
                replace = [(URIRef(self.baseURI),p,o,self.graph) for s,p,o in \
                               self.graph.triples((URIRef(''),None,None))]
                if replace:
                    if self.DEBUG:
                        print >>sys.stderr, \
                          "Replacing empty string URI ref with %s" % (
                            self.baseURI)                        
                    self.graph.remove((URIRef(''),None,None))
                    self.graph.addN(replace)                
                if self.DEBUG:
                    print >>sys.stderr,\
                     "Parsed %s triples (using baseURI: %s) as RDF/XML" % (
                        max(0,len(self.graph) - currLen),self.baseURI)
            elif method == 'text':
                #Attempt a Notation 3 parse (covers NTriples, and Turtle)
                try:
                    self.graph.parse(StringIO(result), format='n3',
                                     publicID=self.baseURI)
                    #@@This is mostly as a workaround for RDFLib 2.4 which will 
                    #force an empty URI string as the subject if xml:base = ''                    
                    replace = [(URIRef(self.baseURI),p,o,self.graph) for s,p,o in \
                                   self.graph.triples((URIRef(''),None,None))]
                    if replace:
                        if self.DEBUG:
                            print >>sys.stderr, \
                              "Replacing empty string URI ref with %s" % (
                                self.baseURI)                        
                        self.graph.remove((URIRef(''),None,None))
                        self.graph.addN(replace)                    
                    if self.DEBUG:
                        print >>sys.stderr, \
                        "Parsed %s triples (using baseURI: %s) as Notation 3" % (
                            max(0,len(self.graph) - currLen),self.baseURI)
                except:
                    if self.DEBUG:
                        print >>sys.stderr, "Unknown text-based RDF serialization"
            else:
                #HTML result - recursive GRDDL mechanism?
                raise Exception("unsupported output type")

def GRDDLAgent(url, graph, webget, useXInclude=True, DEBUG = False):
    """
    The main entry point for the GRDDL agent Takes a url and a graph
    to store the GRDDL result and a webget function and attempts to
    'glean' in the 4 major ways that GRDDL specifies.
    """
    if DEBUG:
        print >>sys.stderr, "Attempting a comprehensive glean of ", url
        print >>sys.stderr, "graph size before:", len(graph)
    parsedSource  = None
    sourceBaseURI = None
    if url not in webget.gleanQueue:
        webget.gleanQueue.add(url)
        for gleanMethod in [XMLGlean, XMLNSGlean, XHTMLProfileGlean,
                            ValidXHTMLGlean]:
            #Don't reparse the GRDDL source
            try:
                if not parsedSource:
                    gleaned = gleanMethod(url, 
                                          graph, 
                                          useXInclude=useXInclude, 
                                          DEBUG = DEBUG)
                    gleaned.load(webget)
                    parsedSource = gleaned.doc
                    sourceBaseURI = gleaned.baseURI                
                else:
                    gleaned = gleanMethod(url, 
                                          graph, 
                                          preParsedDOM=parsedSource, 
                                          DEBUG = DEBUG, 
                                          preCalculatedBase = sourceBaseURI)
                    gleaned.load(webget)
            except Exception, e:
                #Each GRDDL mechanism is independent, fail safely
                if DEBUG:
                    print >>sys.stderr, "Failed glean method of %s on %s: %s"%(gleanMethod.__name__,url,e)
                if url in webget.gleanQueue:
                    webget.gleanQueue.remove(url)
        if DEBUG:
            print >>sys.stderr, "Marking %s as gleaned"%url                
    else:
        if DEBUG:
            print >>sys.stderr, "Skipping previously glean request for source uri: ", url    
    if DEBUG:
        print >>sys.stderr, "graph size after:", len(graph)

class XMLGlean(Glean):
    """
    http://www.w3.org/TR/grddl/#grddl-xml - Adding GRDDL to well-formed XML
    
    The general form of associating a GRDDL transformation link with a
    well-formed XML document is by adorning the root element with a
    grddl namespace declaration and a grddl:transformation attribute
    whose value is a URI reference, or list of URI references, that
    refer to executable scripts or programs which are expected to
    transform the source document into RDF.
        
    """
    def load(self, webget):
        """        
        >>> g = XMLGlean(u'http://www.w3.org/2003/g/po-ex', Graph())
        >>> g.load(WebMemo())
        >>> g.appliedTransforms[0]
        u'http://www.w3.org/2003/g/embeddedRDF.xsl'
        >>> pprint(list(g.graph))
        [(u'http://www.w3.org/2003/g/po-ex',
          u'http://www.w3.org/2003/g/data-view#namespaceTransformation',
          u'http://www.w3.org/2003/g/grokPO.xsl')]
        """
        super(XMLGlean, self).load(webget)
        if self.doc:
            attrs = self.doc.xml_select(u'/*/@data-view:transformation',
                                   {u'data-view': GRDDL_NS})
            if attrs:
                self.transform(U(attrs[0]), webget)

class XMLNSGlean(Glean):
    """
    http://www.w3.org/TR/grddl/#ns-bind - Using GRDDL with XML Namespace Documents
    
    Any resource available for retrieval from a namespace URI is a
    namespace document (cf. section 4.5.4. Namespace documents in
    [WEBARCH]). For example, a namespace document may have an XML
    Schema representation or an RDF Schema representation, or perhaps
    both
        
    To associate a GRDDL transformation with a whole dialect, have the
    namespace document include the grddl:namespaceTransformation
    property.
    
    """

    def load(self, webget):
        """
        
        >>> g = XMLNSGlean(u'http://www.w3.org/2003/g/po-doc.xml', Graph())
        >>> g.load(WebMemo())
        >>> g.nsURI
        u'http://www.w3.org/2003/g/po-ex'
        >>> len(g.graph)
        15
        """
        super(XMLNSGlean, self).load(webget)
        self.nsURI = None
        if self.doc:
            self.nsURI = self.doc.xml_select(u'/*')[0].xml_namespace

            #@@DWC: hmm... why is NSDispatchTermination not recursive?
            if not self.nsURI or self.nsURI in NSDispatchTermination or self.nsURI == self.url:
                return

            #glean GRDDL result from the namespace document
            try:
                nsresult = Graph()
                GRDDLAgent(absolutize(self.nsURI, self.baseURI), nsresult, webget, DEBUG = self.DEBUG)
                if self.DEBUG:
                    print >>sys.stderr, "ns doc graph size", len(nsresult)
            except IOError:
                pass # don't bother if we can't get a namespace document
            else:
                continueRecursion = True
                #setup a set of processed transforms to avoid infinite
                #namespace snooping cycles
                processedNSXForms = set()
                #Recursively find 'new' namespace transformations
                while continueRecursion:
                    todoXForms = set()
                    pat = (URIRef(absolutize(self.nsURI, self.baseURI)), GRDDL_VOCAB.namespaceTransformation, None)
                    for s, p, xform in nsresult.triples(pat):
                        if self.DEBUG:
                            print >>sys.stderr, "found txform in NS doc:", xform
                        if xform not in processedNSXForms:
                            todoXForms.add(xform)
                    #continue only if we have xforms to apply
                    continueRecursion = bool(todoXForms)
                    #apply the new namespace transforms on the GRDDL
                    #source, merging the GRDDL results as we go
                    for newXForm in todoXForms:
                        self.transform(newXForm, webget)
                        processedNSXForms.add(newXForm)

class ValidXHTMLGlean(Glean):
    """
    http://www.w3.org/TR/grddl/#grddl-xhtml - Using GRDDL with valid XHTML
    
    The general form of adding a GRDDL assertion to a valid XHTML document 
    is by specifying the GRDDL profile in the profile attribute of the head 
    element, and transformation as the value of the rel attribute of a link 
    or a element whose href attribute value is a URI reference that refers 
    to an executable script or program which is expected to transform the 
    source document into RDF. This method is suitable for use with valid 
    XHTML documents which are constrained by an XML DTD.
    
    Stated more formally:

    * An XHTML document whose metadata profiles include 
      http://www.w3.org/2003/g/data-view has a GRDDL transformation for each 
      resource identified by a link of type transformation.
              
    """
    def load(self, webget):
        super(ValidXHTMLGlean, self).load(webget)
        if self.doc:
            xhtmlNSMap = {u'xhtml': XHTML_NS}

            #@@ contains() test isn't quite right
            links = self.doc.xml_select(u"""/xhtml:html[xhtml:head[
                                       contains(@profile, "%s")]]
                                       //xhtml:*[(local-name() = "a"
                                       or local-name() = "link")
                                       and contains(@rel,"transformation")]
                                       /@href""" % GRDDL_PROFILE,
                                   xhtmlNSMap)
            for href in links:
                self.transform(U(href), webget)

class XHTMLProfileGlean(Glean):
    """
    http://www.w3.org/TR/grddl/#profile-bind - GRDDL for HTML Profiles
    
    """

    def load(self, webget):
        """
        >>> g = XHTMLProfileGlean(u'http://www.w3.org/2003/g/data-view', Graph())
        >>> g.load(WebMemo())
        >>> GRDDL_PROFILE in g.profiles
        True
        
        """
        super(XHTMLProfileGlean, self).load(webget)
        self.profiles = []
        if self.doc:
            profile = self.doc.xml_select(u'/xhtml:html/xhtml:head/@profile',
                                     {u'xhtml':XHTML_NS})
            if profile:
                self.profiles = U(profile[0]).split()
                for profile in self.profiles:
                    if profile == GRDDL_PROFILE or profile == self.url:
                        #@@What about if a document is it's own profile?
                        continue
                    if self.DEBUG:
                        print >>sys.stderr, "processing profile url: ", profile
                    #glean GRDDL result from the profile document
                    prresult = Graph()
                    GRDDLAgent(absolutize(profile, self.baseURI), prresult, webget, DEBUG = self.DEBUG)
                    continueRecursion = True
                    #setup a set of processed transforms to avoid
                    #infinite profile snooping cycles
                    processedProfileXForms = set()
                    #Recursively find 'new' namespace transformations
                    while continueRecursion:
                        todoXForms = et()
                        if self.DEBUG:
                            print >>sys.stderr, "checking for profileTransformation triples with subject of: ",absolutize(profile, self.baseURI)
                        pat = (URIRef(absolutize(profile, self.baseURI)), GRDDL_VOCAB.profileTransformation, None)
                        for s, p, xform in prresult.triples(pat):
                            if self.DEBUG:
                                print >>sys.stderr, "Found: (%s,%s)"%(p,xform) 
                            if xform not in processedProfileXForms:
                                todoXForms.add(xform)
                        #continue only if we have xforms to apply
                        continueRecursion = bool(todoXForms)
                        #apply the new namespace transforms on the
                        #GRDDL source, merging the GRDDL results as we
                        #go
                        for newXForm in todoXForms:
                            self.transform(newXForm, webget)
                            processedProfileXForms.add(newXForm)



class SmartRedirectHandler(urllib2.HTTPRedirectHandler):     
    def http_error_301(self, req, fp, code, msg, headers):  
        result = urllib2.HTTPRedirectHandler.http_error_301( 
            self, req, fp, code, msg, headers)              
        result.status = code
        return result                                       

    def http_error_302(self, req, fp, code, msg, headers):   
        result = urllib2.HTTPRedirectHandler.http_error_302(
            self, req, fp, code, msg, headers)              
        result.status = code                                
        return result     

class WebMemo(object):
    """Caching web user agent with policy restrictions.

    Make sure we don't abuse any web sites;
    see http://www.w3.org/Help/abuse-info/re-reqs.html
    """
    def __init__(self, zones = None, DEBUG = False):
        """:param zone: URIs that don't start with this string
                        are prohibited by policy
        """
        self._memo = {}
        self._zones = zones
        self.DEBUG = DEBUG
        #set of gleaned Sources (prevent recursive gleaning)
        #see: http://www.w3.org/2001/sw/grddl-wg/td/grddl-tests#loop
        self.gleanQueue = set()

    def __call__(self, addr, types = None):
        """raises IOError iff addr outside zone(s)
        """
        if self._zones and not [ z for z in self._zones if addr.startswith(z) ]:
            raise IOError, "%s outside policy zone(s) %s" % (addr, self._zones)

        memo = self._memo
        url = addr
        try:
            m = memo[addr]
        except KeyError:
            req = urllib2.Request(addr)
            opener = urllib2.build_opener()
            if types:
                req.add_header('Accept', ','.join(types))
            if self.DEBUG:
                print >>sys.stderr, "@@fetching: ", addr, "with types", types
                
            ##From: http://www.diveintopython.org/http_web_services/redirects.html
            #points an 'opener' to the address to 'sniff' out final Location header
            opener = urllib2.build_opener(SmartRedirectHandler())
            f = opener.open(req)
            url = f.url
            if self.DEBUG:
                print >>sys.stderr, "@@HTTP Response Location header: ", url            
            m = f.read(), f.info()
            memo[addr] = m

        return url.encode('utf-8'), m

def usage():    
    print """USAGE: GRDDL.py [options] srcURL

Options:

  --zone=<uri-scheme:> (can be used multiple times)
  --test
  --help
  --debug
  --output-format=<'n3' or 'ntriples' or 'xml'>
  --ns=prefix=namespaceUri*
  --no-xi-filename=<filename>
"""
    
def main(argv):
    import os
    
    if argv is None: argv = sys.argv
    try:
        opts, args = getopt.getopt(argv[1:], "",
                                   ["help", "output-format=",
                                    "debug", "test",
                                    "zone=",
                                    "ns=", "no-xi-filename="])
    except getopt.GetoptError,e:
        print e
        usage()
        return 2
    output = 'xml'
    DEBUG=False    
    docTesting = False
    zones = ["file:"]
    nsBinds = {
        'rdf' : str(RDF.RDFNS),
        'rdfs': str(RDFS.RDFSNS),
        'owl' : "http://www.w3.org/2002/07/owl#",       
        'dc'  : "http://purl.org/dc/elements/1.1/",
        'foaf': "http://xmlns.com/foaf/0.1/",
        'wot' : "http://xmlns.com/wot/0.1/"        
    }
    noXIfilename = None
    for o, a in opts:
        if o == "--test":
            docTesting = True            
        elif o == "--ns":
            pref,nsUri = a.split('=')
            nsBinds[pref]=nsUri
        elif o == "--debug":
            DEBUG = True
        elif o == "--help":
            usage()
            return 0
        elif o == "--output-format":
            output = a
        elif o == "--zone":
            zones.append(a)
        elif o == "--no-xi-filename":
            noXIfilename = a
    if len(args) < 1:
        usage()
        return 2
    elif docTesting:
        test()
        return 2
    graph = Graph()
    namespace_manager = NamespaceManager(Graph())
    for prefix,uri in nsBinds.items():
        if DEBUG:
            print >>sys.stderr, "binding %s to %s"%(prefix,uri)
        namespace_manager.bind(prefix, uri, override=False)        
    graph.namespace_manager = namespace_manager
    addr = absolutize(argv[-1], "file://%s/" % os.getcwd())

    try:
        GRDDLAgent(addr, graph, WebMemo(zones,DEBUG),DEBUG=DEBUG)
    except IOError, e:
        print >>sys.stderr, str(e)
        return 2

    print graph.serialize(format=output)

    if noXIfilename is not None:
        graph = Graph()
        try:
            GRDDLAgent(addr, graph, WebMemo(zones), False,DEBUG = DEBUG)
        except IOError, e:
            print >>sys.stderr, str(e)
            return 2

        print >>sys.stderr, "Serializing noXInclude graph"
        graph.serialize(format=output, destination=noXIfilename)
    
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    main(sys.argv)
