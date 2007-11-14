#summary A Feature-rich WSGI-based SPARQL Service for RDFLib

= Introduction =

Triclops is a rich, WSGI-based SPARQL service with the following features:

  * Centralized configuration (thanks to Paste)
  * Fully compliant SPARQL protocol implementation
  * Trivial, open-ended web server deployment (thanks again to Paste)
  * Forms-based submission of SPARQL queries
  * Additional browsing capabilities
  ** _Clickable_ triple browsing
  ** Class extension browsing
  ** Class browsing
  
= Details =

Triclops is meant to facilitate use and maintenance of network-mounted RDF datasets by both humans and Semantic Web agents.  Use by humans is facilitated through support of common RDF query patterns such as identifying all classes in a triple store, browsing the class extension, and general triple browsing.

== Software Dependencies ==

The software dependencies may seem quite large but they afford a robust platform for supporting high-volume, concurrent access.  In addition, setuptools is used to manage the dependencies, so it should be enough to run:

{{{
python setup.py install
}}}

To handle the installation of the dependent packages.  The specific software dependencies are:

  * [http://4suite.org 4Suite]
  * [http://pythonpaste.org/ Paste] & [http://pythonpaste.org/script/ PasteScript]
  * [http://rdflib.net RDFLib] 
  * [http://beaker.groovie.org/ Beaker] 

== 4Suite / 4Suite-XML ==

Triclops can be configured to serve SPARQL query [http://www.w3.org/TR/rdf-sparql-XMLres/ results] with an XML processing instructions which instructs browsers to render the results using an XSLT stylesheet.
  
== Configuration ==

