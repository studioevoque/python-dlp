"""
This module defines the WSGI entry point for this application.
"""
from Server import *
from paste.deploy.config import ConfigMiddleware
from paste import httpexceptions
from paste.urlparser import StaticURLParser, make_static
from paste.recursive import RecursiveMiddleware
from paste.urlmap import URLMap
from paste.exceptions.errormiddleware import ErrorMiddleware
from beaker.middleware import CacheMiddleware
from rdflib import RDF, RDFS, OWL
from rdflib.OWL import OWLNS
from Ft.Lib.Uri import OsPathToUri

def complementExpansion(ontGraph):
    from FuXi.Syntax.InfixOWL import *
    from FuXi.Horn import ComplementExpansion        
    complementExpanded=[]
    for negativeClass in ontGraph.subjects(predicate=OWL_NS.complementOf):
        containingList = first(ontGraph.subjects(RDF.first,
                                                      negativeClass))
        prevLink = None
        while containingList:
            prevLink = containingList
            containingList = first(ontGraph.subjects(RDF.rest,
                                                          containingList))
        if prevLink:
            for s,p,o in ontGraph.triples_choices((None,
                                                [OWL_NS.intersectionOf,
                                                 OWL_NS.unionOf],
                                                 prevLink)):
                for ignorePred in complementExpanded:
                    if (s,ignorePred,None) in ontGraph: 
                        continue
                _class = Class(s)
                complementExpanded.append(s)
                print >>sys.stderr, "Added %s to complement expansion"%_class
    expandedClasses = set()
    for candidateClass in complementExpanded:
        if ComplementExpansion(Class(candidateClass)) is not None:
            expandedClasses.add(candidateClass)
    print >>sys.stderr, "Complement expanded classes: ", list(expandedClasses)
    return expandedClasses        

def setup_dry_config(global_conf,   
                     nsBindings, 
                     litProps, 
                     resProps, 
                     ontGraph, 
                     ruleSet, 
                     definingOntology, 
                     builtinTemplateGraph, 
                     defaultDerivedPreds):
    proxy = global_conf.get('sparql_proxy')
    for kvStr in global_conf.get('nsBindings').split('|'):
        key,val=kvStr.split('=')
        nsBindings[key]=val
        print "Added namespace binding: %s -> %s"%(key,val)
                
                
    dataStoreOWL = global_conf.get('datastore_owl')
    dataStoreOntGraph = Graph()
    if not proxy and global_conf.get('store') == 'MySQL' and dataStoreOWL:
        for dsOwl in dataStoreOWL.split(','):
            dataStoreOntGraph.parse(dsOwl)
        
        litProps.update(OWL.literalProperties)
        litProps.update(RDFS.literalProperties)
        resProps.update(RDFS.resourceProperties)
        
        for litProp,resProp in dataStoreOntGraph.query(OWL_PROPERTIES_QUERY,
                                                   initNs={u'owl':OWL_NS}):
            if litProp:
                litProps.add(litProp)
            if resProp:
                #Need to account for OWL Full, where datatype properties
                #can be IFPs
                if (resProp,
                    RDF.type,
                    OWL_NS.DatatypeProperty) not in dataStoreOntGraph:
                    resProps.add(resProp)
        print "Registered %s owl:DatatypeProperties"%len(litProps)         
        print "Registered %s owl:ObjectProperties"%len(resProps)
    
        if global_conf.get('topDownEntailment',False):
            from FuXi.DLP.DLNormalization import NormalFormReduction
            from FuXi.DLP import DisjunctiveNormalForm
            from FuXi.Horn.HornRules import HornFromDL, HornFromN3, Ruleset
            from FuXi.Syntax.InfixOWL import *
            from FuXi.Horn import DATALOG_SAFETY_STRICT
            from FuXi.Rete.Magic import IdentifyDerivedPredicates
            complementExpanded =[]
            _ruleSet = Ruleset()
            if global_conf.get('SkipComplementExpansion'):
                for kvStr in global_conf.get('SkipComplementExpansion').split('|') :
                    pref,uri=kvStr.split(':')
                    complementExpanded.append(URIRef(nsBindings[pref]+uri))
                                                        
            definingOntology = global_conf.get('entailment_owl')
            for ont in definingOntology.split(','):
                if os.path.exists(ont):
                    ontGraphPath = OsPathToUri(ont)
                else:
                    ontGraphPath = ont
                print >>sys.stderr, "Parsing Semantic Web root Graph.. ", ontGraphPath
                for owlImport in ontGraph.parse(ontGraphPath).objects(predicate=OWL_NS.imports):
                    ontGraph.parse(owlImport)
                    print >>sys.stderr, "Parsed Semantic Web Graph.. ", owlImport
            
            for prefix,uri in nsBindings.items():
                ontGraph.bind(prefix,uri)
            
            builtins = global_conf.get('builtins')
            if global_conf.get('entailment_n3'):
                #setup rules / builtins
                if builtins:
                    import imp
                    userFuncs = imp.load_source('builtins', builtins)
                    rs = HornFromN3(global_conf.get('entailment_n3'),
                                    additionalBuiltins=userFuncs.ADDITIONAL_FILTERS)
                else:
                    rs = HornFromN3(global_conf.get('entailment_n3'))
                print "Parsed %s rules from %s"%(len(rs.formulae),global_conf.get('entailment_n3'))
                _ruleSet.formulae.extend(rs)
                
            #Setup builtin template graph
            builtinTemplates   = global_conf.get('builtinTemplates',False)
            if builtinTemplates:
                builtinTemplateGraph.parse(builtinTemplates,format='n3')            
            #setup ddl graph
            ddlGraph = global_conf.get('ddlGraph')
            if ddlGraph:
                ddlGraph = Graph().parse(ddlGraph,
                                         format='n3')
                print "Registering DDL metadata"
                defaultDerivedPreds.extend(
                                            IdentifyDerivedPredicates(
                                                  ddlGraph,
                                                  ontGraph,
                                                  _ruleSet))     
            #Reduce the DL expressions to a normal form
            NormalFormReduction(ontGraph)
            #extract rules form normalized ontology graph
            dlp=HornFromDL(ontGraph,
                           derivedPreds=defaultDerivedPreds,
                           complSkip=complementExpansion(ontGraph))
            _ruleSet.formulae.extend(dlp)
            #normalize the ruleset 
            ruleSet.formulae.extend(set(DisjunctiveNormalForm(_ruleSet,safety=DATALOG_SAFETY_STRICT)))

def make_app(global_conf, **app_conf):
    if not 'nsBindings' in globals():
        global nsBindings, litProps, resProps, ontGraph, ruleSet, \
        definingOntology, builtinTemplateGraph, defaultDerivedPreds
        nsBindings    = {u'owl' :OWLNS,
                         u'rdf' :RDF.RDFNS,
                         u'rdfs':RDFS.RDFSNS}
        litProps = set()
        resProps = set()
        ontGraph = Graph()
        ruleSet = set()
        builtinTemplateGraph = Graph()
        definingOntology = Graph()
        defaultDerivedPreds = []
        setup_dry_config(global_conf,
                         nsBindings,
                         litProps,
                         resProps,
                         ontGraph,
                         ruleSet,
                         definingOntology,
                         builtinTemplateGraph,
                         defaultDerivedPreds)        
    # @@@ Core Application @@@
    app = WsgiApplication(global_conf, 
                          nsBindings, 
                          defaultDerivedPreds, 
                          litProps, 
                          resProps, 
                          definingOntology, 
                          ontGraph,
                          ruleSet,
                          builtinTemplateGraph)
    
    # @@@ Expose config variables to other plugins @@@
    app = ConfigMiddleware(app, {'app_conf':app_conf,
                                 'global_conf':global_conf})
    # @@@ Caching support from Beaker @@@
    app = CacheMiddleware(app, global_conf)
    # @@@ Change HTTPExceptions to HTTP responses @@@
    app = httpexceptions.make_middleware(app, global_conf)    
    
    global ticketLookup
    ticketLookup = {}
    return app

def make_form_manager(global_conf,**app_conf):
    global nsBindings, litProps, resProps, ontGraph, ruleSet,\
    definingOntology, builtinTemplateGraph, defaultDerivedPreds
    nsBindings    = {u'owl' :OWLNS,
                     u'rdf' :RDF.RDFNS,
                     u'rdfs':RDFS.RDFSNS}
    litProps = set()
    resProps = set()
    ontGraph = Graph()
    ruleSet = set()
    builtinTemplateGraph = Graph()
    definingOntology = Graph()
    defaultDerivedPreds = []
    setup_dry_config(global_conf,
        nsBindings,
        litProps,
        resProps,
        ontGraph,
        ruleSet,
        definingOntology,
        builtinTemplateGraph,
        defaultDerivedPreds)
    return FormManager(global_conf,
        nsBindings,
        defaultDerivedPreds,
        litProps,
        resProps,
        definingOntology,
        ontGraph,
        ruleSet,
        builtinTemplateGraph)

def make_query_manager(global_conf,**app_conf):
    global nsBindings, litProps, resProps, ontGraph, ruleSet, \
    definingOntology, builtinTemplateGraph, defaultDerivedPreds
    nsBindings    = {u'owl' :OWLNS,
                     u'rdf' :RDF.RDFNS,
                     u'rdfs':RDFS.RDFSNS}
    litProps = set()
    resProps = set()
    ontGraph = Graph()
    ruleSet = set()
    builtinTemplateGraph = Graph()
    definingOntology = Graph()
    defaultDerivedPreds = []    
    setup_dry_config(global_conf,
                     nsBindings,
                     litProps,
                     resProps,
                     ontGraph,
                     ruleSet,
                     definingOntology,
                     builtinTemplateGraph,
                     defaultDerivedPreds)                
    return QueryManager(global_conf, 
                        nsBindings, 
                        defaultDerivedPreds, 
                        litProps, 
                        resProps, 
                        definingOntology, 
                        ontGraph,
                        ruleSet,
                        builtinTemplateGraph)

def make_owlBrowser(global_conf, **app_conf):
    return JOWLBrowser(global_conf)

def make_process_manager(global_conf, **app_conf):
    return ProcessBrowser(global_conf)

def make_usher(global_conf, **app_conf):
    return Usher(global_conf)

def make_about(global_conf, **app_conf):
    return About(global_conf)

def make_browser(global_conf, **app_conf):
    if not 'nsBindings' in globals():
        global nsBindings, litProps, resProps, ontGraph, ruleSet, \
        definingOntology, builtinTemplateGraph, defaultDerivedPreds
        nsBindings    = {u'owl' :OWLNS,
                         u'rdf' :RDF.RDFNS,
                         u'rdfs':RDFS.RDFSNS}
        litProps = set()
        resProps = set()
        ontGraph = Graph()
        ruleSet = set()
        builtinTemplateGraph = Graph()
        definingOntology = Graph()
        defaultDerivedPreds = []    
        setup_dry_config(global_conf,
                         nsBindings,
                         litProps,
                         resProps,
                         ontGraph,
                         ruleSet,
                         definingOntology,
                         builtinTemplateGraph,
                         defaultDerivedPreds)                
    return Browser(global_conf,nsBindings)

def make_ticket_manager(global_conf, **app_conf):
    return TicketManager(global_conf)

def make_entailment_manager(global_conf, **app_conf):
    from FuXi.Horn.HornRules import HornFromDL, HornFromN3, Ruleset
    if not 'nsBindings' in globals():
        global nsBindings, litProps, resProps, ontGraph, ruleSet, \
        definingOntology, builtinTemplateGraph, defaultDerivedPreds
        nsBindings    = {u'owl' :OWLNS,
                         u'rdf' :RDF.RDFNS,
                         u'rdfs':RDFS.RDFSNS}
        litProps = set()
        resProps = set()
        ontGraph = Graph()
        ruleSet = set()
        builtinTemplateGraph = Graph()
        definingOntology = Graph()
        defaultDerivedPreds = []
        setup_dry_config(global_conf,
                         nsBindings,
                         litProps,
                         resProps,
                         ontGraph,
                         ruleSet,
                         definingOntology,
                         builtinTemplateGraph,
                         defaultDerivedPreds)        
    return EntailmentManager(global_conf,
                             nsBindings,
                             defaultDerivedPreds,
                             litProps,
                             resProps,
                             definingOntology,
                             ontGraph,
                             ruleSet,
                             builtinTemplateGraph)