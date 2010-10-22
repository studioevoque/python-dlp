#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
This module implements two mappings from the Relational Algebra assertions
made about SNOMED-CT concepts into the OWL/RDF abstract syntax

## Fully mapping ##

## Short normal form ##

[[[
There are two distinct normal forms that are of value when computing subsumption.
The long normal form is appropriate for a candidate expression because it explicitly states all
the attributes can be inferred from concepts referenced by the expression. This makes it
easier to test whether the candidate fulfils a set of predicate conditions.
The short normal form is more appropriate for predicate expressions. It enables more efficient
retrieval testing because there are fewer conditions to test. However, there is no loss of
specificity because any candidate that fulfils the conditions of the short normal form inevitably
fulfils the conditions of the long normal form.
4.4 Building long and short normal forms ]]

A form which when applied to a predicate expression allows effective computation of whether
a candidate expression is one of its subtypes

Supertype view 
(necessary, explicit Description Logic subsumption 
 - rdfs:subClassOf - assertions made about primitive (or 'natural' SNOMED-CT Classes)

Supertype view: Proximal Primitive Supertypes
� For fully-defined concepts compute the proximal primitives
� For primitive concepts treat the concept itself as the proximal primitive supertype.
.. Rationale: As for long form see 4.5.1.

Attribute view is the set of owl:equivalentClass and owl:intersectionOf assertions about fully-defined
SNOMED-CT concepts

Attribute view: Differential Defining Relationships (compared to supertype view)
� For primitive concepts there are no differential defining relationships because the
primitive concept is its own proximal primitive supertype. Therefore in predicate normal
form the attribute view is empty for primitive concept s.
� For fully-defined concepts the differential form only includes defining relationships , and
relationship groups , that are more specific than those present in the union of the
definitions of the primitive supertypes.
.. Rationale: Each element in the predicate specifies an additional test to be
applied to candidate expressions. However these additional tests are
superfluous because:
... The candidate expression cannot be subsumed by the predicate unless
every candidate primitive supertype is subsumed by at least one
predicate primitive supertype.
... If this condition is met, then all defining relationships or relationship
groups or the candidate primitive supertypes are inevitably also shared
by the candidate expression.

All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the <ORGANIZATION> nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""
import MySQLdb, glob, sys, getopt, time, re, os, itertools
from cStringIO import StringIO
from pprint import pprint
from MySQLdb.constants.CLIENT import *
from rdflib.util import first
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib import URIRef, store, plugin, Literal, RDF, RDFS
from rdflib.Namespace import Namespace
from rdflib.store import *
from FuXi.Syntax.InfixOWL import *
from FuXi.Rete.Util import selective_memoize
from RectorSegmentationAlgorithm import FMA as FMA_NS,SegmentOntology, OBO_OWL    
from AnatomyReification import *
from AnatomyLocusGraphs import FMARestrictionQuery, PClassTransitiveTraversal

def getConnection((user,passwd,db,port,host)):  
    db = MySQLdb.connect(user=user,
                         passwd=passwd,
                         db=db,
                         port=port,
                         host=host,
                         client_flag = LOCAL_FILES)
    return db

CREATE_TABLES=[\
"""
CREATE TABLE Concepts (
  ConceptId char(18) NOT NULL PRIMARY KEY,
  ConceptStatus SMALLINT NOT NULL,
  FullySpecifiedName TEXT NOT NULL,
  CTV3ID char(5) NOT NULL, 
  SNOMEDID TEXT NOT NULL,
  IsPrimitive SMALLINT NOT NULL
)""",\
"""
CREATE TABLE Text_Definitions (
  ConceptId char(18) NOT NULL PRIMARY KEY,
  SNOMEDID TEXT NOT NULL,  
  FullySpecifiedName TEXT NOT NULL,  
  Definition TEXT NOT NULL
)""",\
"""
CREATE TABLE Descriptions (
  DescriptionId char(18) NOT NULL PRIMARY KEY,
  DescriptionStatus SMALLINT NOT NULL,
  ConceptId char(18) NOT NULL,
  INDEX(ConceptId(10)),
  Term TEXT NOT NULL,
  InitialCapitalStatus enum('0','1') NOT NULL,
  DescriptionType SMALLINT NOT NULL,
  LanguageCode char(5) NOT NULL
)""",\
"""
CREATE TABLE Relationships (
  RelationshipId char(18) NOT NULL PRIMARY KEY,
  ConceptId1 char(18) NOT NULL,
  INDEX(ConceptId1(18)),
  RelationshipType char(18) NOT NULL,
  ConceptId2 char(18) NOT NULL,
  INDEX(ConceptId2(18)),
  CharacteristicType SMALLINT NOT NULL,
  Refinability SMALLINT NOT NULL,
  RelationshipGroup SMALLINT NOT NULL
)"""]

loadQuery="""LOAD DATA LOCAL INFILE '%s' IGNORE INTO TABLE %s IGNORE 1 LINES"""

tables=['Concepts','Descriptions','Relationships','Text_Definitions']

extractSQLOutgoing=\
"""
SELECT 
  subject.ConceptId, predicate.ConceptId, object.ConceptId, Relationships.RelationshipGroup
from 
    Relationships
inner join Concepts as subject on 
(Relationships.ConceptId1 = subject.ConceptId)
inner join Concepts as predicate on 
(Relationships.RelationshipType = predicate.ConceptId)
inner join Concepts as object on
(Relationships.ConceptId2 = object.ConceptId)
WHERE Relationships.CharacteristicType not in (1,2) and Relationships.ConceptId1 = '%s'
"""

extractSQLIncoming=\
"""
SELECT 
  subject.ConceptId, predicate.ConceptId, object.ConceptId, NULL as RelationshipGroup
from 
    Relationships
inner join Concepts as subject on 
(Relationships.ConceptId1 = subject.ConceptId)
inner join Concepts as predicate on 
(Relationships.RelationshipType = predicate.ConceptId)
inner join Concepts as object on
(Relationships.ConceptId2 = object.ConceptId)
WHERE Relationships.CharacteristicType not in (1,2) and Relationships.ConceptId2 = '%s'
"""

extractSQL2=\
"""
SELECT 
  ConceptStatus, Concepts.FullySpecifiedName, IsPrimitive,DescriptionStatus,Term,DescriptionType,LanguageCode,Text_Definitions.Definition
from 
    Concepts,Descriptions
left join Text_Definitions on
    Descriptions.ConceptId = Text_Definitions.ConceptId
WHERE Descriptions.ConceptId = Concepts.ConceptId and Concepts.ConceptId = %s
"""

extractSQL3=\
"""
SELECT 
  subject.ConceptId, predicate.ConceptId, object.ConceptId
from 
    Relationships
inner join Concepts as subject on 
(Relationships.ConceptId1 = subject.ConceptId)
inner join Concepts as predicate on 
(Relationships.RelationshipType = predicate.ConceptId)
inner join Concepts as object on
(Relationships.ConceptId2 = object.ConceptId)
WHERE Relationships.CharacteristicType not in (1,2) and Relationships.ConceptId2 = '%s'
"""

TAXON_SUFFIX=re.compile('(.*)(\(.*\))')
statusDict={
    0:'Unspecified',
    1:'Preferred',
    2:'Synonym',
    3:'Fully specified name',
}

DEFAULT_WIDTH = 1
MAP_NS=Namespace('http://code.google.com/p/python-dlp/wiki/ClinicalOntologyModules#')
MAP=ClassNamespaceFactory(MAP_NS)
BIOTOP=Namespace('http://purl.org/biotop/1.0/biotop.owl#')
SNOMEDCT=Namespace('tag:info@ihtsdo.org,2007-07-31:SNOMED-CT#')
RO=Namespace('http://purl.org/obo/owl/obo#')
SNOMED=ClassNamespaceFactory(SNOMEDCT)
CPRNS=Namespace("http://purl.org/cpr/0.9#")
CPR=ClassNamespaceFactory(CPRNS)
SNAP=ClassNamespaceFactory(URIRef("http://www.ifomis.org/bfo/1.1/snap#"))
SPAN=ClassNamespaceFactory(URIRef("http://www.ifomis.org/bfo/1.1/span#"))
BFO=ClassNamespaceFactory(URIRef("http://www.ifomis.org/bfo/1.1#"))
SKOS=Namespace('http://www.w3.org/2004/02/skos/core#')
PHENO=Namespace('http://bioontology.org/wiki/index.php/DallasWorkshop#')
SNOMED_ISA='116680003'
SNOMED_CONCEPT='138875005'
SNOMED_PART_OF='123005000'
SNOMED_IGNORE=[SNOMED_CONCEPT,'362981000']
FMA2 = Namespace('http://bioontology.org/projects/ontologies/fma/fmaOwlDlComponent_2_0#')

SITE_RELATIONSHIPS=[
    '363704007',
    '405813007',
    '405814001',
    '363698007',
]

extractedAnnotations = [SKOS.scopeNote,RDFS.label,RDFS.comment]

ANONYMIZE_DEFINED_CLASSES=False

conceptHash = {}

from cPickle import dumps, PicklingError # for memoize
class memoize(object):
    """Decorator that caches a function's return value each time it is called.
    If called later with the same arguments, the cached value is returned, and
    not re-evaluated. Slow for mutable types."""
    # Ideas from MemoizeMutable class of Recipe 52201 by Paul Moore and
    # from memoized decorator of http://wiki.python.org/moin/PythonDecoratorLibrary
    # For a version with timeout see Recipe 325905
    # For a self cleaning version see Recipe 440678
    # Weak references (a dict with weak values) can be used, like this:
    #   self._cache = weakref.WeakValueDictionary()
    #   but the keys of such dict can't be int
    def __init__(self, func, keyExtent=None):
        self.keyExtent = keyExtent
        self.func = func
        self._cache = {}
    def __call__(self, *args, **kwds):
        key = self.keyExtent and args[:self.keyExtent] or args
        if kwds:
            items = kwds.items()
            items.sort()
            key = key + tuple(items)
        try:
            if key in self._cache:
                return self._cache[key]
            self._cache[key] = result = self.func(*args, **kwds)
            return result
        except TypeError, e:
            try:
                dump = dumps(key)
            except PicklingError:
                return self.func(*args, **kwds)
            else:
                if dump in self._cache:
                    return self._cache[dump]
                self._cache[dump] = result = self.func(*args, **kwds)
                return result

def normalizeName(root,isClass=False):
    root=root.replace("'",'').replace('/',' ').replace(',',' ').replace('-',' ').replace('(',' ').replace(')',' ').replace(':',' ').replace('ü','').replace("<","LessThan").strip()
    if root.find(' ')+1:
        root = ''.join([i[0].upper()+i[1:] for i in root.split(' ') if i])
    if not isClass:
        root=root[0].lower()+root[1:]
    return SNOMEDCT[root.encode('utf-8')]

@selective_memoize([0])
def FMAJoin(concept,db):
    c=db.cursor()
    c.execute(SNOFMAJOIN%concept)
    rt=c.fetchall()

    c.execute(SNOFMAJOIN2%concept)
    rt2 = c.fetchall()
    
    c.close()
    return rt+rt2

@selective_memoize([0])
def extractConcept(concept,db):
    rt=conceptHash.get(concept)
    if rt:
        return rt
    c=db.cursor()
    c.execute(extractSQL2%concept)
    prefName=None
    for status,fullName,primitive,descrStatus,term,descTyp,lang,definition in c.fetchall():
        if descrStatus != 0:
            continue
        if status != 0:
            raise TypeError(concept)
        if descTyp==1:
            prefName=term
    c.close()
    try:
        root,taxon=TAXON_SUFFIX.match(fullName).groups()
        conceptHash[concept] = root,prefName,primitive,taxon[1:-1],definition
        return root,prefName,primitive,taxon[1:-1],definition
    except:
        print concept
        raise concept
        conceptHash[concept] = fullName,prefName,primitive,'',definition
        return fullName,prefName,primitive,'',definition

@selective_memoize([0])
def incomingTraversalAlt(concept,db):
    c=db.cursor()
    c.execute(extractSQL3%concept)
    rt=c.fetchall()
    c.close()
    return rt
                        
@selective_memoize([0,1,3])
def coreRelationshipTraversal(incoming,concept,db,excludePredicate=None):
    c=db.cursor()
    if incoming:
        q = excludePredicate and '%s and Relationships.ConceptId2 <> "%s"'%(
                                                        extractSQLIncoming%concept,
                                                        excludePredicate) or \
                                                        extractSQLIncoming%concept 
    else:
        q = excludePredicate and '%s and Relationships.ConceptId2 <> "%s"'%(
                                                        extractSQLOutgoing%concept,
                                                        excludePredicate) or \
                                                        extractSQLOutgoing%concept
    c.execute(q)
    rt=c.fetchall()
    c.close()
    return rt

def axisClosure(concept,
                db,
                root='root',
                incoming=False,
                traversalAxis=[SNOMED_PART_OF,SNOMED_ISA],
                recursive=True,
                verbose=False,
                yieldRecursionDepth=False,
                depth=0,
                primitiveTraversal=False,
                yieldIsPrimitive=False):
    """
    This is a helper function which calculates closures (transitive or otherwise) of
    SNOMED-CT predicates
    """
    if verbose:
        print >> sys.stdout, "\taxisClosure(%s,..,%s,%s,%s,%s)"%(concept,root,incoming,traversalAxis,recursive)
    rootName,prefName,primitive,taxon,definition=extractConcept(concept,db)
    if verbose:
        print >> sys.stdout, "\t\t%s"%prefName
    if yieldIsPrimitive and yieldRecursionDepth:
        yield concept,primitive, depth
    elif yieldIsPrimitive:
        yield concept,primitive
    else:
        yield concept
        
    if root == 'primitive' and primitive:
        if verbose:
            print >> sys.stdout,"\tTerminating at primitive"
        return
    else:
        rt=coreRelationshipTraversal(incoming,concept,db)
        for s,p,o,roleGroup in rt:#c.fetchall():
            if verbose:
                print >> sys.stdout,"\t%s %s %s"%(s,p == SNOMED_PART_OF and 'partOf' or 'subClassOf',o)
            if p in traversalAxis:
                if recursive:
                    if primitiveTraversal and not primitive:
                        #if we only want to count supertype traversal
                        #along primitive links and the current link
                        #is not primitive, don't increment 'link-hop' counter (used to find proximal primitive supertypes)
                        newDepth=depth
                    else:
                        newDepth=depth+1
                    for node in axisClosure(incoming and s or o,
                                            db,
                                            root,
                                            incoming,
                                            traversalAxis,
                                            verbose=verbose,
                                            depth=newDepth,
                                            primitiveTraversal=primitiveTraversal,
                                            yieldRecursionDepth=yieldRecursionDepth,
                                            yieldIsPrimitive=yieldIsPrimitive):
                        yield node   
                else:
                    if yieldIsPrimitive:
                        sPrim = extractConcept(s,db)[2]
                        oPrim = extractConcept(o,db)[2]
                        if incoming:
                            if yieldRecursionDepth:
                                yield s,sPrim,depth
                            else:
                                yield s,sPrim
                        elif yieldRecursionDepth:
                            yield o,oPrim,depth
                        else:
                            yield o,oPrim
                    else:
                        yield incoming and s or o

global skolemDict, sepTripleCount, processedMaps, restrictionMaps, fmaExtracts, keyAnatomy, keyAnatID, sepRuleFire
skolemDict      = {}
sepTripleCount  = {}
processedMaps   = {}
restrictionMaps = {}
sepRuleFire     = {}
keyAnatID       = set()
fmaExtracts     = set()
keyAnatomy      = set()

CLASHING_RESTRICTION_QUERY=\
"""
ASK
{
  ?restr a owl:Restriction;
         owl:onProperty ?onProp;
         ?restrictionKind ?CLASS .
}"""

def clashingRestriction(graph,restriction,onProp,restrKind,C):
    bindings={Variable('restr')          : restriction,
              Variable('onProp')         : onProp,
              Variable('restrictionKind'): restrKind,
              Variable('CLASS')          : C }
    rt=graph.query(CLASHING_RESTRICTION_QUERY,initBindings=bindings)
    return rt.askAnswer[0]

SNOFMAJOIN=\
"""
SELECT Concepts.ConceptId, fmaPreferredName, FMAURI, structure 
from Concepts, SNCT2FMA as map 
where map.ConceptId = Concepts.ConceptId and 
      Concepts.ConceptId = '%s'"""

SNOFMAJOIN2=\
"""
SELECT Concepts.ConceptId, fmaPreferredName, FMAURI, 'P' 
from Concepts, SNOMEDPARTS2FMA as map 
where map.ConceptId = Concepts.ConceptId and 
      Concepts.ConceptId = '%s'"""

ENTIRE_PATTERN = re.compile('Entire (.+)')

SEP_SUB_MATCH_SQL=\
"""
SELECT 
  Term,ConceptId
from 
    Descriptions
WHERE 
  DescriptionStatus = 1 AND
  Term REGEXP "%s"
"""

findFMAE4S_Query=\
"""
select EXISTS (
select map.fmaPreferredName, map.FMAURI
from 
    Relationships as isa    
left outer join SNCT2FMA as map on
     map.ConceptId = isa.ConceptId1 and
     map.structure = 'E' 
WHERE  isa.CharacteristicType not in (1,2) and
       isa.RelationshipType = '116680003' and 
       isa.ConceptId1 = '%s' and
       isa.ConceptId2 = '%s' )""" 

findSPForE=\
"""
SELECT 
  isa.ConceptId2 as SClassID, partOf.ConceptId1 as PClassID, pClassIsa.ConceptId2 as SForPClassID
from 
    Relationships as isa
left outer join Relationships as partOf on
(partOf.ConceptId2 = isa.ConceptId1 and
 partOf.RelationshipType = '123005000' )
left outer join Relationships as pClassIsa on 
(pClassIsa.ConceptId1 = partOf.ConceptId1 and
 pClassIsa.RelationshipType = '116680003' )
WHERE isa.CharacteristicType not in (1,2) and
      partOf.CharacteristicType not in (1,2) and
      pClassIsa.CharacteristicType not in (1,2) and
      isa.RelationshipType = '116680003' and 
      isa.ConceptId1 = '%s' 
"""

findSEForP=\
"""
SELECT 
  isa.ConceptId2 as SClassID, partOf.ConceptId2 as EClassID 
from 
    Relationships as isa
left outer join Relationships as partOf on
(partOf.ConceptId1 = isa.ConceptId1 and
 partOf.RelationshipType = '123005000' )
left outer join Relationships as pClassIsa on 
(pClassIsa.ConceptId1 = partOf.ConceptId2 and
 pClassIsa.RelationshipType = '116680003' )
WHERE isa.CharacteristicType not in (1,2) and
      partOf.CharacteristicType not in (1,2) and
      pClassIsa.CharacteristicType not in (1,2) and
      isa.RelationshipType = '116680003' and 
      isa.ConceptId1 = '%s' and
      (partOf.ConceptId1 = NULL or pClassIsa.ConceptId2 = isa.ConceptId2)
"""

findPEForS=\
"""
SELECT 
  isa.ConceptId1 as PClassID, 
  partOf.ConceptId2 as EClassID
from 
    Relationships as isa
left outer join 
(Relationships as partOf 
  inner join Relationships as isa2 on
     partOf.RelationshipType = '123005000' AND
     partOf.ConceptId1 = isa2.ConceptId1 AND
     isa2.ConceptId2 = '%s' AND
     isa2.RelationshipType = '116680003'
  inner join Relationships as isa3 on
     partOf.ConceptId2 = isa3.ConceptId1 AND
     isa3.ConceptId2 = '%s' AND
     isa3.RelationshipType = '116680003'
) on
  isa.ConceptId1 = partOf.ConceptId1

WHERE isa.CharacteristicType not in (1,2) and
      partOf.CharacteristicType not in (1,2) and
      isa2.CharacteristicType not in (1,2) and
      isa.RelationshipType = '116680003' and 
      isa.ConceptId2 = '%s'
"""

@selective_memoize([1,2])
def findFMAE4S(db,eClass,sClass):
    c=db.cursor()
    c.execute(findFMAE4S_Query%(eClass,sClass))
    return first(c.fetchall())

@selective_memoize([1,2,3])
def findClassInSEP(db,concept,tag,target):
    if target == 'S':
        if tag == 'E':
            c=db.cursor()
            c.execute(findSPForE%concept)
            rt=c.fetchall()
        else:
            c=db.cursor()
            c.execute(findSEForP%concept)
            rt=c.fetchall()
    else:
        assert tag == 'S'
        c=db.cursor()
        c.execute(findPEForS%(concept,concept,concept))
        rt=c.fetchall()
    return rt
    

def URIFromConcept(db,concept):
    try: 
        rootName,prefName,primitive,taxon,definition=extractConcept(concept,db)
    except:
        return
    try:
        return normalizeName(rootName,isClass=True)
    except UnicodeDecodeError:
        return 

def annotateTerm(targetGraph,term,taxon,concept,isAnatomy=False):
    targetGraph.add((term.identifier,SKOS.scopeNote,Literal(taxon)))
    targetGraph.add((term.identifier,SKOS.prefSymbol,Literal(concept)))
    term.isAnatomy = isAnatomy
    return term

def extractSNOMEDDef(targetGraph,
                     concept,
                     db,
                     width=DEFAULT_WIDTH,
                     options=None,
                     outBox=None,
                     targetConcept=False,
                     selectedConcept=False,
                     verbose=False,
                     normalForm=None,
                     targets=None):
    #Outbox is a list of concepts that have already been processed
    #It ensures that no concept is processed more than once
    outBox = outBox and outBox or set()
    if concept in outBox:
        return
    #rootName is the human-readable SNOMED-CT name for the concept
    #prefName is the preferred human-readable name
    #primitive is a boolean indicating whether or not the concept is a primitive
    #taxon is the name of the primary SNOMED-CT taxonomy this concept falls under
    try: 
        rootName,prefName,primitive,taxon,definition=extractConcept(concept,db)
    except:
        return
    #Sanitize the 'root name' and cast it into a URI
    try:
        normName=normalizeName(rootName,isClass=True)
    except UnicodeDecodeError:
        return 
    if verbose:
        print >> sys.stdout,concept,normName,prefName,definition and \
          '|%s|'%definition or '',primitive,width,outBox        
#    if not ANONYMIZE_DEFINED_CLASSES or targetConcept or primitive:

    #If we choose to not make anonymous classes out of non-primitive SNOMED
    #concepts, we are dealing with a chosen concept, or the concept
    #is primitive then we use the sanitized URI as the identifier of the
    #corresponding OWL Class
    term=Class(normName)
    #We set the preferred human-readable name as the rdf:label
    #and add a concept giving the SNOMED-CT code identifier
    term.label = Literal(prefName and prefName or rootName)
    
    if options.fma:
        rt=FMAJoin(concept,db)
        if rt and rt[0][2]:
            if term.identifier in restrictionMaps:
                return
            #Add an FMA term to extract and handle
            #SNOMED-CT anatomic 'structures' as binary disjunction of an 'entire' and its 'part'
            #Mark as equivalent with FMA class
            outBox.add(concept)
            sId,fmaName,fmaURI,structure=rt[0]
            fmaURI = URIRef(fmaURI)
            if concept in targets:
                keyAnatomy.add(term.identifier)
                fmaExtracts.add(fmaURI)
            fmaTerm = FMAAnatomyTerm(fmaURI,Literal(sanitizeFMAName(fmaName)))
            fmaExtracts.add(fmaTerm.identifier)
            
            #Mark for replacement in all references
            restrictionMaps.setdefault(term.identifier,set()).add(fmaTerm)            
            sepRuleFire.setdefault(term.identifier,{})['*.1']=fmaTerm.identifier
            if structure == 'S':
                sepTripleCount.setdefault('S',set()).add(term.identifier)
                rt=findClassInSEP(db,concept,'S',None)
                if rt:
                    for pClass,eClass in rt:
                        pClassTerm = \
                        extractSNOMEDDef(
                                 targetGraph,
                                 pClass,
                                 db,
                                 None,
                                 options=options,
                                 outBox=outBox,
                                 normalForm=normalForm,
                                 targets=targets)                    
                        eClassTerm = \
                        extractSNOMEDDef(
                                 targetGraph,
                                 eClass,
                                 db,
                                 None,
                                 options=options,
                                 outBox=outBox,
                                 normalForm=normalForm,
                                 targets=targets)
                    return annotateTerm(targetGraph,term,taxon,concept,isAnatomy=True)                    
            else:
                if structure == '*':
                    return annotateTerm(targetGraph,term,taxon,concept,isAnatomy=True)
                tag = structure
                if tag == 'P':
                    rt=findClassInSEP(db,concept,tag,'S')
                    if rt:
                        #(3.3)If Asct_s is the S-class in the Sep of Asct, Asct_e 
                        #is the E-class in the Sep of Asct,  and Asct_e was 
                        #mapped to Cfma in the FMA, then for every restriction 
                        #where Asct_s is the filler, replace with
                        #(Afma or Cfma)
                        sepTripleCount.setdefault('P',
                                                  set()).add(term.identifier)
                        success = False  
                        for sClass,eClass in rt:
                            if sClass and eClass:
                                success = True
                                rt=FMAJoin(eClass,db)
                                if rt:
                                    sId,eFmaName,eFmaURI,structure=rt[0]
                                    eFmaTerm = FMAAnatomyTerm(URIRef(eFmaURI),
                                                              Literal(sanitizeFMAName(eFmaName)))
                                    sClassURI = URIFromConcept(db,sClass)
                                    disjunct = LogicalAnatomyDisjunction([eFmaTerm,fmaTerm])
                                    restrictionMaps.setdefault(sClassURI,
                                                               set()).add(disjunct)#  fmaCl | eFmaCl)
                                    sepRuleFire.setdefault(sClassURI,{})['3.3']=(fmaTerm.identifier,eFmaURI)
                                    sepTripleCount.setdefault('S',set()).add(sClassURI)                                                    
                        if success:
                            return annotateTerm(targetGraph,term,taxon,concept,isAnatomy=True)
                else:
                    #An entire anatomical entity
                    rt = findClassInSEP(db,concept,tag,'S')
                    if rt:
                        #(1.2) If Asct_s is the S-class in the Sep of Asct, then 
                        #for every restriction where Asct_s is the filler, 
                        #replace with: (Afma or (partof some Afma)
                        #(1.3) If Asct_p is the P-class in the Sep of Asct, 
                        #then for every restriction where Asct_p is the filler, 
                        #replace w/: (partof some Afma)
                        sepTripleCount.setdefault('E',
                                                  set()).add(term.identifier)    
                        includeSNCTLinks = False
                        for sClass,pClass, sForP in rt:
                            if sForP == sClass:
                                #sClass has a full triplet 
                                sClassURI = URIFromConcept(db,sClass)
                                pClassURI = URIFromConcept(db,pClass)
                                disjunct = LogicalAnatomyDisjunction(
                                                 [fmaTerm,
                                                  SomePartOfAnatomy(fmaTerm)])
                                restrictionMaps.setdefault(sClassURI,
                                                           set()).add(disjunct)
                                sepRuleFire.setdefault(sClassURI,{})['1.2']=fmaTerm.identifier
                                sepTripleCount.setdefault('S',set()).add(sClassURI)
                                restrictionMaps.setdefault(pClassURI,
                                                          set()).add(SomePartOfAnatomy(fmaTerm))
                                sepRuleFire.setdefault(pClassURI,{})['1.3']=fmaTerm.identifier
                                sepTripleCount.setdefault('P',set()).add(pClassURI)
                                includeSNCTLinks = True
                            elif sClass in targets or sClass in keyAnatID:
                                includeSNCTLinks = True
                        if not includeSNCTLinks:
                            #If the replaced E-class is not part of a full SEP or
                            #or its S-class is not relevant to domain, replace
                            #with FMA term (losing SNOMED-CT definitions)
                            return annotateTerm(targetGraph,term,taxon,concept,isAnatomy=True)
                        else:
                            annotateTerm(targetGraph,term,taxon,concept,isAnatomy=True)
                            
#    if definition:
#        targetGraph.add((normName,RDFS.comment,Literal(definition)))
    primitiveText = primitive and ' (a primitive concept)' or ''
    if selectedConcept:
        term.comment = Literal("SNOMED-CT Code: "+primitiveText+concept+
                               '\nSelected for extraction')
    else:
        term.comment = Literal("SNOMED-CT Code: "+concept+primitiveText)
    #We add a skos:scopeNote statement identifying the concept with the
    #taxonomy
    annotateTerm(targetGraph,term,taxon,concept)
    rt=coreRelationshipTraversal(False,concept,db)    
    
    roleGrouping = {}
    
    if primitive:
        #Primitive SNOMED-CT 
        definingProperties={}
        upstreamAttributes=set()
        for s,p,o,roleGroup in rt:
            #<concept> <SNOMED-CT-RELATION> <otherConcept>
            #Add the concept to the list of those that have been processed already
            outBox.add(s)
            if p == SNOMED_ISA:
                if o in SNOMED_IGNORE:# or normalForm:
                    #Ignore isa relations with the top-level SNOMED-CT meta concept
                    continue
                if normalForm:
                    #Unlike the definition of short normal form in SNOMED-CT manual (where
                    #the supertype view of primitives are empty. 
                    #supertype view consists of proximal primitives
                    proxPrims={} 
                    for ancestor,ancIsPrim,depth \
                            in axisClosure(
                                    o,
                                    db,
                                    yieldRecursionDepth=True,
                                    traversalAxis=[SNOMED_ISA],
                                    primitiveTraversal=True,
                                    verbose=verbose,
                                    yieldIsPrimitive=True):
                        #We want to only work with the primitive superclasses (and selected classes)
                        if ( ancIsPrim and ancestor not in SNOMED_IGNORE and \
                                    ancestor not in proxPrims ) or\
                           ( ancestor in targets and ancestor not in proxPrims ):
                            if depth == 0 or ancestor in targets:
                                #proximal primitive
                                ancTerm=extractSNOMEDDef(targetGraph,
                                                         ancestor,
                                                         db,
                                                         None,
                                                         options=options,
                                                         outBox=outBox,
                                                         normalForm=normalForm,
                                                         targets=targets)
                                if ancTerm is None:
                                    ancInfo=extractConcept(ancestor,db)
                                    ancId=normalizeName(ancInfo[0],isClass=True)
                                    ancTerm = Class(ancId)
                                proxPrims[ancestor]=ancTerm
                                outBox.add(ancestor)
                                
                                #Save defining relationships of all primitive superclasses
                                stmts=coreRelationshipTraversal(False,ancestor,db,excludePredicate=SNOMED_ISA)
                                for s1,p1,o1,roleGroup1 in stmts:
                                    if p1 != SNOMED_ISA:
                                        upstreamAttributes.add((p1,o1))
                    if proxPrims:
                        term.subClassOf = proxPrims.values()
                else:
                    for ancestor in axisClosure(o,
                                                db,
                                                root=options.root,
                                                traversalAxis=[SNOMED_ISA],
                                                verbose=verbose):
                        #For each ancestor, attempt to extract it (forcibly
                        #continuing until the end of the upwards traversal)
                        extractSNOMEDDef(targetGraph,
                                         ancestor,
                                         db,
                                         None,
                                         options=options,
                                         outBox=outBox,
                                         normalForm=normalForm,
                                         targets=targets)
                        #ensure we don't process the ancestor twice
                        outBox.add(ancestor)
                    #Assert (in RDFS) that this term is a subclass of the other concept
                    assert OWL_NS.Restriction not in term.type
                    objRootName,prefName,oPrimitive,taxon,definition=extractConcept(o,db)
                    oId=normalizeName(objRootName,isClass=True)
                    #coin a URI or a new BNode identifier depending on if the other concept
                    #is primitive or if we are not anonymizing defined classes
                    obj = (oPrimitive or not ANONYMIZE_DEFINED_CLASSES) and Class(oId) or \
                          skolemDict.setdefault(oId,Class())                                
                    term.subClassOf = [obj]
            elif width is None or width > 0:
                #Defining attribute relationship
                #@todo: save to check for redundancies 
                #if we haven't terminiated our extraction algorithm, continue processing
                #the other concept
                #Decrement the width count to ensure we don't traverse too far along
                #the relation axix beyond the threshold
                objRootName,prefName,oPrimitive,taxon,definition=extractConcept(o,db)
                obId=normalizeName(objRootName,isClass=True)
                obj = (oPrimitive or not ANONYMIZE_DEFINED_CLASSES) and Class(obId) or \
                      skolemDict.setdefault(obId,Class())        
                      
                roleRestriction = Property(normalizeName(extractConcept(p,db)[0]))|some|obj
                #@todo: should check if property uri is already in outbox (see elsewhere)        
                definingProperties[(p,o)]=roleRestriction
                    
                if options.roleGroupAsPart and roleGroup != 0:
                    #Indicate (for later) that this role restriction is part of a group
                    roleGrouping.setdefault(roleGroup,set()).add(roleRestriction)
                       
        for (pId,oId),restr in definingProperties.items():
            if normalForm and (pId,oId) in upstreamAttributes:
#                For fully-defined concepts the differential form only includes defining relationships [...]
#                that are more specific than those present in the union of the
#                definitions of the primitive supertypes
                continue       
            if pId in SITE_RELATIONSHIPS and concept in targets:
                keyAnatID.add(oId)                
            filler=extractSNOMEDDef(targetGraph,
                             oId,
                             db,
                             width is not None and width-1 or None,
                             options=options,
                             outBox=outBox,
                             normalForm=normalForm,
                             targets=targets)
            if pId in SITE_RELATIONSHIPS and concept in targets and filler is not None:
                keyAnatomy.add(classOrIdentifier(filler))            
            outBox.add(oId)
            skipMembership=False
            restrClass           = restr.restrictionRange
            restrKind            = restr.restrictionType
            onProp               = propertyOrIdentifier(restr.onProperty)
            
            #If the term already subsumes a restriction
            #that accounts for the current one, we skip it
            for member in term.subClassOf:
                _id = member.identifier
                if clashingRestriction(targetGraph,
                                       _id,
                                       onProp,
                                       restrClass,
                                       restrKind): 
                    if options.roleGroupAsPart:
                        for groupNo,group in roleGrouping.items():
                            if restr in group:
                                import pdb;pdb.set_trace()
                                raise
                                #If we are converting role groups into parts
                                #then discard the clashing restriction from the group                                
                                #group.remove(restr)
                    skipMembership=True
            def memberOfSet(_set): return restr in _set
            if not skipMembership:
                if options.roleGroupAsPart and \
                    first(itertools.ifilter(memberOfSet,roleGrouping.values())):
                    #If the restriction is part of a role group, take care 
                    #of it later
                    pass
                else:
                    restr+=term                        
        for groups in roleGrouping.values():
            if len(groups) > 1:
                #Instead of Class: CONCEPT 
                #SubClassOf: (P1 some Oa1), (P2 some Ob1) 
                #(where Oa1 and Ob1 are of the same group)
                #write: 
                #Class: CONCEPT 
                #SubClassOf: (has_part some 
                #  ((P1 some Oa1) and (P2 some Ob1)))
                groupExpr = BooleanClass(members=groups)
                mereologicalGroup = Property(RO['has_part'])|some|groupExpr
                mereologicalGroup += term
            else:
                #If the role group has only member, it loses its relevance
                _restr = groups.pop()
                _restr += term
    else:
        #Defined class
        members=set()
        proxPrims = set()
        definingProperties={}
        upstreamAttributes=set()
        for s,p,o,roleGroup in rt:
            outBox.add(s)
            if p == SNOMED_ISA:
                if o in SNOMED_IGNORE:
                    continue
                if normalForm:
                    #Long or short normal form
                    for ancestor,ancIsPrim,depth \
                            in axisClosure(
                                    o,
                                    db,
                                    yieldRecursionDepth=True,
                                    traversalAxis=[SNOMED_ISA],
                                    primitiveTraversal=True,
                                    verbose=verbose,
                                    yieldIsPrimitive=True):
                        #We want to only work with the primitive superclasses
                        if ancIsPrim and ancestor != '138875005' and \
                                ancestor not in proxPrims:
                            #Save defining relationships of all primitive superclasses
                            stmts=coreRelationshipTraversal(False,ancestor,db,excludePredicate=SNOMED_ISA)
                            for s1,p1,o1,roleGroup1 in stmts:
                                if p1 != SNOMED_ISA:
                                    upstreamAttributes.add((p1,o1))
                            if depth == 0:
                                #proximal primitive
                                proxPrims.add(ancestor)
                else:
                    for ancestor in axisClosure(o,
                                                db,
                                                root=options.root,
                                                traversalAxis=[SNOMED_ISA],
                                                verbose=verbose):
                        extractSNOMEDDef(targetGraph,
                                         ancestor,
                                         db,
                                         None,
                                         options=options,
                                         outBox=outBox,
                                         normalForm=normalForm,
                                         targets=targets)
                        outBox.add(ancestor)
                    objRootName,prefName,oPrimitive,taxon,definition=\
                        extractConcept(o,db)
                    obId=normalizeName(objRootName,isClass=True)
                    obj = (oPrimitive or not ANONYMIZE_DEFINED_CLASSES) and \
                        Class(obId) or skolemDict.setdefault(obId,Class())                        
                    members.add(obj)
            else:
                #Defining attribute relationship
                objRootName,prefName,oPrimitive,taxon,definition=extractConcept(o,db)
                obId=normalizeName(objRootName,isClass=True)
                obj = (oPrimitive or not ANONYMIZE_DEFINED_CLASSES) and \
                    Class(obId) or skolemDict.setdefault(obId,Class())                
                roleRestriction = Property(normalizeName(extractConcept(p,db)[0]))|some|obj
                definingProperties[(p,o)]=roleRestriction
                if options.roleGroupAsPart and roleGroup != 0:
                    #Indicate (for later) that this role restriction is part of a group
                    roleGrouping.setdefault(roleGroup,set()).add(roleRestriction)
                    
        for (pId,oId),restr in definingProperties.items():
            if normalForm and (pId,oId) in upstreamAttributes:
#                For fully-defined concepts the differential form only includes defining relationships [...]
#                that are more specific than those present in the union of the
#                definitions of the primitive supertypes
                continue            
            members.add(restr)
            if pId in SITE_RELATIONSHIPS and concept in targets:
                keyAnatID.add(oId)
            filler=extractSNOMEDDef(targetGraph,
                             oId,
                             db,
                             width is not None and width-1 or None,
                             options=options,
                             outBox=outBox,
                             normalForm=normalForm,
                             targets=targets)
            if pId in SITE_RELATIONSHIPS and concept in targets and filler is not None:
                keyAnatomy.add(classOrIdentifier(filler))            
            outBox.add(oId)
        if normalForm:
            #Defined class in normal form only subsumes proximal primitive supertypes
            for proxPrim in proxPrims:
                memberTerm=extractSNOMEDDef(targetGraph,
                                            proxPrim,
                                            db,
                                            None,
                                            options=options,
                                            outBox=outBox,
                                            normalForm=normalForm,
                                            targets=targets)
                if memberTerm is None:
                    termInfo=extractConcept(proxPrim,db)
                    termId=normalizeName(termInfo[0],isClass=True)
                    memberTerm = (termInfo[2] or not ANONYMIZE_DEFINED_CLASSES) \
                        and Class(termId) or skolemDict.setdefault(termId,Class())
                else:
                    outBox.add(proxPrim)
                if verbose:
                    print >> sys.stdout, "\tProximal primitive: ", memberTerm                                
                members.add(memberTerm)
        if len(members) == 1:
            term.equivalentClass = [members.pop()]
        elif (term.identifier,OWL_NS.intersectionOf,None) in term.graph:
            #a conjunction
            conjunctiveCollection=BooleanClass(term.identifier)
            for member in [i for i in members if i.identifier not in conjunctiveCollection]:
                #New role restriction not in term conjunction
                skipMembership = False
                #Check if one of existing conjuncts already accounts for 
                #role restriction, skip it
                for entry in conjunctiveCollection:
                    if OWL_NS.Restriction in member.type:
                        assert isinstance(member,Restriction)
                        restrClass           = member.restrictionRange
                        restrKind            = member.restrictionType
                        onProp               = propertyOrIdentifier(member.onProperty)
                        if clashingRestriction(term.graph,
                                               entry,
                                               onProp,
                                               restrClass,
                                               restrKind):  
                           if options.roleGroupAsPart:
                               for groupNo,group in roleGrouping.items():
                                   if member in group:
                                       import pdb;pdb.set_trace()
                                       raise
                                       #If we are converting role groups into parts
                                       #then discard the clashing restriction from the group                                
                                       #group.remove(restr)                                                                                             
                           skipMembership=True
                    else:
                        assert isinstance(member,Class)
                        if classOrIdentifier(member) == entry:
                            skipMembership = True
                def memberOfSet(_set): return member in _set
                if not skipMembership:  
                    if options.roleGroupAsPart and \
                        first(itertools.ifilter(memberOfSet,roleGrouping.values())):
                        #If the restriction is part of a role group, take care 
                        #of it later
                        pass
                    else:
                        conjunctiveCollection += member
        elif first(term.equivalentClass):
            assert len(list(term.equivalentClass))==1
            otherClass=first(term.equivalentClass)
            term.graph.remove((term.identifier,OWL_NS.equivalentClass,None))
            members.add(otherClass)
            term=BooleanClass(identifier=term.identifier,members=members)
        else:         
            if options.roleGroupAsPart:
                for groups in roleGrouping.values():
                    if len(groups) > 1:
                        #Instead of Class: CONCEPT 
                        #SubClassOf: (P1 some Oa1), (P2 some Ob1) 
                        #(where Oa1 and Ob1 are of the same group)
                        #write: 
                        #Class: CONCEPT 
                        #SubClassOf: (has_part some 
                        #  ((P1 some Oa1) and (P2 some Ob1)))
                        groupExpr = BooleanClass(members=groups)
                        mereologicalGroup = Property(RO['has_part'])|some|groupExpr
                        #remove role group members from list of conjuncts
                        #and add mereological conjunct instead
                        for item in groups:
                            members.remove(item)
                        members.add(mereologicalGroup)
                    else:
                        #If the role group has only member, it loses its relevance
                        #We must ensure it will be a member of the conjunct
                        _restr = groups.pop()
                        assert _restr in members
            term=BooleanClass(identifier=term.identifier,members=members)
    #Incoming
    stmts=incomingTraversalAlt(concept,db)   
    for s,p,o in stmts:
        if options.fma and concept in keyAnatID and p == SNOMED_ISA and first(term.label)[-9:]=='structure':
            #Possibly the EClass of a structure, mapped to FMA
            rt=findFMAE4S(db,s,concept)
            if rt[0]:
                #S-E triplet, extract E-class
                t=extractSNOMEDDef(
                         targetGraph,
                         s,
                         db,
                         None,
                         options=options,
                         outBox=outBox,
                         normalForm=normalForm,
                         targets=targets)
                         
        elif p != SNOMED_ISA and width is not None and width>0:
            #Other incoming link, extract only if within
            #recursion
            extractSNOMEDDef(
                 targetGraph,
                 s,
                 db,
                 width-1,
                 options=options,
                 outBox=outBox,
                 normalForm=normalForm,
                 targets=targets)
    return term

createMapping="""
CREATE TABLE SNCT2FMA (
  ConceptId char(18) NOT NULL PRIMARY KEY,
  fmaPreferredName TEXT NOT NULL,
  FMAURI TEXT NOT NULL,
  structure enum('S','E','*') NOT NULL 
)"""

createMapping2="""
CREATE TABLE SNOMEDPARTS2FMA (
  ConceptId char(18) NOT NULL PRIMARY KEY,
  fmaPreferredName TEXT NOT NULL,
  FMAURI TEXT NOT NULL 
)"""

mappingTable='SNCT2FMA'

mappingPattern  = re.compile(r'^(\d+)\|([^\|]+)\|\|([^\|]+)\|*([^\|]*).*$')
mappingPattern2 = re.compile(r'^(\d+)\|([^\|]+)\|[^\|]+\|[^\|]+\|\|([^\|]+)\|.*$')

def mappingGenerator(fd,partOfMapping=False):
    if partOfMapping:
        for line in fd.readlines():
            line=line.strip()
            snoID=mappingPattern2.match(line).group(1)
            snoPrefTerm=mappingPattern2.match(line).group(2)
            fmaName=mappingPattern2.match(line).group(3)
            yield snoID,fmaName.strip()
    else:
        for line in fd.readlines():
            line=line.strip()
            snoID=mappingPattern.match(line).group(1)
            fmaName=mappingPattern.match(line).group(3)
            mappingAnnotation=mappingPattern.match(line).group(4)
            if mappingAnnotation:
                yield snoID,fmaName.strip(),\
                      mappingAnnotation=='StructureX' and 'S' or 'E'
            else:
                yield snoID,fmaName.strip(),'*' 
        
def sanitizeFMAName(name):
    return name.replace(' ','_')        
        
def loadMappingFromDictionary(db,mapDict,location):
    fd=open(os.path.join(location,'matchingTerms+fromGeneratedSyn.txt'))
    c=db.cursor()
    c.executemany(
      """INSERT IGNORE INTO SNOMED2FMA (ConceptId, fmaPreferredName, FMAURI, structure)
      VALUES (%s, %s, %s, %s)""",
      [ (snomedId,fmaName,fmaUri,structure)
            for snomedId,(fmaName,fmaUri,structure) in mapDict.items() ])

def loadPClassMapping(db,location):
    fd=open(os.path.join(location,'matchingTermsPClasses.txt'))
    c=db.cursor()
    c.execute("""SHOW tables""")
    rt = [i[0] for i in c.fetchall()]
    if 'SNOMEDPARTS2FMA' in rt:
        print "Droping table SNOMEDPARTS2FMA"
        c.execute("drop table SNOMEDPARTS2FMA")
    c.execute("SET AUTOCOMMIT=1")
    c.execute(createMapping2)
    
    store = plugin.get('MySQL',Store)('fma')
    rt=store.open('user=root,password=,host=localhost,db=fma',create=False)
    fmaGraph = Graph(store,FMA_NS)
    
    c.executemany(
      """INSERT IGNORE INTO SNOMEDPARTS2FMA (ConceptId, fmaPreferredName, FMAURI)
      VALUES (%s, %s, %s)""",
      [
       (snomedId,fmaName,first(fmaGraph.subjects(RDFS.label,Literal(fmaName))))
        for snomedId,fmaName in mappingGenerator(fd,partOfMapping=True) ])

    c.execute("SELECT * from SNOMEDPARTS2FMA;")
    print pprint(c.fetchall())
    print "Loaded SNOMED-CT -> FMA anatomical mapping into SNOMEDPARTS2FMA"
    db.close()
    
#    for snomedId,fmaName in mappingGenerator(fd,partOfMapping=True):
#        print snomedId,fmaName,first(fmaGraph.subjects(RDFS.label,Literal(fmaName)))
    
def loadMapping(db,location):
    fd=open(os.path.join(location,'matchingTerms+fromGeneratedSyn.txt'))
    c=db.cursor()
    c.execute("""SHOW tables""")
    rt = [i[0] for i in c.fetchall()]
    if mappingTable in rt:
        print "Droping table %s"%mappingTable
        c.execute("drop table %s"%mappingTable)
    c.close()
    c=db.cursor(MySQLdb.cursors.DictCursor)
    c.execute("SET AUTOCOMMIT=1")
    c.execute(createMapping)
    
    store = plugin.get('MySQL',Store)('fma')
    rt=store.open('user=root,password=,host=localhost,db=fma',create=False)#store._db = db
    fmaGraph = Graph(store,FMA_NS)
    assert len(fmaGraph)
#    for snomedId,fmaName in mappingGenerator(fd):
#        print snomedId,fmaName,first(fmaGraph.subjects(RDFS.label,Literal(fmaName)))
    c.executemany(
      """INSERT IGNORE INTO SNCT2FMA (ConceptId, fmaPreferredName, FMAURI, structure)
      VALUES (%s, %s, %s, %s)""",
      [
       (snomedId,fmaName,first(fmaGraph.subjects(RDFS.label,Literal(fmaName))),annotation)
        for snomedId,fmaName,annotation in mappingGenerator(fd) ])

    c.execute("SELECT * from SNCT2FMA;")
    print pprint(c.fetchall())
    print "Loaded SNOMED-CT -> FMA anatomical mapping into SNCT2FMA"
    db.close()

def load(db,locationPrefix,files):
    c=db.cursor()
    c.execute("""SHOW tables""")
    rt = c.fetchall()
    for table in tables:
        if (table,) in rt:
            print "Droping table %s"%table
            c.execute("drop table %s"%table)
    c.close()
    c=db.cursor(MySQLdb.cursors.DictCursor)
    c.execute("SET AUTOCOMMIT=1")
    
    for createExpr in CREATE_TABLES:
        #print createExpr
        c.execute(createExpr)
    c.close()
    for idx,table in enumerate(tables):
        c=db.cursor()#MySQLdb.cursors.DictCursor)
        c.execute("SET AUTOCOMMIT=1")
        try:
            if files:
                fn=files[idx]
            else:
                fn='sct_%s_20070731.txt'%table.lower()
        except IndexError:
            continue
        fn=os.path.join(locationPrefix,fn)
        loadExpr=loadQuery%(fn,table)
        print "Loading ", table
        print "Executing:\n", loadQuery%(fn,table)
        c.execute(loadExpr)
        print "Result: ", c.fetchall()
        c.close()
        
FMA_ANNOTATION_SEARCH1=\
"""
SELECT ?class ?label 
{ 
  ?class rdfs:label ?label 
  FILTER(regex(?label, "%s") && isIRI(?class))  
}
"""        

FMA_ANNOTATION_SEARCH2=\
"""
PREFIX obo: <http://www.geneontology.org/formats/oboInOwl#>
SELECT ?class ?label 
{ 
  ?class obo:hasExactSynonym 
       [ a obo:Synonym ;
         rdfs:label ?label ] 
  FILTER(regex(?label, "%s") && isIRI(?class))         
}"""        

SNOMED_SITES_2_REPLACE=\
"""
SELECT ?restr
{ 
  ?restr a owl:Restriction; 
         owl:onProperty ?prop;
         owl:someValuesFrom ?term
  FILTER(
      ?prop = sno:findingSite         ||
      ?prop = sno:procedureSite       ||
      ?prop = sno:procedureSiteDirect 
  ) 
}"""

SNOMED_SITES_QUERY=\
"""
SELECT ?term 
{ 
  [] a owl:Restriction; 
     owl:onProperty ?prop ;
     owl:someValuesFrom ?term
  FILTER(
      ?prop = sno:findingSite ||
      ?prop = sno:procedureSite ||
      ?prop = sno:procedureSiteDirect 
  ) 
}"""

SNOMED_SITESBY_PART=\
"""
SELECT ?term 
{ 
  [] a owl:Restriction; 
     owl:onProperty sno:partOf; 
     owl:someValuesFrom ?term 
}"""

DANGLING_FMA_TERMS=\
"""
SELECT ?cl 
{ 
  ?cl a owl:Class
  FILTER(REGEX(?cl,"%s")) 
  OPTIONAL { ?other ?p ?cl  } 
  FILTER(!BOUND(?other))  
}
"""

DANGLING_CLASS=\
"""
SELECT ?restr 
{ 
  ?restr a ?kind
  FILTER(?kind = owl:Restriction || ?kind = owl:Class) 
  OPTIONAL { ?other ?p ?restr  } 
  FILTER(!BOUND(?other))  
}"""

DANGLING_QUERY=\
"""
SELECT ?dangler 
{ 
  [] rdfs:subClassOf ?dangler . 
  ?dangler a owl:Class .
  OPTIONAL { 
      ?dangler1 a owl:Restriction
      FILTER(?dangler = ?dangler1 && 
             isBlank(?dangler1)) 
  }
  FILTER(!bound(?dangler1)) 
}"""

SITES_QUERIES=[ SNOMED_SITES_QUERY,SNOMED_SITESBY_PART ]

ID_COMMENT_PATTERN=re.compile('SNOMED-CT Code: (\d+).*$')

def findFMATerms(individual):
    if isinstance(individual,BooleanClass):
        toDel = []
        for member in individual:
            try:
                member = CastClass(member,individual.graph)
                for term in findFMATerms(member):
                    yield term
            except MalformedClass:
                toDel.append(member)
        for item in toDel:
            idx = individual.index(item)
            del individual[idx]
    elif isinstance(individual,Restriction):
        for term in findFMATerms(individual.someValuesFrom):
            yield term
    elif individual is not None and individual.identifier.find(FMA_NS)+1:
        yield individual

def extract(output,db,options,concepts=[],verbose=False,normalForm=None):
    namespace_manager = NamespaceManager(Graph())
    namespace_manager.bind('owl', OWL_NS, override=False)
    namespace_manager.bind('rdf', RDF.RDFNS, override=False)
    namespace_manager.bind('rdfs', RDFS.RDFSNS, override=False)
    namespace_manager.bind('skos', SKOS, override=False)
    namespace_manager.bind('snomed',SNOMEDCT)
    g = Graph()
    g.namespace_manager = namespace_manager
    Individual.factoryGraph = g
    conceptObjs=set()   
    Property(SKOS.definition,baseType=OWL_NS.AnnotationProperty)
    Property(SKOS.scopeNote,baseType=OWL_NS.AnnotationProperty)
    for code in set(concepts):
        rt=extractSNOMEDDef(g,
                         code,
                         db,
                         options=options,
                         targetConcept=True,
                         selectedConcept=True,
                         verbose=verbose,
                         normalForm=normalForm,
                         targets=set(concepts))
        if rt is not None:
            if not hasattr(rt,'isAnatomy') or \
               not rt.isAnatomy or \
               first(g.objects(rt.identifier,
                               SKOS.prefSymbol)) in concepts:
                #Either not anatomy, or anatomy and selected for extraction
                conceptObjs.add(rt)
                
    if output:
        mapTerms=MAP['SNOMED-term']
        snctAloneFName=options.output.split('.')[0]+'-snomed.owl'            
        f=open(snctAloneFName,'w')
        f.write(g.serialize(format='pretty-xml'))
        f.close()
        
        if options.fma:
            ont=Ontology(comment=Literal('Mapping from SNOMED-CT extraction to FMA segment'))
            sNo = len(sepTripleCount.get('S',[]))
            eNo = len(sepTripleCount.get('E',[]))
            pNo = len(sepTripleCount.get('P',[]))
            total = sNo + eNo + pNo
            sPercent = total > 0 and (float(sNo * 100) / float(total)) or 0
            ePercent = total > 0 and (float(eNo * 100) / float(total)) or 0
            pPercent = total > 0 and (float(pNo * 100) / float(total)) or 0
            print >> sys.stderr, "FMA mapping statistics .."
            print >> sys.stderr, "Total number of anatomy mappings: ..", total
            print >> sys.stderr, "'Structure' mappings: %s (%s percent)"%\
                (sNo,sPercent)
            print >> sys.stderr, "'Entire' mappings: %s (%s percent)"%\
                (eNo,ePercent)
            print >> sys.stderr, "'Part' mappings: %s (%s percent)"%\
                (pNo,pPercent)
            ont.comment = [Literal("There were %s SNOMED-CT -> FMA mappings %s of which were for structures, %s were for parts, and %s of which were for entire anatomic entities"%\
                                   (total,sNo,pNo,eNo))]
        else:
            ont=Ontology(comment=Literal('SNOMED-CT extraction'))
        if options.fma:
            fmaToKeep = set()
            store = plugin.get('MySQL',Store)('fma')
            store.open('user=root,password=,host=localhost,db=fma',create=False)
            origFMAGraph = Graph(store,URIRef(FMA_NS))
            
            axiomReplacementGraph = Graph()
            axiomAnnotationNs = Namespace('tag:cut@case.edu,2010:AxiomAnnotation#')
            axiomReplacementGraph.bind('axiom',axiomAnnotationNs)
            axiomReplacementGraph.bind('sno',SNOMEDCT)
            axiomReplacementGraph.bind('skos',SKOS)
            axiomReplacementGraph.bind('ro',RO)
            axiomReplacementGraph.bind('fma',FMA_NS)
            ruleFired = Property(axiomAnnotationNs.ruleFired,
                                 graph=axiomReplacementGraph)
            newTerm = Property(axiomAnnotationNs.newTerm,
                               graph=axiomReplacementGraph)
                                 
            axiomReplaced = Property(axiomAnnotationNs.axiomReplaced,
                                     graph=axiomReplacementGraph)
            
            fmaName=options.output.split('.')[0]+'-anatomy.owl'            
            #First identify and cleanup SNOMED -> FMA mappings:
            for old,newTerms in restrictionMaps.items():
                replacement = None
                members = set()
                for term in newTerms:
                    if old in keyAnatomy:
                        #Extract all referenced FMA terms, making sure
                        #to get all has_part restrictions that
                        #refer to a SomePartOfAnatomy instance
                        for fmaTerm in DepthFirstTraversal(term):
#                            for ancestor in fmaTerm.CircumTranverse(origFMAGraph):
                            if isinstance(fmaTerm,SomePartOfAnatomy):
                                #We want to also extracts things asserted
                                #as having the term as a part via has_part
                                #(which will not otherwise be picked up by the 
                                #segmenetation algorithm
                                uri=fmaTerm.term.identifier
                                for _term in PClassTransitiveTraversal(uri,origFMAGraph):
                                    if not [cls for cls in 
                                            Class(uri,
                                                  graph=origFMAGraph).subClassOf
                                              if OWL_NS.Restriction in cls.type and \
                                              (cls.identifier,
                                               OWL_NS.onProperty,
                                               RO['part_of']) in origFMAGraph and \
                                              (cls.identifier,
                                               OWL_NS.someValuesFrom,
                                               _term) in origFMAGraph]:
                                        #Adds only if not redundant amongst outgoing links
                                        fmaToKeep.add(_term)
                                        fmaExtracts.add(_term)                    
                    replClass = term.makeClass(g)
                    members.add(replClass)
                    #For all SNOMED-CT anatomy class that map, they are replaced
                    #by their FMA counterpart
                    for rule, terms in sepRuleFire[old].items():
                        if rule =='*.1':
                            if axiomReplacementGraph.query(
                                "ASK { ?old axiom:ruleFired [ skos:editorialNote ?rule; axiom:newTerm ( ?newTerm )]  }",
                                initNs={u'axiom':axiomAnnotationNs,
                                        u'skos' :SKOS},
                                initBindings={Variable('old'):old,
                                              Variable('rule'):Literal(rule),
                                              Variable('newTerm'):terms}).askAnswer[0]:
                                continue
                            lst = Collection(ruleFired.graph,BNode(),seq=[terms])                            
                            replacementMD = AnnotatibleTerms(BNode(),graph=ruleFired.graph)
                            newTerm.extent=[(replacementMD.identifier,lst.uri)]
                            
                        elif rule =='3.3':
                            sTerm,eTerm = terms
                            if axiomReplacementGraph.query(
                                "ASK { ?old axiom:ruleFired [ skos:editorialNote '3.3'; axiom:newTerm ( ?newTerm1 ?newTerm2 )]  }",
                                initNs={u'axiom':axiomAnnotationNs,
                                        u'skos' :SKOS},
                                initBindings={Variable('old'):old,
                                              Variable('newTerm1'):sTerm,
                                              Variable('newTerm2'):eTerm}).askAnswer[0]:
                                continue                            
                            sTerm = Class(sTerm,graph=ruleFired.graph)
                            eTerm = Class(eTerm,graph=ruleFired.graph)
                            lst = Collection(ruleFired.graph,
                                             BNode(),
                                             seq=[sTerm.identifier,
                                                  eTerm.identifier])
                            replacementMD = AnnotatibleTerms(BNode(),graph=ruleFired.graph)  
                            newTerm.extent=[(replacementMD.identifier,lst.uri)]                          

                        elif rule in ('1.2','1.3'):
                            if axiomReplacementGraph.query(
                                "ASK { ?old axiom:ruleFired [ skos:editorialNote ?rule; axiom:newTerm ( ?newTerm )]  }",
                                initNs={u'axiom':axiomAnnotationNs,
                                        u'skos' :SKOS},
                                initBindings={Variable('old'):old,
                                              Variable('rule'):Literal(rule),
                                              Variable('newTerm'):terms}).askAnswer[0]:
                                continue                            
                            lst = Collection(ruleFired.graph,BNode(),seq=[terms])                            
                            replacementMD = AnnotatibleTerms(BNode(),graph=ruleFired.graph)
                            newTerm.extent=[(replacementMD.identifier,lst.uri)]

                        label = replClass.__repr__()
                        # print label, Literal(rule), replacementMD.identifier
                        
                        axiomReplacementGraph.add((replacementMD.identifier,
                                                   SKOS.editorialNote,
                                                   Literal(rule))) 
                        axiomReplacementGraph.add((replacementMD.identifier,
                                                   SKOS.definition,
                                                   Literal(label))) 
                            
                        ruleFired.extent = [(old,replacementMD.identifier)]
                        # axiomReplaced.extent = [(old,replClass.identifier)]
                        
                    #Class(old).serialize(axiomReplacementGraph)
                    Class(old,graph=axiomReplacementGraph)
                    # replClass.serialize(axiomReplacementGraph)
                    
                for item in members:
                    for fmaTerm in findFMATerms(item):
                        fmaExtracts.add(fmaTerm.identifier)
                        
                if len(members)>1:
                    replacement = BooleanClass(
                                   operator=OWL_NS.unionOf,
                                   members=members)
                elif not replacement:
                    replacement = members.pop()
                _cls = Class(old)
                
                replIdentifier = replacement.identifier
                if isinstance(replacement,BooleanClass):
                    pass
                    # for fillerReference in g.query("SELECT ?RESTR { ?RESTR owl:someValuesFrom ?CLS  }",
                    #                                 initBindings={Variable('CLS'):old}):
                    #         ind=Individual(fillerReference)
                    #         ind.identifier = replacement.identifier
                else:
                    oldId=_cls.identifier
                    newId=replacement.identifier
                    _cls.identifier = newId
                    fmaToKeep.add(newId)
                    #replace all relations to the candidate w/ the FMA term
                    # import warnings
                    # warnings.warn("Replacing %s with %s"%(oldId,newId))            
                    #remove all statements about SNOMED candidate term

                restrictionsToReplace = [ fillerRestriction
                    for fillerRestriction in \
                         g.query(SNOMED_SITES_2_REPLACE,
                                 initNs={u'sno': SNOMEDCT},
                                 initBindings={Variable('term') : old}) ]
                for restr in restrictionsToReplace:
                    g.remove((restr,OWL_NS.someValuesFrom,None))
                for restr in restrictionsToReplace:
                    g.add((restr,OWL_NS.someValuesFrom,replIdentifier))

                if _cls in conceptObjs:
                    mapTerms += replacement
                    conceptObjs.remove(Class(old))
            
            axiomMetaDataFName=options.output.split('.')[0]+'-axioms.owl'            
            f=open(axiomMetaDataFName,'w')
            f.write(axiomReplacementGraph.serialize(format='pretty-xml'))
            f.close()
            
            fmaTerms=MAP['FMA-term']
            for fmaTerm in fmaExtracts:
                fmaTerms += Class(fmaTerm)
                                                                                
            ont.imports = [URIRef(fmaName)]
            f=open(fmaName,'w')
            #Prior to extracting to FMA, ensure we aren't extracting terms
            #that aren't referenced or needed in the SNOMED-CT module    
            toDo = []
            for danglingFMA in g.query(DANGLING_FMA_TERMS%FMA_NS):
                if danglingFMA not in fmaToKeep and \
                    Class(danglingFMA,
                         skipOWLClassMembership=True) not in conceptObjs:#(danglingFMA,RDFS.subClassOf,mapTerms.identifier) not in g:
                    print >> sys.stderr, "Dangling FMA term ", danglingFMA
                    toDo.append(danglingFMA)
                    fmaExtracts.discard(danglingFMA)
            for danglingFMA in toDo:
                g.remove((danglingFMA,None,None))   
            print len(fmaExtracts), " selected FMA terms"         

        for sct_term in conceptObjs:
            mapTerms += sct_term
        for cl in fmaExtracts:
            if (None,None,cl) not in g:
                print >> sys.stderr, "dangling FMA class", cl
        print "%s FMA classes"%(len([cls 
                         for cls in g.subjects(RDF.type,OWL_NS.Class)
                            if cls.find(FMA_NS)+1]))
                    
        f=open(output,'w')
        f.write(g.serialize(format='pretty-xml'))
    else:
        for restr in g.subjects(RDF.type,OWL_NS.Restriction):
            if (None,None,restr) not in g:
                g.remove((restr,None,None))
            else:
                assert (restr,RDFS.subClassOf,None) not in g
        
        print g.serialize(format='pretty-xml')
        
def proximalPrimitives(owlGraph,definedClass):
    for member in BooleanClass(definedClass,graph=owlGraph):
        if isinstance(m,URIRef):
            if not Class(member,graph=owlGraph).isPrimitive(): 
                for proxPrim in proximalPrimitives(owlGraph,member):
                    yield proxPrim
            else:
                yield CastClass(member,owlGraph)
        
def subsumptionTraversal(node,g):
    for s in Class(node,graph=g).subClassOf:
       yield s.identifier
        
def subsumptionTransplant(traverseGraph,
                          deletionGraph,
                          term,
                          replacementGraph=[],
                          newRootGraph=None,
                          oldRootGraph=None,
                          equivalent=None,
                          parent=None):
    terms=[Individual(t,deletionGraph) 
           for t in traverseGraph.transitiveClosure(subsumptionTraversal,
                                                    term)]
    for t in terms:
        t.delete()
    if equivalent:
        for graph in replacementGraph:
            Individual(term,graph).replace(equivalent)
    elif parent:
        term=Class(term,graph=newRootGraph)
#        print "Before, ", term.__repr__(True)
        del term.subClassOf
        term.subClassOf = [parent]
#        print "After, ", term.__repr__(True)
        
        #del (Class(term,graph=oldRootGraph)).subClassOf

definedTerms="SELECT Def.ConceptId,Def.Definition from Text_Definitions Def ;"

def extractSNOMEDCore(db,options):
    c=db.cursor()
    c.execute(definedTerms)
    extract(options.output,
            db, 
            options,   
            (_id for _id,_def in c.fetchall()),
            verbose=options.verbose,
            normalForm=options.normalForm)    
    c.close()
    
def main():    
    from optparse import OptionParser
    parser = OptionParser()

    parser.add_option('--root',type="choice",default='root',
      choices=['primitive','root'],
      help='Determines the termination point for the extraction algorithm '+\
           '(either stop at the closest primitive concept going upwards or at '+\
           'the very top of the SNOMED taxonomy).  Respectively the value of '+\
           'this option can be one of "primitive" or "root" (the default)')
    
    parser.add_option('--load',action="store_true",
      help='Load SNOMED-CT distribution files (in the current directory) into a MySQL DB')

    parser.add_option('--loadFMAMapping',action="store_true",
      help='Load the SNOMED-CT -> FMA mapping into a database',
      default=False)

    parser.add_option('--loadFMAPClassMapping',action="store_true",
      help='Load the P-Class SNOMED-CT -> FMA mapping into a database',
      default=False)

    parser.add_option('--align',
      help='Indicate whether to clean up and align the ontology with the CPR ontology located at the given path')

    parser.add_option('--fma',action='store_true',default=False,
      help='Indicate which anaotmical SNOMED-CT terms to correlate with FMA')

    parser.add_option('--verbose',action="store_true",default=False,
        help='Output debug print statements or not')

    parser.add_option('-e','--extract',
      help='Extract an OWL representation from SNOMED-CT using the '+\
           'comma-separated list of SNOMED-CT identifiers as the starting point')

    parser.add_option('-r','--roleGroupAsPart',action='store_true',default=False,
      help='Convert role groups into mereological component (via ro:has_part)')

    parser.add_option('--snomedCore',action='store_true',default=False,
      help='Extract an OWL representation from SNOMED-CT using the '+\
           'concepts with human readable definitions as the starting point')

    parser.add_option('--extractFile',
      help='Same as --extract, except the comma-separated list of SNOMED-CT identifiers are in the specified file')

    parser.add_option('-o', '--output', default=None,
      help='The name of the file to write out the OWL/RDF to (STDOUT is used otherwise')

    parser.add_option('-n', '--normalForm', default=None,
      help='Whether to extract using the long normal form (long), short normal form (short), or neither (- the default -)')

    parser.add_option('-l', '--location', default='./',
      help='The directory where the delimited files or SNOMED-CT -> FMA mappings will be loaded from (the '+\
           'default is the current directory)')
        
    parser.add_option('-s', '--server', default='localhost',
      help='Host name of the MySQL database to connect to')

    parser.add_option('-f', '--files', default=None,
      help='A comma-separated list of distribution files to load from '+
      'in the order: concept, descriptions, relationship, definition')

    parser.add_option('-p', '--port', default='3306',type='int',
      help='The port to use when connecting to the MySQL database')

    parser.add_option('-w', '--password',help='Password')
    
    parser.add_option('-u', '--username',
      help='User name to use when connecting to the MySQL database')    
    
    parser.add_option('-d', '--database',
      help='The name of the MySQL database to connect to')
    
    parser.add_option('--profile',action='store_true',help='Enable profiling statistics')
        
    (options, args) = parser.parse_args()
    
    if not (options.database or options.username):
        print "The database (--database) and username (--username) must be provided "+\
              "in order to connect to MySQL"
        sys.exit(1)  
    if options.extractFile and options.extract:
        print "Either --extractFile or --extract can be specified, not both"  
        sys.exit(1)
        
    if True:#options.password:
        password=options.password
    else:
        import getpass
        password = getpass.getpass("Enter the MySQL password (%s): "%options.username)

    try:
        db=getConnection((options.username,
                          password,
                          options.database,
                          int(options.port),
                          options.server))
    except:
        error = StringIO()
        import traceback; traceback.print_stack(file=error); traceback.print_exc(file=error)
        print "Unable to connect to the MySQL database using the given credentials:"
        print error.getvalue()
        sys.exit(1)    
        
    if options.load:
        print options.location
        load(db,
             options.location,
             options.files is not None and options.files.split(','))
    elif options.loadFMAMapping:
        loadMapping(db,options.location)
    elif options.loadFMAPClassMapping:
        loadPClassMapping(db,options.location)
    elif options.snomedCore:
        extractSNOMEDCore(db,options)
    elif options.extract or options.extractFile:
        if options.extract:
            concepts = [i.strip() for i in options.extract.split(',')]
        else:
            splitChar = open(options.extractFile).read().find(',')+1 and ',' or '\n'
            concepts = [i.strip() for i in 
                            open(options.extractFile).read().strip().split(splitChar)]
        assert len(concepts)
        if options.verbose:
            print >> sys.stdout,"Killing upwards traversal at ", options.root
        assert options.normalForm in [None,'short','long'],"--normalForm must be either 'short' or 'long'"
        
        if options.profile:
            import hotshot, hotshot.stats
            prof = hotshot.Profile("snomed.prof")
            res = prof.runcall(extract,
                               options.output,
                               db, 
                               options,   
                               concepts,
                               verbose=options.verbose,
                               normalForm=options.normalForm)
            prof.close()
            stats = hotshot.stats.load("snomed.prof")
            stats.strip_dirs()
            stats.sort_stats('time','cumulative','pcalls')
            stats.print_stats(.1)
            stats.print_callers(.05)
            print "==="*20            
            stats.print_callees(.05)
        else:
            extract(options.output,
                    db, 
                    options,   
                    concepts,
                    verbose=options.verbose,
                    normalForm=options.normalForm)
    else:
        print "This script must be called with one of the --load or --extract option present"
        sys.exit(1)


if __name__ == '__main__':
#    import pycallgraph
#    pycallgraph.start_trace()
    main()
#    pycallgraph.make_dot_graph('snomed-timing.png')
#    sys.exit(1)
