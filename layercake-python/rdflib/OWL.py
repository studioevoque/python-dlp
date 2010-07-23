from rdflib.Namespace import Namespace

OWLNS = Namespace("http://www.w3.org/2002/07/owl#")

Thing                  = OWLNS.Thing
Nothing                = OWLNS.Nothing
AllDifferent           = OWLNS.AllDifferent
Restriction            = OWLNS.Restriction
ObjectProperty         = OWLNS.ObjectProperty
DatatypeProperty       = OWLNS.DatatypeProperty
TransitiveProperty     = OWLNS.TransitiveProperty
SymmetricProperty      = OWLNS.SymmetricProperty
FunctionalProperty     = OWLNS.FunctionalProperty
InverseFunctionalProperty=OWLNS.InverseFunctionalProperty
AnnotationProperty     = OWLNS.AnnotationProperty
Ontology               = OWLNS.Ontology
OntologyProperty       = OWLNS.OntologyProperty
DeprecatedClass        = OWLNS.DeprecatedClass
DeprecatedProperty     = OWLNS.DeprecatedProperty
DataRange              = OWLNS.DataRange
minCardinality         = OWLNS.minCardinality
maxCardinality         = OWLNS.maxCardinality
cardinality            = OWLNS.cardinality
equivalentClass        = OWLNS.equivalentClass
disjointWith           = OWLNS.disjointWith
equivalentProperty     = OWLNS.equivalentProperty
sameAs                 = OWLNS.sameAs
Class                  = OWLNS.Class
differentFrom          = OWLNS.differentFrom
distinctMembers        = OWLNS.distinctMembers
unionOf                = OWLNS.unionOf
intersectionOf         = OWLNS.intersectionOf
complementOf           = OWLNS.complementOf
oneOf                  = OWLNS.oneOf
onProperty             = OWLNS.onProperty
allValuesFrom          = OWLNS.allValuesFrom
someValuesFrom         = OWLNS.someValuesFrom
hasValue               = OWLNS.hasValue
inverseOf              = OWLNS.inverseOf
imports                = OWLNS.imports
backwardCompatibleWith = OWLNS.backwardCompatibleWith
incompatibleWith       = OWLNS.incompatibleWith
versionInfo            = OWLNS.versionInfo
priorVersion           = OWLNS.priorVersion
distinctMembers        = OWLNS.distinctMembers

literalProperties = [
    minCardinality,
    maxCardinality,
    cardinality,
    versionInfo,
]

resourceProperties = [
    equivalentClass,
    disjointWith,
    equivalentProperty,
    sameAs,
    differentFrom,
    distinctMembers,
    unionOf,
    intersectionOf,
    complementOf,
    oneOf,
    onProperty,
    allValuesFrom,
    hasValue,
    someValuesFrom,
    inverseOf,
    imports,
    versionInfo,
    priorVersion,
    backwardCompatibleWith,
    incompatibleWith,
]