"""
See: http://www.w3.org/2000/10/swap/doc/CwmBuiltins
"""

from rdflib import Namespace, Variable, Literal
STRING_NS = Namespace("http://www.w3.org/2000/10/swap/string#")
LOG_NS = Namespace("http://www.w3.org/2000/10/swap/log#")
MATH_NS = Namespace("http://www.w3.org/2000/10/swap/math#")
EULER_NS = Namespace("http://eulersharp.sourceforge.net/2003/03swap/owl-rules#")

def LogNotEqualTo(subject,object_):
    """
    Equality in this sense is actually the same URI.      
    """
    def func(s,o):
        return s != o
    return func

def LogEqualTo(subject,object_):
    """
    True if the subject and object are the same RDF node (symbol or literal).
    """
    def func(s,o):
        return s == o
    return func

def StringContains(subject,object_):
    return subject[-1].contains(object_[-1])

def StringGreaterThan(subject,object_):
    pass

def StringLessThan(subject,object_):
    pass

def StringEqualIgnoringCase(subject,object_):
    pass

#def MathProduct(arguments):
#    def productF(bindings):
#        return eval(' * '.join([isinstance(arg,Variable) and 'bindings[u"%s"]'%arg or str(arg) for arg in arguments]))
#    return productF
def MathEqualTo(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:equalTo can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:equalTo can only be used with Numeric Literals! (%s)"%term    
    def func(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:equalTo can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:equalTo can only be used with Numeric Literals!"
        return s.toPython() == o.toPython()
    return func
def MathGreaterThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def greaterThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:greaterThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:greaterThan can only be used with Numeric Literals!"
        return s.toPython() > o.toPython()
    return greaterThanF

def MathLessThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def lessThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals!"
        return s.toPython() < o.toPython()
    return lessThanF

def MathNotLessThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:notLessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def nLessThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:notLessThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals!"
        return not(s.toPython() < o.toPython())
    return nLessThanF

FUNCTIONS = {
#    MATH_NS.absoluteValue : None,
#    MATH_NS.negation : None,
#    MATH_NS.difference  : MathDifference,
#    MATH_NS.product : MathProduct,
#    MATH_NS.sum : MathSum,    
#    MATH_NS.integerQuotient : MathIntegerQuotient,
#    STRING_NS.concatenation : None,
    #{} => {rdf:nil :memberCount 0}.
    #EULER_NS.memberCount: None,    
}
FILTERS = {
    LOG_NS.equalTo : LogEqualTo,
    LOG_NS.includes : None,
    LOG_NS.notEqualTo : LogNotEqualTo,
    LOG_NS.notIncludes : None,
    MATH_NS.equalTo : MathEqualTo,
    MATH_NS.greaterThan : MathGreaterThan,
    MATH_NS.lessThan : MathLessThan,
    MATH_NS.notEqualTo : None,
    MATH_NS.notGreaterThan : None,
    MATH_NS.notLessThan : MathNotLessThan,
    STRING_NS.contains : StringContains,
    STRING_NS.containsIgnoringCase : None,
    STRING_NS.endsWith : None,
    STRING_NS.equalIgnoringCase : StringEqualIgnoringCase,
    STRING_NS.greaterThan : StringGreaterThan,
    STRING_NS.lessThan : StringLessThan,
    STRING_NS.matches : None,
    STRING_NS.notEqualIgnoringCase : None,
    STRING_NS.notGreaterThan : None,
    STRING_NS.notLessThan : None,
    STRING_NS.notMatches : None,
    STRING_NS.startsWith : None,    
}