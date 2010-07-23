


class TopDownSPARQLEntailingStore(Store):
    """
    A Store which uses FuXi's sip strategy and the in-memory SPARQL Algebra
    implementation as a store-agnostic, top-down decision procedure for 
    SPARQL OWL2-RL/RIF/N3 entailment  
    """
    context_aware = True
    formula_aware = True
    transaction_aware = True
    regex_matching = NATIVE_REGEX
    batch_unification = True
    
    def isaBaseQuery(self, query):
        pass
    
    def __init__(self, store,derivedPredicates=[]):
        self.dataset = store
    
    def batch_unify(self, patterns):
        """
        Perform RDF triple store-level unification of a list of triple
        patterns (4-item tuples which correspond to a SPARQL triple pattern
        with an additional constraint for the graph name).  
        
        If there are any derived predicates
        
        For the SQL
        backend, this method compiles the list of triple patterns into SQL
        statements that obtain bindings for all the variables in the list of
        triples patterns.

        :Parameters:
        - `patterns`: a list of 4-item tuples where any of the items can be
           one of: Variable, URIRef, BNode, or Literal.
        
        Returns a generator over dictionaries of solutions to the list of
        triple patterns.  Each dictionary binds the variables in the triple
        patterns to the correct values for those variables.
        
        For more on unification see:
        http://en.wikipedia.org/wiki/Unification  
        """
    
