#!/usr/bin/env python
# encoding: utf-8
"""
untitled.py

Created by Chimezie Ogbuji on 2008-03-04.
Copyright (c) 2008 __MyCompanyName__. All rights reserved.
"""
from rdflib import plugin
from rdflib.store import Store, VALID_STORE, CORRUPTED_STORE, NO_STORE, UNKNOWN
from rdflib.Graph import Graph, ConjunctiveGraph
import sys
import os
store_id='user-rdf'
connection_string='user=chime,password=1618,db=ctirRdf,host=altix1'

def main():
    store = plugin.get('MySQL',Store)(store_id)
    store.open(connection_string,create=False)
    for kb in store.createTables:
        print kb.createSQL()
    print "\n"
    for suffix,(relations_only,tables) in store.viewCreationDict.items():
        query='create view %s%s as %s'%(store._internedId,
                                        suffix,
        '\n union all \n'.join([t.viewUnionSelectExpression(relations_only) 
                            for t in tables]))
        print query,"\n\n"

if __name__ == '__main__':
	main()

