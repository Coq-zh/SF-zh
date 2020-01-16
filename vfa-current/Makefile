-include CONFIGURE
COQMFFLAGS := -Q . VFA 

ALLVFILES := Maps.v Preface.v Perm.v Sort.v Multiset.v Selection.v SearchTree.v ADT.v Extract.v Redblack.v Trie.v Priqueue.v Binom.v Decide.v Color.v  MapsTest.v  PrefaceTest.v  PermTest.v  SortTest.v  MultisetTest.v  SelectionTest.v  SearchTreeTest.v  ADTTest.v  ExtractTest.v  RedblackTest.v  TrieTest.v  PriqueueTest.v  BinomTest.v  DecideTest.v  ColorTest.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: build clean
