node(n0).
node(n1).
node(n2).
node(n3).
node(m0).
node(m1).
node(m2).
node(m3).
node(n4).
edge(n3, n4).
edge(n1, n3).
edge(n1, n2).
edge(n0, n1).
edge(n1, m0).
edge(m0, m1).
edge(m1, m2).
edge(m2, m3).
source(n0).
destination(m3).
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).
query(S, D) :- source(S), destination(D), connected(S, D).
go :- query(n0, m3).
