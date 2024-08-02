node(n0).
node(n1).
node(n2).
node(n3).
node(n4).
edge(n3, n4).
edge(n2, n3).
edge(n1, n2).
edge(n0, n1).
connected(X, Y) :- edge(X, Y).
connected(A, B) :- edge(A, M), connected(M, B).
go :- connected(n0, n4).
