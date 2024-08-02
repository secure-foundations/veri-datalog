edge(n0, n1).
edge(n1, n2).
connected(A,C) :- edge(A,B), edge(B,C).
go :- connected(n0, n2).
