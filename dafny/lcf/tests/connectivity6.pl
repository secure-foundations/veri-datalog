edge(n0, n1).
edge(n1, n2).
edge(n1, n3).
connected(A, B) :-
    edge(A, B).
connected(A, C) :-
    edge(A, B),
    connected(B, C).
go :- connected(n0, n3).
