edge(0, 1).
edge(1, 2).
edge(1, 3).
connected(A, B) :-
    edge(A, B).
connected(A, C) :-
    edge(A, B),
    connected(B, C).
go :- connected(0, 3).
