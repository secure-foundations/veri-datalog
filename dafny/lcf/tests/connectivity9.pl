edge([0, 1], [1, 2]).
edge([1, 2], [1, 2, 3]).
edge([1, 2], [2, 3]).
connected(A, B) :-
    edge(A, B).
connected(A, C) :-
    edge(A, B),
    connected(B, C).
go :- connected([0, 1], [2, 3]).
