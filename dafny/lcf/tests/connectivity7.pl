edge("cat", "dog").
edge("dog", "bird").
edge("dog", "fish").
connected(A, B) :-
    edge(A, B).
connected(A, C) :-
    edge(A, B),
    connected(B, C).
go :- connected("dog", "fish").
