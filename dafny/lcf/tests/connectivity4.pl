node(a0).
node(a1).
node(a2).
node(a3).
node(a4).
node(b0).
node(b1).
node(b2).
node(b3).
node(b4).
node(c0).
edge(a0, a1).
edge(a1, a2).
edge(a0, a3).
edge(a3, a4).
edge(a4, c0).
edge(b0, b1).
edge(b1, b2).
edge(b0, b3).
edge(b3, b4).
edge(b4, c0).

doubleconnected(A, B, C) :-
    edge(A, C),
    edge(B, C).
doubleconnected(A, B, C) :-
    edge(A, X),
    edge(B, C),
    doubleconnected(X, B, C).
doubleconnected(A, B, C) :-
    edge(A, C),
    edge(B, Y),
    doubleconnected(A, Y, C).
doubleconnected(A, B, C) :-
    edge(A, X),
    edge(B, Y),
    doubleconnected(X, Y, C).

go :- doubleconnected(a0, b0, c0).
