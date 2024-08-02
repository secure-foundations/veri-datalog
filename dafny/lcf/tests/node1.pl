node(n0).
node(n1).
node(n2).
start(n0).
end(n2).
is_end_node(C) :-
    node(C),
    end(C).
go :-
    start(A),
    node(A),
    is_end_node(B).
