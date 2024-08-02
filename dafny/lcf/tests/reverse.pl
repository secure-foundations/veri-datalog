one_two_three(L) :-
    reverse(L, [3, 2, 1]).

go :- one_two_three([1, 2, 3]).
