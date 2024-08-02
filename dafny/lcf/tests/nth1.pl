third_is_seven(L) :-
    nth1(3, L, 7).

go :- third_is_seven([3, 42, 7, 9]).
