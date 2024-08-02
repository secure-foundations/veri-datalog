single_digit_prime(N) :-
    member(N, [2, 3, 5, 7]).

go :- single_digit_prime(7).
