has_length_four(L) :-
  length(L, 4).

go :- has_length_four(["cat", "dog", "bird", "fish"]).
