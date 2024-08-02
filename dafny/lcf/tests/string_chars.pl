num_chars(S, N) :-
  string_chars(S, C),
  length(C, N).

go :- num_chars("hello", 5).
