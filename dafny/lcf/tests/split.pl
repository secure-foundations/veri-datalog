three_parts(S) :-
  split_string(S, ".", "", P),
  length(P, L),
  L == 3.

go :- three_parts("a.b.c").
