query(N) :- Min = 1, Max = 10, N \= 13, Min =< N, N =< Max.
go :- query(5).
