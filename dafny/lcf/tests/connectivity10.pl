node("n0").
node("n1").
node("n2").
node("n3").
node("n4").
node("n5").
node("n6").
node("n7").
node("n8").
node("n9").
node("n10").
edge("n0", "n1").
edge("n4", "n5").
edge("n3", "n8").
edge("n1", "n2").
edge("n2", "n3").
edge("n3", "n7").
edge("n3", "n4").
edge("n3", "n10").
edge("n3", "n6").
edge("n8", "n9").
source("n0").
destination("n5").
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).
go :- source(S), destination(D), connected(S,D).
