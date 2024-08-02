hello_world(S) :-
    string_lower(S, "hello world").

go :- hello_world("HeLLo wOrLD").
