module Example
open FStar.List
open Core

// f(X) :- g(X).

let fact1 : pfact = {
  vars = 1;
  head = App "f" [PVar 0];
  body = PTerm (App "g" [PVar 0])
}

// g(x).

let fact2 : pfact = {
  vars = 0;
  head = App "g" [PAtom "x"];
  body = PTrue
}

unfold let prog = [fact1; fact2]

// f(x)
let test (m : model) : Lemma (requires interp_prog m prog) (ensures interp_pterm m [] (App "f" [PAtom #0 "x"])) = 
  infer_sound m prog 1 [];
  infer_sound m prog 0 [SVal?.v (interp_pval m [] (PAtom #0 "x"))]
