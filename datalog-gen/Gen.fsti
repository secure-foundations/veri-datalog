module Tst
open FStar.String

type ty = 
  | TString : ty
  | TProd : ty -> ty -> ty
  | TList : ty -> ty

let rec interp_ty (t : ty) : Type =
  match t with
  | TString -> string
  | TProd t1 t2 -> interp_ty t1 * interp_ty t2
  | TList t1 -> list (interp_ty t1)

let fresh a = nat -> a & nat
let return #a (x : a) : fresh a = fun n -> (x, n)
let bind #a #b (c : fresh a) (k : a -> fresh b) =
  fun n -> 
    let (y, n') = c n in
    k y n'

let freshIdx : fresh nat = fun n -> (n + 1, n + 1)

let runFresh #a : fresh a -> a = fun c -> fst (c 0)

let rec mkFacts t (cur_id : nat) (v : interp_ty t) : Tot (fresh string) (decreases %[t; v]) = 
  match t with
  | TString -> 
    return (concat "" ["strVal(x"; string_of_int cur_id; ", string_"; v; ")."])
  | TProd t1 t2 -> 
    id1 <-- freshIdx;
    id2 <-- freshIdx;
    let f1 = concat "" ["fst(x"; string_of_int cur_id; ", "; "x"; string_of_int id1; ")."] in
    let f2 = concat "" ["snd(x"; string_of_int cur_id; ", "; "x"; string_of_int id2; ")."] in
    let v : interp_ty t1 & interp_ty t2 = v in
    f3 <-- mkFacts t1 id1 (fst v);
    f4 <-- mkFacts t2 id2 (snd v);
    return (concat "       " [f1; f2; f3; f4])
  | TList t1 -> 
    let v : list (interp_ty t1) = v in
    (match v with 
     | [] -> return (concat "" ["isNil(x"; string_of_int cur_id; ")."])
     | (x::xs) -> 
       id1 <-- freshIdx;
       id2 <-- freshIdx;
       v1 <-- mkFacts t1 id1 x; 

       v2 <-- mkFacts (TList t1) id2 xs; 
       let f1 = concat "" ["isCons(x"; string_of_int cur_id; ", x"; string_of_int id1; ", x"; string_of_int id2; ")."] in
       return (concat "       " [f1; v1; v2]))

let mkFactsMain #t (v : interp_ty t) : string = runFresh (mkFacts t 0 v)

let v : interp_ty (TProd (TProd TString TString) TString) = 
  ( ("a", "b"), "c")

let tst = mkFactsMain v
//  "fst(x0, x1).       snd(x0, x2).       fst(x1, x3).       snd(x1, x4).       strVal(x3, \"a\").       strVal(x4, \"b\").       strVal(x2, \"c\")."

let v2 : interp_ty (TList (TProd TString TString)) = 
  [ ("a", "b"); ("c", "d")]

let tst2 = mkFactsMain v2
//  "isCons(x0, x1, x2).       fst(x1, x3).       snd(x1, x4).       strVal(x3, \"a\").       strVal(x4, \"b\").       isCons(x2, x5, x6).       fst(x5, x7).       snd(x5, x8).       strVal(x7, \"c\").       strVal(x8, \"d\").       isNil(x6)."


(* 
Example datalog program based on traversing v2:

allPairsEqual(X, Y) :- isNil(X), isNil(Y).
allPairsEqual(X, Y) :-
  isCons(X, V1, XS), 
  isCons(Y, V2, YS), 
  allPairsEqual(XS, YS),
  X = Y.

*)
