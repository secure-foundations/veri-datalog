module Core
open FStar.List.Tot

let fin (n:nat) = (x:nat{x < n})

let tuple (n:nat) v = (xs:list v{length xs == n})

let rcons #v (xs : list v) (x : v) = xs @ [x]

let length_rcons #v (xs : list v) (x : v) : Lemma (length (rcons xs x) == length xs + 1) [SMTPat (length (rcons xs x))] = 
  append_length  xs [x]

type pval (g:nat) = 
 | PVar of fin g
 | PAtom of string
 | PNat of nat
 | PPlus : pval g -> pval g -> pval g
 | PList : list (pval g) -> pval g

type pterm (g:nat) = 
  | App : string -> list (pval g) -> pterm g

type pexpr (g:nat) = 
  | PTrue
  | PTerm : pterm g -> pexpr g
  | PAnd : pexpr g -> pexpr g -> pexpr g
  // TODO: and, or, ...

noeq
type pfact = {
  vars : nat;
  head : pterm vars;
  body : pexpr vars
}

let prog = list pfact

type semval d = 
  | SVal : (v:d) -> semval d
  | SNat : nat -> semval d
  | SList : list (semval d) -> semval d

noeq
type model = {
  modDomain : Type0;
  bot : modDomain;
  modAtoms : string -> modDomain;
  modFuncs : string -> list (semval modDomain) -> prop
}

let rec interp_pval (#g : nat) (m : model) (vs : tuple g m.modDomain) (p : pval g)  : semval (m.modDomain) = 
  match p with
  | PVar i -> SVal (index vs i)
  | PAtom s -> SVal (m.modAtoms s)
  | PNat n -> SNat n
  | PPlus x y -> 
    (match interp_pval m vs x, interp_pval m vs y with
     | SNat a, SNat b -> SNat (a + b)
     | _, _ -> SVal m.bot)
  | PList ls -> 
    SList (interp_pval' m vs ls)
and interp_pval' (#g : nat) (m : model) (vs : tuple g m.modDomain) (p : list (pval g)) : list (semval m.modDomain) = 
  match p with
  | [] -> []
  | x::xs' -> interp_pval m vs x :: interp_pval' m vs xs'

let interp_pterm (#g:nat) (m : model) (vs : tuple g m.modDomain) (p : pterm g) : prop = 
  match p with
  | App f ps -> 
    m.modFuncs f (map (interp_pval m vs) ps)

let rec interp_pexpr (#g:nat) (m:model) (vs : tuple g m.modDomain) (p : pexpr g) = 
  match p with
  | PTrue -> True
  | PTerm f -> interp_pterm m vs f
  | PAnd x y -> interp_pexpr m vs x /\ interp_pexpr m vs y

let interp_pfact (m:model) (p : pfact)  = 
  forall (vs : tuple p.vars m.modDomain). 
    interp_pexpr m vs p.body ==> interp_pterm m vs p.head

let interp_prog (m:model) (p : prog) =
  forall (i : fin (length p)). interp_pfact m (index p i)


let infer_sound (m:model) (p : prog) (i : fin (length p)) (vs : tuple (index p i).vars m.modDomain) : 
  Lemma (requires interp_prog m p) (ensures interp_pexpr m vs (index p i).body ==> interp_pterm m vs (index p i).head) = ()
