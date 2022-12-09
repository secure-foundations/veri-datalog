// Used by spec
include "std-lib/src/Collections/Sequences/Seq.dfy"
// Used by impl
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Math.dfy"
include "definitions.dfy"
include "evar.dfy"
include "search_clause.dfy"
import opened Seq
//import opened Sets
import opened Wrappers


// TODO: Create another datastructure that ties 'subst' to 'rule'
// datatype TopDownProofStep = ProofStep(subst:EvarSubstitution, rule:Rule, success_emap:EvarMap) {
//     predicate valid() 
//         reads success_emap
//     {
//         && forall e :: e in subst.Values ==> e in success_emap.evar_map
//         && success_emap.fully_resolved()
//         // exists e:Evar :: e in success_emap.evar_map && true
//         // && subst.getreverse(e).Some?
//         // && rule.head.substitution_complete(get_substitution_from_subst(subst, success_emap))
//     }

//     function subst_of() : Substitution
//         reads success_emap
//         requires valid()
//     {
//         map v:VarTerm | v in subst.Keys :: Const(success_emap.evar_map[subst[v]].value)
//     }
// }

// type TopDownProof = seq<TopDownProofStep>









/*

Suppose we have used the rule:

A(X, Y) :- B(X, Y), C(Y, Z), D(X, Z).

to prove A("x","y").

The recursive calls to search() should return proofs:
    B(x,y) with factset1
    C(y,z) with factset2
    D(x,z) with factset3

The proof of A(x, y) looks like:
    ProofStep(subst = [X->x, Y->y, Z->z], rule = A(X,Y) :- ..., facts = factset1 ++ factset2 ++ factset3) 
    ++ [proof of B(x,y) with factset1 \union factset2 \union factset3] 
    ++ [proof of C(y,z) with factset2 \union factset3] 
    ++ [proof of D(x,z) with factset3]

applyRule : seq<Proof> -> Rule -> Proof
proofs of RHS -> rule -> proof of LHS

==> Need to write a unionFactSet operation that flattens multiple proofs into one.

Proof of validity for the ProofStep:
    assert (B(x,y) in factset)      because B(x,y) in factset1
    assert (C(y,z) in factset)      because C(y,z) in factset2
    assert (D(x,z) in factset)      because D(x,z) in factset3
(concreteness follows)
*/