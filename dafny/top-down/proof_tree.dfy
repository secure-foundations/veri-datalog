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


datatype ProofTree = ProofTree(
    subtrees:seq<ProofTree>, // the subtrees of the current node
    search_clause: SearchClause, // the rule used to construct this node
    subst: EvarSubstitution // the substitution used to construct this node's search clause
) {
    predicate valid() {
        (forall s :: s in subtrees ==> s.valid()) 
        && |subtrees| == 0 ==> |search_clause.rule.body| == 0
    }
}

ghost method ProofFromProofTree(prog: Program, query: Rule, tree:ProofTree) returns (proof:Proof) 
    requires tree.valid()
    requires tree.search_clause.rule == query
    ensures valid_proof(prog, query, proof) // TODO this doesn't work for induction
{
    if |tree.subtrees| == 0 {
        proof := [ProofStep(tree.search_clause.subst_of(), tree.search_clause.rule, [])];
    } else {
        var subproofs := [];
        for i := 0 to |tree.subtrees| {
            var subproof := ProofFromProofTree(prog, query, tree.subtrees[i]);
            assert valid_proof(prog, query, subproof);
            subproofs := subproofs + subproof;

        }
    }
}
