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
datatype ProofStep = ProofStep(subst:EvarSubstitution, rule:Rule, success_emap:EvarMap) {
    predicate valid() {
        exists e:Evar :: e in success_emap.evar_map && true
        // && subst.getreverse(e).Some?
        // && rule.head.substitution_complete(get_substitution_from_subst(subst, success_emap))
    }
}

type Proof = seq<ProofStep>
