include "evar.dfy"
include "definitions.dfy"
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Sequences/Seq.dfy"
include "bijective_map.dfy"
import opened Wrappers
import opened Seq
import opened BijectiveMap

// TODO write some documentation here :)
datatype SearchClause = SearchClause(name:string, evar_terms:seq<Evar>, clause: Clause, subst: EvarSubstitution)
{
    predicate valid()
    {
        && valid_clause(clause) // Restriction
        // && distinct(evar_terms) // Restriction
        && (name == clause.name)
        && subst.valid()
        && (subst.Values() == ToSet(evar_terms))
        // && (subst.Values == ToSet(evar_terms))
        && |evar_terms| == |clause.terms|
        && forall i:nat | i < |clause.terms| :: (subst.in1(clause.terms[i])
                                                 && subst.get1(clause.terms[i]) == evar_terms[i])
        // && forall i:nat | i < |clause.terms| :: (clause.terms[i] in subst
        //                                          && subst[clause.terms[i]] == evar_terms[i])
    }

    predicate valid_emap(emap: EvarMap) 
        reads emap
        requires valid() // TODO: This is required
    {
        && (forall e:Evar :: e in evar_terms ==> e in emap.evar_map)
        && (forall e:Evar :: subst.in2(e) ==> e in emap.evar_map)
        // && (forall e:Evar :: e in subst.Values ==> e in emap.evar_map)
        // multiset(evar_terms) <= multiset(emap.evar_map.Keys)
    }

    predicate emap_fully_resolved(emap: EvarMap)
        reads emap
        requires valid()
        requires valid_emap(emap)
    {
        forall e:Evar :: e in evar_terms ==> emap.evar_map[e].Some?
    }

/*

    predicate valid_proof_for(proof: Proof, emap: EvarMap)
        requires valid_emap(emap)
    {
        valid_proof(proof, (subst \compose emap)(clause))
    }

*/

    // predicate valid()
    // {
    //     rule.head.name == name
    //     // Todo something about the body mapping to the rule's body under some evar map
    // }
    // function subst_of() : Substitution
    //     ensures rule.head.substitution_concrete(subst_of())
    //     ensures (forall clause :: clause in rule.body ==> 
    //                     clause.substitution_concrete(subst_of()))
    // {
    //     //bimap.l_to_r
    //     assume false;
    //     map[]
    //     // todo something about applying it to an evar_map to get an actual concrete subst out of it
    // }

  // predicate is_ground() 
  // {
  //   forall t :: t in terms ==> t.Const?
  // }

  // predicate substitution_complete(sub:Substitution) 
  // {
  //   forall t :: t in terms && t.Var? ==> t in sub
  // }

  // predicate substitution_concrete(sub:Substitution) 
  // {
  //   substitution_complete(sub) && forall t :: t in terms && t.Var? ==> sub[t].Const?
  // }

  // function make_fact(sub:Substitution) : Fact
  //   requires substitution_concrete(sub)
  // {
  //   var new_terms := 
  //     seq(|terms|, 
  //         i requires 0 <= i < |terms| => 
  //           var t := terms[i];
  //           match t
  //             case Const(c) => t
  //             case Var(s) => sub[t]);
  //   SearchClause(name, new_terms)
  // }
}