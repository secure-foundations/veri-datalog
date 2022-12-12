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
        && (forall i:nat | i < |clause.terms| :: clause.terms[i].Const? ==> emap.evar_map[evar_terms[i]] == Some(clause.terms[i].c))
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

    lemma make_fact_preserves(emap: EvarMap)
        requires valid()
        requires emap.inv()
        requires subst.valid()
        requires valid_emap(emap)
        requires emap_fully_resolved(emap)
        requires forall e:Evar :: subst.in2(e) ==> e in emap.evar_map
        requires clause.substitution_concrete(make_subst(emap, subst))
        ensures forall i:nat | i < |clause.make_fact(make_subst(emap, subst)).terms| 
                       :: clause.make_fact(make_subst(emap, subst)).terms[i].c == emap.evar_map[evar_terms[i]].value
    {
        var s := make_subst(emap, subst);
        var f := clause.make_fact(s);
        assert |f.terms| == |evar_terms|;
        for i := 0 to |f.terms|
            invariant forall j:nat | j < i :: f.terms[j].Const?
            invariant forall j:nat | j < i :: emap.evar_map[evar_terms[j]].Some?
            // invariant forall j:nat | j < i :: evar_terms[j] in emap.evar_map
            invariant forall j:nat | j < i :: f.terms[j].c == emap.evar_map[evar_terms[j]].value
        {
            var lhs := f.terms[i];
            assert (lhs.Const?);
            var rhs := emap.evar_map[evar_terms[i]];
            assert (rhs.Some?);
            assert (subst.get1(clause.terms[i]) == evar_terms[i]);
            assert (s[clause.terms[i]] == Const(rhs.value));
            if (s[clause.terms[i]].Var?) {
                assert (s[clause.terms[i]] == f.terms[i]);
                assert (lhs.c == rhs.value);
            }
            // assert (evar_terms[i] == subst.)
            assert (lhs.c == rhs.value);
        } 
    }

    twostate lemma monotonically_increasing_preserves_valid_emap(emap: EvarMap)
        requires old(emap.inv())
        requires valid()
        requires old(valid_emap(emap))
        requires emap.monotonically_increasing()
        ensures valid_emap(emap)
    {

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