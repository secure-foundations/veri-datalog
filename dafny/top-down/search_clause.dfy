include "def.dfy"
include "evar.dfy"

include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Sequences/Seq.dfy"
import opened Wrappers
import opened Seq

datatype SearchClause = SearchClause(name:string, evar_terms:seq<Evar>)
{
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