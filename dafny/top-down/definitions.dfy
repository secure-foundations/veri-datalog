// Used by spec
include "std-lib/src/Collections/Sequences/Seq.dfy"
// Used by impl
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Math.dfy"
//include "std-lib/src/Collections/Sets/Sets.dfy"
import opened Seq
//import opened Sets
import opened Wrappers

datatype Term = Var(s:string) | Const(c:string)
type ConstTerm = t:Term | t.Const? witness Const("")
type VarTerm = t:Term | t.Var? witness Var("")
type Substitution = map<Term,Term>
datatype Clause = Clause(name:string, terms:seq<Term>)
{
  predicate is_ground() 
  {
    forall t :: t in terms ==> t.Const?
  }

  predicate substitution_complete(sub:Substitution) 
  {
    forall t :: t in terms && t.Var? ==> t in sub
  }

  predicate substitution_concrete(sub:Substitution) 
  {
    substitution_complete(sub) && forall t :: t in terms && t.Var? ==> sub[t].Const?
  }

  function make_fact(sub:Substitution) : Fact
    requires substitution_concrete(sub)
  {
    var new_terms := 
      seq(|terms|, 
          i requires 0 <= i < |terms| => 
            var t := terms[i];
            match t
              case Const(c) => t
              case Var(s) => sub[t]);
    Clause(name, new_terms)
  }
}
type Fact = c:Clause | c.is_ground() witness Clause("", [])
datatype Rule = Rule(head:Clause, body:seq<Clause>) 
type Program = seq<Rule>


datatype ProofStep = ProofStep(sub:Substitution, rule:Rule, facts:seq<Fact>)
{
  predicate valid() {
    // Substitution has a mapping for each variable in the head
    rule.head.substitution_concrete(sub) &&
    (forall clause :: clause in rule.body ==> 
     // Substitution has a mapping for each variable in the clause
     && clause.substitution_concrete(sub)
     // We can satisfy this clause with an existing fact
     && clause.make_fact(sub) in facts)
  }

  // The new fact we can conclude by applying this rule
  function new_fact() : Fact
    requires valid() 
  {
    rule.head.make_fact(sub)
  }
}

/*
assert(exists i :: s[i] == a)
var i | 0 <= i < |s| && s[i] == a;
...
assert((s'+s)[|s'|+i] == a);
assert(a in (s'+s));
*/


/*
valid_proof(prog, A(X,Y), ...)
valid_proof(prog, B(P,Q), ...)
==>
valid_proof(prog, A(X,Y), ...) // where seq<Fact> contains B(P,Q)

*/

type Proof = seq<ProofStep> 

predicate valid_proof(prog:Program, query:Rule, proof:Proof)
{
  && |proof| > 0
  // We start with an empty set of facts
  && First(proof).facts == []
  // Each proof step is valid 
  && (forall i :: 0 <= i < |proof| ==> proof[i].valid())
  // Each proof step except the last uses a rule from the program
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i].rule in prog)
  // Each proof step extends the set of facts by one
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i+1].facts == proof[i].facts + [ proof[i].new_fact() ] )
  // Last proof step shows the query is valid
  && Last(proof).rule == query
}

predicate valid_query(prog:Program, query:Rule)
{
  exists proof :: valid_proof(prog, query, proof)
}