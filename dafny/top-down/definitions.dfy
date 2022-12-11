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

predicate valid_proof(prog:Program, query:Clause, proof:Proof)
{
  && |proof| > 0
  // We start with an empty set of facts
  && First(proof).facts == []
  // Each proof step is valid 
  && (forall i :: 0 <= i < |proof| ==> proof[i].valid())
  // Each proof step uses a rule from the program
  && (forall i :: 0 <= i < |proof| ==> proof[i].rule in prog)
  // Each proof step extends the set of facts by one
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i+1].facts == proof[i].facts + [ proof[i].new_fact() ] )
  // Last proof step shows the query is valid
  && Last(proof).rule.head == query
}

predicate valid_query(prog:Program, query:Clause)
{
  exists proof :: valid_proof(prog, query, proof)
}


predicate match_exists(t:Term, clauses:seq<Clause>) 
{
  exists i, j :: 0 <= i < |clauses| && 0 <= j < |clauses[i].terms| && clauses[i].terms[j] == t
}

predicate rule_is_range_restricted(r:Rule)
{
  if |r.body| == 0 then true
  else
    forall t:Term :: t in r.head.terms ==> 
      (t.Var? ==> match_exists(t, r.body))
}

// Check that a clause does not have duplicate terms
predicate valid_clause(c:Clause) {
  forall i:nat, j:nat | i < |c.terms| && j < |c.terms| :: i != j ==> c.terms[i] != c.terms[j]
}

predicate valid_rule(r:Rule) {
  && (|r.body| == 0 ==> r.head.is_ground())
  && rule_is_range_restricted(r)
  // TODO: The below two conditions are temporary relaxations
  && valid_clause(r.head)
  && forall b :: b in r.body ==> valid_clause(b)
}

predicate valid_program(p:Program) {
  forall i :: 0 <= i < |p| ==> valid_rule(p[i])
}

method clause_is_ground(c:Clause) returns (b:bool)
  ensures b == c.is_ground()
{
  for i := 0 to |c.terms| 
    invariant forall j :: 0 <= j < i ==> c.terms[j].Const?
  {
    if !c.terms[i].Const? {
      return false;
    }
  }
  return true;
}

method find_var(term:Term, clauses:seq<Clause>) returns (b:bool)
  ensures b == match_exists(term, clauses)
{
  for i := 0 to |clauses| 
    invariant forall m :: 0 <= m < i ==>
                (forall k :: 0 <= k < |clauses[m].terms| ==> clauses[m].terms[k] != term) 
  {
    var clause := clauses[i];
    for j := 0 to |clause.terms| 
      invariant forall k :: 0 <= k < j ==> clause.terms[k] != term
    {
      if clause.terms[j] == term {
        return true;
      }
    }
  }
  return false;
}

method check_clause(c:Clause) returns (b:bool)
  ensures b == valid_clause(c)
{
  var terms_seen:set<Term> := {};
  reveal ToSet();
  for k := 0 to |c.terms|
    invariant terms_seen == ToSet(c.terms[..k])
    invariant forall i:nat, j:nat | i < k && j < k :: i != j ==> c.terms[i] != c.terms[j]
  {
    if c.terms[k] in terms_seen {
      return false;
    } else {
      terms_seen := terms_seen + {c.terms[k]};
    }
  }
  return true;
}

method check_rule(r:Rule) returns (b:bool)
  ensures b == valid_rule(r)
{
  if |r.body| == 0 {
    var bb := clause_is_ground(r.head);
    if !bb {
      return false;
    }
  } else {
      for i := 0 to |r.head.terms| 
        invariant forall j :: 0 <= j < i ==> (r.head.terms[j].Var? ==> match_exists(r.head.terms[j], r.body))
      {
        var term := r.head.terms[i];
        if term.Var? {
          var bbb := find_var(term, r.body);
          if !bbb {
            return false;
          }
        }
      }
  }
  // TODO: The below is a restriction on the types of clauses allowed in the Datalog program
  var b' := check_clause(r.head);
  if !b' {
    return false;
  }
  for i := 0 to |r.body| 
    invariant forall j | 0 <= j < i :: valid_clause(r.body[j])
  {
    var b'' := check_clause(r.body[i]);
    if !b'' {
      return false;
    }
  }
  return true;
}

method check_program(prog:Program) returns (b:bool)
  ensures b == valid_program(prog)
{
  b := true;
  for i := 0 to |prog| 
    invariant forall j :: 0 <= j < i ==> valid_rule(prog[j])
  {
    var valid_rule := check_rule(prog[i]);
    if !valid_rule {
      return false;
    }
  }
}