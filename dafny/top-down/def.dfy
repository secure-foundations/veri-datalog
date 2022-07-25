// Used by spec
include "std-lib/src/Collections/Sequences/Seq.dfy"
// Used by impl
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Math.dfy"
//include "std-lib/src/Collections/Sets/Sets.dfy"
import opened Seq
//import opened Sets
import opened Wrappers


// References:
//  https://abiteboul.com/TEACHING/DBCOURSE/deductive-eval-datalog.pdf
//  https://www.sti-innsbruck.at/sites/default/files/thesis/christoph-fuchs-thesis-final-09-2008.pdf
//  http://webdam.inria.fr/Alice/pdfs/Chapter-13.pdf
//  https://pages.cs.wisc.edu/~paris/cs838-s16/lecture-notes/lecture8.pdf
//  https://www.vldb.org/conf/1987/P043.PDF

////////////////////////////////////////
// Trusted Specification
////////////////////////////////////////
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

////////////////////////////////////////
// (Verified) Implementation
////////////////////////////////////////

method substitute(c:Clause, sub:Substitution) returns (c':Clause)
{
  var new_terms := 
    seq(|c.terms|, 
        i requires 0 <= i < |c.terms| => 
          var t := c.terms[i];
          match t
            case Const(_) => t
            case Var(_) => if t in sub then sub[t] else t);
  c' := Clause(c.name, new_terms);
}

method unify_terms(head:seq<Term>, target:seq<Term>) returns (s:Option<Substitution>)
  requires |head| == |target|
{
  var sub := map [];
  for i := 0 to |head| {
    var h := head[i];
    var t := target[i];
    match (h, t) {
      case (Const(hc), Const(tc)) => if hc != tc { return None; }
      case (Var(_), Const(_)) => sub := sub[h := t];
      case (Const(_), Var(_)) => return None;
      case (Var(_), Var(_)) => sub := sub[t := t];
    }
  }
  return Some(sub);
}

method unify(c1:Clause, c2:Clause) returns (s:Option<Substitution>)
{
  if c1.name != c2.name || |c1.terms| != |c2.terms| {
    return None;
  } else { 
    s := unify_terms(c1.terms, c2.terms);   
  }
}

method find_matching_rules(c:Clause, prog:Program) returns (matches: seq<(Rule, Substitution)>) 
{
  matches := [];
  // Find rules that might apply
  for j := 0 to |prog| {
    var rule := prog[j];
    var uresult := unify(c, rule.head);
    match uresult {
      case None => 
      case Some(sub) => matches := matches + [(rule, sub)];
    }
  }
}

type KnowledgeBase = seq<Fact>

method query(prog:Program, query:Rule) returns (subs: seq<Substitution>)
{
  

  subs := [];
  var stack := query.body;
  while |stack| > 0 {
    var target_clause := stack[0];
    stack := stack[1..];
    // Find rules that might apply
    for j := 0 to |prog| {
      var uresult := unify(target_clause, prog[j].head);
      match uresult {
        case None => 
        case Some(sub) => 
          // Apply sub to the rule's body

          // Push body onto the stack
      }
    }
  }
}
