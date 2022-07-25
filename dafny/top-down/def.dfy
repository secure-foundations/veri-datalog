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
type Substitution = map<Term,ConstTerm>
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

  function make_fact(sub:Substitution) : Fact
    requires substitution_complete(sub)
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
    rule.head.substitution_complete(sub) &&
    (forall clause :: clause in rule.body ==> 
     // Substitution has a mapping for each variable in the clause
     && clause.substitution_complete(sub)
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

predicate valid_rule(r:Rule) {
  && (|r.body| == 0 ==> r.head.is_ground())
  && rule_is_range_restricted(r)
}

predicate valid_program(p:Program) {
  forall i :: 0 <= i < |p| ==> valid_rule(p[i])
}

function apply_sub(c:Clause, sub:Substitution) : Clause
{
  var new_terms := 
      seq(|c.terms|, 
          i requires 0 <= i < |c.terms| => 
            var t := c.terms[i];
            match t
              case Const(_) => t
              case Var(_) => if t in sub then sub[t] else t);
    Clause(c.name, new_terms)
}

// Needed below to satisfy Dafny's type checker
function term_to_var_term(t:Term) : VarTerm
  requires t.Var?
{
  t
}

function terms_vars(terms:seq<Term>) : set<VarTerm>
{
  set i | 0 <= i < |terms| && terms[i].Var? :: term_to_var_term(terms[i])
}

function clause_vars(c:Clause) : set<VarTerm>
{
  terms_vars(c.terms)
}

method substitute(c:Clause, sub:Substitution) returns (c':Clause)
  ensures c.substitution_complete(sub) ==> c'.is_ground()
  ensures forall sub' :: c'.substitution_complete(sub') ==>
            c.substitution_complete(sub + sub')
  ensures c' == apply_sub(c, sub)
{
  var new_terms := 
    seq(|c.terms|, 
        i requires 0 <= i < |c.terms| => 
          var t := c.terms[i];
          match t
            case Const(_) => t
            case Var(_) => if t in sub then sub[t] else t);
  c' := Clause(c.name, new_terms);

  forall sub' | c'.substitution_complete(sub') 
    ensures c.substitution_complete(sub + sub')
  {
    forall t | t in c.terms && t.Var? 
      ensures t in sub + sub'
    {
      var i :| 0 <= i < |c.terms| && c.terms[i] == t;
      if c'.terms[i].Var? {
      }
    }
  }
}

method unify_terms(terms:seq<Term>, consts:seq<Term>) returns (s:Option<Substitution>)
{

}

method unify(c1:Clause, c2:Clause) returns (s:Option<Substitution>)
{
  if c1.name != c2.name {
    return None;
  } else { 
    s := unify_terms(c1.terms, c2.terms);   
  }
}

type KnowledgeBase = seq<Fact>

method query(prog:Program, query:Rule) returns (subs: seq<Substitution>)
{
  subs := [];
  for i := 0 to |query.body| {
    // Find rules that might apply
    for j := 0 to |prog| {
      var uresult := unify(query.body[i], prog[j].head);
      match uresult {
        case None => 
        case Some(sub) => subs := subs + [sub];
      }
    }
  }
}
