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
//  http://tinman.cs.gsu.edu/~raj/8710/f03/ch3.pdf
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
      case (Const(_), Var(_)) => sub := sub[t := h];
      case (Var(_), Var(_)) => sub := sub[h := t];
    }
  }
  return Some(sub);
}

method unify(head:Clause, target:Clause) returns (s:Option<Substitution>)
{
  if head.name != target.name || |head.terms| != |target.terms| {
    return None;
  } else { 
    s := unify_terms(head.terms, target.terms);   
  }
}

function method {:extern} int_to_string(i:int) : string

function method make_vars_unique_clause(c:Clause, counter:int) : Clause
{
  var new_terms := 
    seq(|c.terms|, 
        i requires 0 <= i < |c.terms| => 
          var t := c.terms[i];
          match t 
            case Const(_) => t
            case Var(v) => Var(v + int_to_string(counter)));
  Clause(c.name, new_terms)  
}

method make_vars_unique(r:Rule, counter:int) returns (r': Rule)
{
  var head := make_vars_unique_clause(r.head, counter);
  var body := seq(|r.body|, 
           i requires 0 <= i < |r.body| => 
            var c := r.body[i];
            make_vars_unique_clause(c, counter));
  r' := Rule(head, body);
}

method find_matching_rules(c:Clause, prog:Program) returns (matches: seq<(Rule, Substitution)>) 
{
  matches := [];
  // Find rules that might apply
  for j := 0 to |prog| {
    var rule := prog[j];
    var rule' := make_vars_unique(rule, 0);   // TODO: Add a proper counter
    var uresult := unify(rule'.head, c);
    match uresult {
      case None => 
      case Some(sub) => matches := matches + [(rule', sub)];
    }
  }
}

function method apply_sub_clause(sub:Substitution, c:Clause) : Clause
{
  var new_terms := 
    seq(|c.terms|, 
        i requires 0 <= i < |c.terms| => 
          var t := c.terms[i];
          if t in sub then sub[t] else t);
  Clause(c.name, new_terms)
}
            
method apply_sub_clauses(sub:Substitution, clauses:seq<Clause>) returns (s:seq<Clause>)
{
  s := seq(|clauses|, 
           i requires 0 <= i < |clauses| => 
            var c := clauses[i];
            apply_sub_clause(sub, c));          
}

/*
datatype TermPattern = VarPat | ConstPat(c:string)
datatype ClausePattern = ClausePattern(name:string, patterns:seq<TermPattern>)

function method mk_term_pattern(t:Term) : TermPattern
{
  match t
    case Const(c) => ConstPat(c)
    case Var(_) => VarPat
}

function method mk_clause_pattern(c:Clause) : ClausePattern
{
  var patterns :=
    seq(|c.terms|, 
        i requires 0 <= i < |c.terms| => 
          var t := c.terms[i];
          mk_term_pattern(t));
  ClausePattern(c.name, patterns)
}
*/

method query(prog:Program, query:Rule) returns (b:bool)
  requires |query.body| > 0
{
  var stack: seq<seq<Clause>> := [query.body];
  //var goals := {};
  var bound := 0x1_0000_0000;
  while |stack| > 0 && bound > 0 
    decreases bound
    invariant forall i :: 0 <= i < |stack| ==> |stack[i]| > 0
  {
    var clauses := stack[0];
    stack := stack[1..];
    
    // Process the first clause first (TODO: Choose more strategically)
    var clause := clauses[0];
    //var pat := mk_clause_pattern(clause);
    // if pat in goals { }
    //goals := goals + { pat };
    var matches := find_matching_rules(clause, prog);
    if |matches| == 0 {
      // We can't make any progress on this branch, so stop here
      // Signal failure by stopping to process this clause set?
    } else {
      for i := 0 to |matches| 
        invariant forall i :: 0 <= i < |stack| ==> |stack[i]| > 0
      {
        var (rule, sub) := matches[i];
        // TODO: Probably not the same sub in both of these cases
        var rule_body := apply_sub_clauses(sub, rule.body);
        var remaining_clauses := apply_sub_clauses(sub, clauses[1..]);
        var new_clauses := rule_body + remaining_clauses;
        if |new_clauses| == 0 {
          // We've resolved everything down to basic facts!
          return true;
        }
        stack := [new_clauses] + stack;          
      }      
    }
    bound := bound - 1;
  }
  return false;
}

method check_rule(r:Rule) returns (b:bool)
  ensures b == (|r.body| > 0)
{
  b := |r.body| > 0;
}

method run(raw_prog:Program)
  requires |raw_prog| > 0
{
  var prog := DropLast(raw_prog);
  var q := Last(raw_prog);
  //print "Program is: ", prog, "\n";
  //print "Query is: ", q, "\n";
  //var valid_prog := check_program(prog);
  var valid_query := check_rule(q);
  //if valid_prog && valid_query {
  if valid_query {
    var b := query(prog, q);  
    print "Query returned ", b, "\n";
  } else {
    print "Sorry, that's an invalid program and/or query\n";
  }
}
