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

method unify_terms(terms:seq<Term>, consts:seq<ConstTerm>) returns (s:Option<Substitution>)
  ensures s.Some? ==> |terms| == |consts| && 
    (forall j :: 0 <= j < |terms| ==> 
      match terms[j]
        case Var(_) => terms[j] in s.value && s.value[terms[j]] == consts[j]
        case Const(_) => terms[j] == consts[j])
    && s.value.Keys == terms_vars(terms)
{
  if |terms| != |consts| {
    s := None;
  } else if |terms| == 0 {
    s:= Some(map[]);
  } else {
    var sub:Substitution := map[];
    for i := 0 to |terms| 
      invariant sub.Keys == terms_vars(terms[..i])
      invariant forall j :: 0 <= j < i ==> 
        match terms[j]
        case Var(_) => terms[j] in sub && sub[terms[j]] == consts[j]
        case Const(_) => terms[j] == consts[j]
    {
      var term := terms[i];
      var cons := consts[i];
      match term {
        case Var(s) => 
              // The substitution we computed isn't consistent with the current pair
              if term in sub && sub[term] != cons {
                return None;
              }
              // Extend the substitution with the current pair
              sub := sub[term := cons];
        case Const(c) =>
          if c != cons.c {
            return None;
          }
      }
    }
    s := Some(sub);
  }
}

method unify(c:Clause, fact:Fact) returns (s:Option<Substitution>)
  ensures s.Some? ==> c.substitution_complete(s.value) 
                   && c.make_fact(s.value) == fact
                   && s.value.Keys == clause_vars(c)
{
  if c.name != fact.name {
    return None;
  } else { 
    s := unify_terms(c.terms, fact.terms);   
  }
}

type KnowledgeBase = seq<Fact>

predicate subs_complete_all(c:Clause, subs:seq<Substitution>)
{
  forall m :: 0 <= m < |subs| ==> c.substitution_complete(subs[m])
}

predicate facts_complete_all(c:Clause, subs:seq<Substitution>, kb:KnowledgeBase)
  requires subs_complete_all(c, subs)
{
  forall m :: 0 <= m < |subs| ==> c.make_fact(subs[m]) in kb
}

lemma lemma_make_fact_consistent(c:Clause, f:Fact, s:Substitution, s0:Substitution, s1:Substitution)
  requires s == s0 + s1
  requires c.substitution_complete(s1)
  requires c.make_fact(s1) == f
  ensures  c.make_fact(s) == f
{

}

lemma make_fact_transitive(c:Clause, g:Clause, fact:Fact, s0:Substitution, s1:Substitution)
  requires g == apply_sub(c, s0)
  requires g.substitution_complete(s1)
  requires s1.Keys == clause_vars(g)
  requires fact == g.make_fact(s0 + s1)
  ensures  c.substitution_complete(s0 + s1)
  ensures  fact == c.make_fact(s0 + s1)
{
  var s := s0 + s1;
  assert c.substitution_complete(s) by {
    forall t | t in c.terms && t.Var?
      ensures t in s
    {
      if t in g.terms {
        assert t in s1;
      } else {
        if t !in s0 {
          var i :| 0 <= i < |c.terms| && c.terms[i] == t;
          assert g.terms[i] == if t in s0 then s0[t] else t;
        }
        
      }
    }
  }  
}

method eval_clause(kb:KnowledgeBase, c:Clause, subs:seq<Substitution>) returns (subs':seq<Substitution>)
  ensures forall i :: 0 <= i < |subs'| ==> c.substitution_complete(subs'[i]) && c.make_fact(subs'[i]) in kb
  ensures forall c':Clause :: subs_complete_all(c', subs) ==> subs_complete_all(c', subs')
  ensures forall c':Clause :: subs_complete_all(c', subs) && facts_complete_all(c', subs, kb) 
                           ==> subs_complete_all(c', subs') && facts_complete_all(c', subs', kb) 
{
  subs' := [];
  for i := 0 to |subs| 
    invariant forall j :: 0 <= j < |subs'| ==> c.substitution_complete(subs'[j]) && c.make_fact(subs'[j]) in kb
    invariant forall c':Clause :: subs_complete_all(c', subs) ==> subs_complete_all(c', subs')
    invariant forall c':Clause :: subs_complete_all(c', subs) && facts_complete_all(c', subs, kb) 
                              ==> subs_complete_all(c', subs') && facts_complete_all(c', subs', kb) 
  {
    var grounded := substitute(c, subs[i]);
    //print "\t\t\tgrounded ", c, " to get ", grounded, "\n";
    for j := 0 to |kb| 
      invariant forall k :: 0 <= k < |subs'| ==> c.substitution_complete(subs'[k]) && c.make_fact(subs'[k]) in kb
      invariant forall c':Clause :: subs_complete_all(c', subs) ==> subs_complete_all(c', subs')
      invariant forall c':Clause :: subs_complete_all(c', subs) && facts_complete_all(c', subs, kb) 
                              ==> subs_complete_all(c', subs') && facts_complete_all(c', subs', kb) 
    {
      var extension := unify(grounded, kb[j]);
      match extension {
        case None =>
        case Some(sub) =>
          assert grounded.substitution_complete(sub);
 
          //assume sub.Keys * subs[i].Keys == {};
          //assert grounded.make_fact(sub + subs[i]) == kb[j];
          //print "\t\tUnified ", c, " with ", kb[j], " and got ", sub, "\n";
          ghost var old_subs' := subs';
          subs' := subs' + [subs[i] + sub];
          //assert Last(subs') == subs[i] + sub;
          forall k | 0 <= k < |subs'|
            ensures c.substitution_complete(subs'[k]) && c.make_fact(subs'[k]) in kb
          {            
            if k < |subs'| - 1 {
              assert subs'[k] == old_subs'[k];
              assert c.make_fact(subs'[k]) in kb;
            } else {
              assert subs'[k] == subs[i] + sub;
              assert grounded.make_fact(sub) == kb[j];
              lemma_make_fact_consistent(grounded, kb[j], subs[i] + sub, subs[i], sub);
              assert grounded.make_fact(subs[i] + sub) == kb[j];
              make_fact_transitive(c, grounded, kb[j], subs[i], sub);
            }          
          }
        forall c':Clause | subs_complete_all(c', subs) && facts_complete_all(c', subs, kb) 
          ensures subs_complete_all(c', subs') && facts_complete_all(c', subs', kb)
        {
          forall m | 0 <= m < |subs'|
            ensures c'.make_fact(subs'[m]) in kb
          {
            if m < |old_subs'| {
            } else {              
              //assume sub.Keys * subs[i].Keys == {};
              assert subs'[m] == subs[i] + sub;
              assert c'.make_fact(subs'[m]) == c'.make_fact(subs[i]);
            }
          }
        }
      }
    }
  }
}

method eval_clauses(kb:KnowledgeBase, clauses:seq<Clause>) returns (subs:seq<Substitution>) 
  ensures forall j :: 0 <= j < |clauses| ==> 
              && subs_complete_all(clauses[j], subs)
              && facts_complete_all(clauses[j], subs, kb)
{
  subs := [map[]];
  for i := 0 to |clauses| 
    invariant forall j :: 0 <= j < i 
      ==> subs_complete_all(clauses[j], subs)
      && facts_complete_all(clauses[j], subs, kb)
  {
    var old_subs := subs;
    subs := eval_clause(kb, clauses[i], subs);
  }
}

predicate valid_partial_proof(prog:Program, proof:Proof)
{
  |proof| > 0 ==>
  // We start with the base set of facts
  && First(proof).facts == []
  // Each proof step is valid and uses a rule from the program
  && (forall i :: 0 <= i < |proof| ==> proof[i].valid() && proof[i].rule in prog)
  // Each proof step extends the set of facts by one
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i+1].facts == proof[i].facts + [ proof[i].new_fact() ] )
}

lemma lemma_valid_proof_step(step:ProofStep)
  requires valid_rule(step.rule)
  requires forall j :: 0 <= j < |step.rule.body| ==>                 
                 step.rule.body[j].substitution_complete(step.sub)
              && step.rule.body[j].make_fact(step.sub) in step.facts
  ensures step.valid()
{  
}

method eval_rule(prog:Program, kb:KnowledgeBase, r:Rule, ghost proof:Proof) returns (kb':KnowledgeBase, ghost proof':Proof)
  requires valid_rule(r)
  requires r in prog
  requires valid_partial_proof(prog, proof)
  requires |kb| > 0 && |proof| > 0 
  requires Last(kb) == Last(proof).new_fact()
  requires Last(proof).facts == DropLast(kb)
  ensures valid_partial_proof(prog, proof')
  ensures |kb'| > 0 && |proof'| > 0 
  ensures Last(kb') == Last(proof').new_fact()
  ensures Last(proof').facts == DropLast(kb')
  ensures |kb'| > |kb| ==> Last(proof').rule == r
{
  //print "Evaluating rule: ", r, "\n";
  if |r.body| == 0 {
    kb' := kb + [r.head];
    proof' := proof + [ProofStep(map[], r, kb)];
  }

  kb' := kb;
  proof' := proof;
  
  var subs := eval_clauses(kb, r.body);
 
  //print "\teval_clauses returned: ", subs, "\n";
  for i := 0 to |subs| 
    invariant valid_partial_proof(prog, proof')
    invariant |kb'| > 0 && |proof'| > 0
    invariant Last(kb') == Last(proof').new_fact()
    invariant Last(proof').facts == DropLast(kb')
    invariant kb <= kb';
    invariant|kb'| > |kb| ==> Last(proof').rule == r
  {
    ghost var step := ProofStep(subs[i], r, kb');
    var new_fact := substitute(r.head, subs[i]);    
    //print "\tFound a new fact: ", new_fact, "\n";
    ghost var old_kb' := kb';
    if new_fact !in kb' {
      kb' := kb' + [new_fact];  
      lemma_valid_proof_step(step);
      assert step.valid();
      proof' := proof' + [step];    
    } 
  }
}

method eval_query_once(prog:Program, kb:KnowledgeBase, r:Rule, ghost proof:Proof) returns (kb':KnowledgeBase, ghost proof':Proof)
  requires valid_rule(r)
  requires valid_partial_proof(prog, proof)
  requires |kb| > 0 && |proof| > 0 
  requires Last(kb) == Last(proof).new_fact()
  requires Last(proof).facts == DropLast(kb)
  ensures |kb'| > |kb| ==> |proof'| > 0 && Last(proof').rule == r && valid_proof(prog, r, proof')
{
  //print "Evaluating rule: ", r, " against: ", kb, "\n";
  if |r.body| == 0 {
    kb' := kb + [r.head];
    proof' := proof + [ProofStep(map[], r, kb)];
  }

  kb' := kb;
  proof' := proof;
  var subs := eval_clauses(kb, r.body);

  if |subs| == 0 {
    return;
  }

  var i := 0;
  ghost var step := ProofStep(subs[i], r, kb');
  var new_fact := substitute(r.head, subs[i]);    
  //print "\tFound a new fact: ", new_fact, "\n";
  ghost var old_kb' := kb';
  kb' := kb' + [new_fact];    
        
  lemma_valid_proof_step(step);
  assert step.valid();
  proof' := proof' + [step];  
}

method immediate_consequence(prog:Program, kb:KnowledgeBase, ghost proof:Proof)
  returns (kb':KnowledgeBase, ghost proof':Proof)
  requires valid_program(prog)
  requires valid_partial_proof(prog, proof)
  requires |kb| > 0 && |proof| > 0 
  requires Last(kb) == Last(proof).new_fact()
  requires Last(proof).facts == DropLast(kb)
  ensures valid_partial_proof(prog, proof')
  ensures |kb'| > 0 && |proof'| > 0 
  ensures Last(kb') == Last(proof').new_fact()
  ensures Last(proof').facts == DropLast(kb')
{
  kb' := kb;
  proof' := proof;
  for i := 0 to |prog| 
    invariant |kb'| > 0 && |proof'| > 0 
    invariant valid_partial_proof(prog, proof')
    invariant Last(kb') == Last(proof').new_fact()
    invariant Last(proof').facts == DropLast(kb')
  {
    kb', proof' := eval_rule(prog, kb', prog[i], proof');  
  }
}

method solve(prog:Program, kb:KnowledgeBase, ghost proof:Proof) returns (kb':KnowledgeBase, ghost proof':Proof)
  requires valid_program(prog)
  requires valid_partial_proof(prog, proof)
  requires |kb| > 0 && |proof| > 0 
  requires Last(kb) == Last(proof).new_fact()
  requires Last(proof).facts == DropLast(kb)
  ensures valid_partial_proof(prog, proof')
  ensures |kb'| > 0 && |proof'| > 0 
  ensures Last(kb') == Last(proof').new_fact()
  ensures Last(proof').facts == DropLast(kb')
{
  kb' := kb;
  proof' := proof;
  var count := 4294967295;  // Cheap hack to avoid proving termination
  while count > 0 
    invariant valid_partial_proof(prog, proof')
    invariant |kb'| > 0 && |proof'| > 0 
    invariant Last(kb') == Last(proof').new_fact()
    invariant Last(proof').facts == DropLast(kb')
  {
    var old_kb' := kb';
    kb', proof' := immediate_consequence(prog, old_kb', proof');
    //print "New |kb| = ", |kb'|, "\n";
    if |kb'| == |old_kb'| {
      return kb', proof';
    }
    count := count - 1;
  }
}


// Checks if any fact can satisfy the query
method query(prog:Program, query:Rule) returns (b:bool, ghost proof:Proof)
  requires valid_program(prog)
  requires valid_rule(query)
{
  kb, partial_proof := solve(prog, kb, partial_proof);  
  var new_kb;
  new_kb, partial_proof := eval_query_once(prog, kb, query, partial_proof);

  if |new_kb| > |kb| {
    proof := partial_proof;
    print "Query succeeded!\n";
    b := true;
    return;
  } else {
    print "Query failed.  Sorry!\n";
    b := false;
    return;
  }
}

