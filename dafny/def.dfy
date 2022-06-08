// Used by spec
include "std-lib/src/Collections/Sequences/Seq.dfy"
// Used by impl
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Sets/Sets.dfy"
import opened Seq
import opened Sets
import opened Wrappers

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


datatype ProofStep = ProofStep(sub:Substitution, rule:Rule, facts:set<Fact>)
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

predicate valid_proof(prog:Program, facts:set<Fact>, query:Rule, proof:Proof)
{
  && |proof| > 0
  // We start with the base set of facts
  && First(proof).facts == facts
  // Each proof step is valid and uses a rule from the program
  && (forall i :: 0 <= i < |proof| ==> proof[i].valid() && proof[i].rule in prog)
  // Each proof step extends the set of facts by one
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i+1].facts == proof[i].facts + { proof[i].new_fact() } )
  // Last proof step shows the query is valid
  && Last(proof).rule == query
}

predicate valid_query(prog:Program, facts:set<Fact>, query:Rule)
{
  exists proof :: valid_proof(prog, facts, query, proof)
}

////////////////////////////////////////
// Model-Theoretic Spec
////////////////////////////////////////

// Needed below to satisfy Dafny's type checker
function clause_to_fact(c:Clause) : Fact
  requires c.is_ground()
{
  c
}

function base_facts(prog:Program) : set<Fact>
{
  set r | r in prog && |r.body| == 0 && r.head.is_ground() :: clause_to_fact(r.head)
}

type Interpretation = set<Fact>

predicate substitution_complete_for_rule(sub:Substitution, r:Rule)
{
  && r.head.substitution_complete(sub)
  && (forall i :: 0 <= i < |r.body| ==> r.body[i].substitution_complete(sub))
}

function ground_rule_body(sub:Substitution, r:Rule) : set<Fact>
  requires substitution_complete_for_rule(sub, r)
{
  set clause | clause in r.body :: clause.make_fact(sub)
}

predicate rule_true_in_interp(interp:Interpretation, r:Rule)
{
  forall sub ::
    // substitution must include all of the variables in the rule
    substitution_complete_for_rule(sub, r) 
    // facts produced from the body are in the interpretation
    && ground_rule_body(sub, r) <= interp
    // then the head must be in the interpretation as well
    ==> r.head.make_fact(sub) in interp
}

predicate is_model(interp:Interpretation, prog:Program)
{
  && base_facts(prog) <= interp
  && (forall i :: 0 <= i < |prog| ==> rule_true_in_interp(interp, prog[i]))
}

predicate is_min_model(interp:Interpretation, prog:Program)
{
  && is_model(interp, prog)
  && (forall interp' :: interp != interp && is_model(interp', prog) ==> |interp| <= |interp'|)
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
/*
function clauses_vars(clauses:seq<Clause>) : set<VarTerm>
{
  set i | 0 <= i < |clauses| && clauses[i].Var? :: clauses
}
*/
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

predicate valid_partial_proof(prog:Program, facts:set<Fact>, proof:Proof)
{
  |proof| > 0 ==>
  // We start with the base set of facts
  && First(proof).facts == facts
  // Each proof step is valid and uses a rule from the program
  && (forall i :: 0 <= i < |proof| ==> proof[i].valid() && proof[i].rule in prog)
  // Each proof step extends the set of facts by one
  && (forall i :: 0 <= i < |proof| - 1 ==> proof[i+1].facts == proof[i].facts + { proof[i].new_fact() } )
}

lemma lemma_valid_proof_step(step:ProofStep)
  requires valid_rule(step.rule)
  requires forall j :: 0 <= j < |step.rule.body| ==>                 
                 step.rule.body[j].substitution_complete(step.sub)
              && step.rule.body[j].make_fact(step.sub) in step.facts
  ensures step.valid()
{  
}

method eval_rule(kb:KnowledgeBase, r:Rule) returns (kb':KnowledgeBase, ghost proof:Proof)
  requires valid_rule(r)
  ensures |proof| == |kb'|
  ensures forall j :: 0 <= j < |proof| ==> 
              proof[j].valid() && proof[j].rule == r && proof[j].facts == ToSet(kb)
  ensures forall j :: 0 <= j < |kb'| ==>  kb'[j] == proof[j].rule.head.make_fact(proof[j].sub)
{
  proof := [];
  //print "Evaluating rule: ", r, "\n";
  if |r.body| == 0 {
    return [r.head], [ProofStep(map[], r, ToSet(kb))];
  }

  kb' := [];

  var subs := eval_clauses(kb, r.body);
  //print "\teval_clauses returned: ", subs, "\n";
  for i := 0 to |subs| 
    invariant |proof| == |kb'| == i
    invariant forall j :: 0 <= j < |proof| ==> 
              proof[j].valid() && proof[j].rule == r && proof[j].facts == ToSet(kb)
    invariant forall j :: 0 <= j < i ==>  kb'[j] == proof[j].rule.head.make_fact(proof[j].sub)       
  {
    var new_fact := substitute(r.head, subs[i]);
    //print "\tFound a new fact: ", new_fact, "\n";
    ghost var step := ProofStep(subs[i], r, ToSet(kb));  
    assert forall f :: f in kb ==> f in ToSet(kb) by { reveal ToSet(); }    
    lemma_valid_proof_step(step);
    assert step.valid();
    proof := proof + [step];
    kb' := kb' + [new_fact];
  }
}

// TODO: Migrate this to std-lib
method LemmaHasNoDuplicatesExtend<T>(s:seq<T>, elt:T)
  requires HasNoDuplicates(s)
  requires elt !in ToSet(s)
  ensures  HasNoDuplicates([elt]+s)
  ensures  ToSet([elt] + s) == ToSet(s) + {elt}
{
  reveal ToSet();
  reveal HasNoDuplicates();
}

// TODO: Migrate this to std-lib
method SetToSeq<T>(s:set<T>) returns (q:seq<T>)
  ensures HasNoDuplicates(q)
  ensures |q| == |s|
  ensures ToSet(q) == s
{
  q := [];
  var subset := s;
  LemmaCardinalityOfEmptySetIs0(q);
  LemmaNoDuplicatesCardinalityOfSet(q);
  while (subset != {}) 
    invariant ToSet(q) * subset == {}
    invariant ToSet(q) + subset == s
    invariant HasNoDuplicates(q)
  {
    var elt :| elt in subset;
    assert elt !in ToSet(q);
    LemmaHasNoDuplicatesExtend(q, elt);
    q := [elt] + q;    
    subset := subset - {elt};
  }
  assert ToSet(q) == s;
  LemmaCardinalityOfSetNoDuplicates(q);
}

method merge(kb0:KnowledgeBase, kb1:KnowledgeBase) returns (kb':KnowledgeBase)
  requires HasNoDuplicates(kb0)
  ensures HasNoDuplicates(kb')
  ensures |kb'| >= |kb0|
  ensures ToSet(kb') == ToSet(kb0) + ToSet(kb1)
{
  var s0 := ToSet(kb0);
  var s1 := ToSet(kb1);
  LemmaCardinalityOfSetNoDuplicates(kb0);
  var union := s0 + s1;
  assert |s0| == |kb0|;
  LemmaUnionSize(s0, s1);
  assert |union| >= |s0|;
  kb' := SetToSeq(union);
}

ghost method merge_proofs(prog:Program, initial_facts:set<Fact>, proof:Proof, proof_steps:Proof, old_kb:KnowledgeBase, new_kb:KnowledgeBase) 
  returns (proof':Proof)
  requires valid_partial_proof(prog, initial_facts, proof)
  requires |proof| > 0 ==> Last(proof).facts == ToSet(old_kb);
  requires |proof_steps| == |new_kb|
  requires forall j :: 0 <= j < |proof_steps| ==> 
              proof_steps[j].valid() && proof_steps[j].rule in prog && proof_steps[j].facts == ToSet(old_kb)
  requires forall j :: 0 <= j < |new_kb| ==>  new_kb[j] == proof_steps[j].rule.head.make_fact(proof_steps[j].sub)
  //ensures |proof'| > |proof|
  ensures |proof'| > 0 ==> Last(proof').facts == ToSet(old_kb) + ToSet(new_kb)
  ensures valid_partial_proof(prog, initial_facts, proof')
{
  proof' := proof;
  LemmaCardinalityOfEmptySetIs0(new_kb[..0]);
  for i := 0 to |proof_steps|
    invariant First(proof').facts == initial_facts;
    invariant valid_partial_proof(prog, initial_facts, proof')
    invariant |proof'| > 0 ==> Last(proof').facts == ToSet(old_kb) + ToSet(new_kb[..i]);
  {
    var new_step := ProofStep(proof_steps[i].sub, proof_steps[i].rule, proof_steps[i].facts + { new_kb[i] });
    assert new_step.valid();
    proof' := proof' + [new_step];
    assert First(proof').facts == initial_facts;
    assert forall i :: 0 <= i < |proof'| ==> proof'[i].valid() && proof'[i].rule in prog;
    assert forall i :: 0 <= i < |proof'| - 1 ==> proof'[i+1].facts == proof'[i].facts + { proof'[i].new_fact() };

  }
  assume false;
}
/*
method immediate_consequence(prog:Program, kb:KnowledgeBase, ghost initial_facts:set<Fact>, ghost proof:Proof)
  returns (kb':KnowledgeBase, ghost proof':Proof)
  requires valid_program(prog)
  requires HasNoDuplicates(kb)
  requires valid_partial_proof(prog, initial_facts, proof)
  requires |proof| > 0 ==> Last(proof).facts == ToSet(kb)
  ensures HasNoDuplicates(kb')
  ensures |kb'| >= |kb|
  ensures valid_partial_proof(prog, initial_facts, proof')
  ensures |proof'| > 0 ==> Last(proof').facts == ToSet(kb')
{
  kb' := kb;
  proof' := proof;
  for i := 0 to |prog| 
    invariant HasNoDuplicates(kb')
    invariant |kb'| >= |kb|
    invariant valid_partial_proof(prog, initial_facts, proof')
    invariant |proof'| > 0 ==> Last(proof').facts == ToSet(kb')
  {
    var new_kb, proof_steps := eval_rule(kb', prog[i]);
    proof' := merge_proofs(prog, initial_facts, proof', proof_steps, kb', new_kb);    
    kb' := merge(kb', new_kb);    
  }
}

method solve(prog:Program) returns (kb:KnowledgeBase, ghost proof:Proof)
  requires valid_program(prog)
  ensures valid_partial_proof(prog, ToSet([]), proof)
  ensures |proof| > 0 ==> Last(proof).facts == ToSet(kb)
{
  kb := [];
  proof := [];
  LemmaCardinalityOfEmptySetIs0(kb);  
  LemmaNoDuplicatesCardinalityOfSet(kb);
  var count := 4294967295;  // Cheap hack to avoid proving termination
  while count > 0 
    invariant HasNoDuplicates(kb)
    invariant valid_partial_proof(prog, ToSet([]), proof)
    invariant |proof| > 0 ==> Last(proof).facts == ToSet(kb)
  {
    var old_kb := kb;
    kb, proof := immediate_consequence(prog, old_kb, ToSet([]), proof);
    if |kb| == |old_kb| {
      return kb, proof;
    }
    count := count - 1;
  }
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

method check_rule(r:Rule) returns (b:bool)
  ensures b == valid_rule(r)
{
  if |r.body| == 0 {
    b := clause_is_ground(r.head);
  } else {
      for i := 0 to |r.head.terms| 
        invariant forall j :: 0 <= j < i ==> (r.head.terms[j].Var? ==> match_exists(r.head.terms[j], r.body))
      {
        var term := r.head.terms[i];
        if term.Var? {
          var b := find_var(term, r.body);
          if !b {
            return false;
          }
        }
      }
      return true;
  }
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

// Checks if any fact can satisfy the query
method query(prog:Program, query:Rule)
  requires valid_program(prog)
  requires valid_rule(query)
{  
  var kb, partial_proof := solve(prog);
  assert valid_partial_proof(prog, ToSet([]), partial_proof);
  var new_kb, proof_steps := eval_rule(kb, query);
  assume false;
  var proof := merge_proofs(prog, ToSet([]), partial_proof, proof_steps, kb, new_kb);    
  //kb' := merge(kb', new_kb);
  if |new_kb| > 0 {
    assert valid_proof(prog, ToSet([]), query, proof);
  }
  
  print "Done\n";
}

// Finds all facts derivable from the query
method query_all(prog:Program, query:Rule)
  requires valid_program(prog)
  requires valid_rule(query)
{  
  var kb, proof := solve(prog + [query]);
  //if ? {
  //  assert valid_proof(prog, ToSet([]), query, proof);
  //}
  print "Results:\n";
  for i := 0 to |kb| {
    //print kb[i], "\n";
    if kb[i].name == query.head.name {
      //return kb[i];
      print kb[i], "\n";
    }
  }
  print "Done\n";
}

method run(raw_prog:Program)
  requires |raw_prog| > 0
{
  var prog := DropLast(raw_prog);
  var q := Last(raw_prog);
  //print "Program is: ", prog, "\n";
  //print "Query is: ", q, "\n";
  var valid_prog := check_program(prog);
  var valid_query := check_rule(q);
  if valid_prog && valid_query {
    query_all(prog, q);  
  } else {
    print "Sorry, that's an invalid program and/or query\n";
  }
}

/*
method Main() {
  var f1 := Rule(Clause("node", [Const("x")]), []);
  var f2 := Rule(Clause("node", [Const("y")]), []);
  var f3 := Rule(Clause("node", [Const("z")]), []);

  var e1 := Rule(Clause("edge", [Const("x"), Const("y")]), []);
  var e2 := Rule(Clause("edge", [Const("y"), Const("z")]), []);  

  var r1 := Rule(Clause("connected", [Var("A"), Var("A")]), [Clause("node", [Var("A")])]);
  //var r1 := Rule(Clause("connected", [Var("A"), Var("B")]), [Clause("edge", [Var("A"), Var("B")])]);
  var r2 := Rule(Clause("connected", [Var("A"), Var("B")]), [Clause("connected", [Var("A"), Var("M")]), Clause("edge", [Var("M"), Var("B")])]);

  var prog := [f1, f2, f3, e1, e2, r1, r2];
  var q := Rule(Clause("query", [Var("W")]), [Clause("connected", [Const("x"), Var("W")])]);
  run(prog, q);
}
*/*/