include "definitions.dfy"
include "evar.dfy"
include "search_clause.dfy"
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Sequences/Seq.dfy"
import opened Wrappers
import opened Seq

/*

Search procedure:

global evar_map

search(goal: SearchClause) returns (ghost proof: Option<ProofTree>, b: bool)
  ensures b == True <==> (proof == Some(proof') && proof'.valid())
{
  // goal: R(arg1, arg2, ..., argN): where the args are evars in the evar_map
  rules <- all rules with heads of the form R(arg1, arg2, ..., argN)
  for rule in rules:
    match unify(rule.Head, goal) with
    | None => continue; // can't instantiate this rule due to conflicted ground terms
    | Some(subst) =>
      // subst is a map<var --> evar>
      substitutedBody: seq<SearchClause> = evarify(rule.Body, subst);
      for searchClause: SearchClause in substitutedBody:
        search(searchClause)
}

*/

method find_matching_rules(rules: seq<Rule>, goal:SearchClause) returns (c:seq<Rule>)
    ensures forall r:Rule :: r in c ==> r.head.name == goal.name && |r.head.terms| == |goal.evar_terms|
    ensures forall r:Rule :: r in c ==> r.head == goal.clause
    ensures forall r:Rule :: r in c ==> r in rules
{
    var matching_rules : seq<Rule> := [];
    
    for i := 0 to |rules|
        invariant forall r:Rule :: r in matching_rules ==> r.head.name == goal.name && |r.head.terms| == |goal.evar_terms|
        invariant forall r:Rule :: r in matching_rules ==> r in rules
    {
        var rule := rules[i];
        if (rule.head.name == goal.name && |rule.head.terms| == |goal.evar_terms|) {
            matching_rules := matching_rules + [rule];
        }
    }
    // TODO postcondition on goal.clause, based on bijective map stuff
    return matching_rules;
}


method unify(head_clause:Clause, goal:SearchClause, emap:EvarMap) returns (o:Option<EvarSubstitution>)//, e:EvarMap)
    requires emap.inv()
    requires |head_clause.terms| == |goal.evar_terms|
    requires goal.valid()
    requires goal.valid_emap(emap)
    modifies emap
    ensures emap.is_more_resolved()
    ensures goal.valid_emap(emap)
    ensures emap.inv()
    ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    ensures o.Some? ==> forall v :: v in goal.clause.terms && v.Var? ==> v in o.value
    ensures head_clause.is_ground() && o.Some? ==> goal.emap_fully_resolved(emap)
    ensures emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
{
    // check if all terms in clause have correct mapping in goal.evar_terms
    var subst:EvarSubstitution := map[];
    for i := 0 to |head_clause.terms| 
        invariant emap.inv()
        invariant goal.valid_emap(emap)
        invariant forall e :: e in subst.Values ==> e in emap.evar_map
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
        invariant emap.is_more_resolved()
        invariant forall j :: 0 <= j < i ==> head_clause.terms[j].Const? ==> emap.evar_map[goal.evar_terms[j]].Some?
    {
        if head_clause.terms[i].Var? {
            //print "a";
            var variableName := head_clause.terms[i].s;
            subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
        } else if head_clause.terms[i].Const? {
            //print "b";
            var constant := head_clause.terms[i].c;
            var e := emap.lookup(goal.evar_terms[i]);
            match e {
                case None => {
                    emap.resolve(goal.evar_terms[i], constant);
                }
                case Some(constant') =>
                    if constant != constant' {
                        // ignore rule
                        return None;
                    }
                    // } else {
                    //     subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
                    // }
            }
        }
    }
    reveal ToSet();
    return Some(subst);
}

method evarify(clause:Clause, subst:EvarSubstitution, emap:EvarMap) 
    returns (sc:SearchClause, subst':EvarSubstitution)
    requires emap.inv()
    requires forall e :: e in subst.Values ==> e in emap.evar_map
    modifies emap
    ensures  emap.inv()
    ensures  sc.valid_emap(emap)
    ensures  forall e :: e in subst'.Values ==> e in emap.evar_map
    ensures  emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    ensures  forall s :: s in subst ==> s in subst'
    ensures  sc.clause == clause
    ensures  sc.clause.substitution_complete(make_subst(emap, subst'))
    ensures  sc.valid()
{
    subst' := subst;
    var local_subst:EvarSubstitution := map[];
    var evar_terms:seq<Evar> := [];
    reveal ToSet();
    for i := 0 to |clause.terms|
        invariant emap.inv()
        invariant forall e :: e in evar_terms ==> e in emap.evar_map
        invariant forall e :: e in subst'.Values ==> e in emap.evar_map
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map 
        invariant forall s :: s in subst ==> s in subst'
        invariant forall j :: 0 <= j < i ==> clause.terms[j].Var? ==> clause.terms[j] in subst'
        invariant forall e :: e in local_subst.Values ==> e in evar_terms
    {
        var term := clause.terms[i];
        match term {
            case Var(s) => {
                if term in subst'.Keys {
                    var ev := subst'[term]; // this should imply ev in emap.evar_map
                    evar_terms := evar_terms + [ev];
                    local_subst := local_subst[term := ev];
                } else if term !in subst' {
                    var new_ev := emap.get_new_evar();
                    evar_terms := evar_terms + [new_ev];
                    subst' := subst'[term := new_ev];
                    local_subst := local_subst[term := new_ev];
                }
            }
            case Const(c) => {
                var new_ev := emap.get_new_evar();
                evar_terms := evar_terms + [new_ev];
                emap.resolve(new_ev, c);
            }
        }
    }

    sc := SearchClause(clause.name, evar_terms, clause, local_subst);
}

method search (rules:seq<Rule>, goal:SearchClause, emap:EvarMap, depth: nat) returns (b:bool, ghost proof: Option<Proof>)//, e:EvarMap)
    requires valid_program(rules)
    requires emap.inv()
    requires goal.valid_emap(emap)
    requires goal.valid()
    // ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    modifies emap
    ensures emap.inv()
    ensures goal.valid_emap(emap) // TODO: Do we need to prove this at all times?
    ensures emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    ensures b ==> proof.Some? && valid_proof(rules, goal.clause, proof.value)
    ensures b ==> goal.emap_fully_resolved(emap)
    decreases depth
    // what the correct matching rule is (rule for which we returned true)
    //   - maybe return a sequence of these rules
    //   - build a 'substitution' map like Bryan using these rules
    //       - a substitution is either a variable->evar or evar->const(resolve)
    //   - ??
    //   - reuse Bryan's spec
    // ensures b ==> that rule works

    // the different subst bi-maps are consistent // WRONG
    // we should somehow say b==true ==> at no point we made the same evar resolve to two diff consts
    // for each subst (at each instantiation of a rule down the tree), convert that subst into Bryan's substitution (using the 'global' evarmap)
    //  -- keep a ghost state of seq<subst * rule> or a seq<applied_rules> * seq<subst for that rule>?
    //  -- (var -> evar -> const) ==> (var -> const) like Bryan's substitution (a ground substitution)
    //  -- do the above for ALL evars in our evarmap, the one for which search returns true (basically for all evars we want them to be present in substs)
    //  --   at each proofstep, the number of evars for which the above stuff is not done decreases
    // prove completeness of our substs? - we get a valid ProofStep for free?
{
    if (depth == 0) {
        return false, None;
    }
    //print "Searching on ", goal, " with emap ", emap.evar_map, "\n";
    // find all rules that match current goal
    var matching_rules := find_matching_rules(rules, goal);
    //print "\t matching_rules = ", matching_rules, "\n";

    // for all rules that match the current goal
    for i := 0 to |matching_rules|
        invariant emap.inv()
        // invariant goal.valid_emap(emap)
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    {
        //print "\t i = ", i, "\n"; 
        var current_emap:EvarMap := new EvarMap.Init(emap); // TODO: Check if this actually makes a copy
        var rule:Rule := matching_rules[i];
        //print "\t matching_rule = ", rule, "\n";
        var option_subst := unify(rule.head, goal, emap);
        
        //print "\t option_subst = ", option_subst, "\n";
        
        var subst : EvarSubstitution;
        match option_subst {
            case None => continue;
            case Some(subst') => subst := subst';
        }

        var search_clauses:seq<SearchClause> := [];
        if |rule.body| == 0 {
            var concreteSubst := make_subst(emap, subst);
            var proofStep := ProofStep(concreteSubst, rule, []);
            assert rule in rules; // needed to use valid_program(rules) to conclude that valid_rule(rule) and then conclude that rule.head.is_ground() 
            return true, Some([proofStep]);
        } else {
            for j := 0 to |rule.body|
                invariant |search_clauses| == j
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant current_emap.evar_map == old(current_emap.evar_map)
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                invariant forall e :: e in subst.Values ==> e in emap.evar_map
                invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
                invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                invariant forall i :: 0 <= i < j ==> rule.body[i] == search_clauses[i].clause;
                invariant forall i :: 0 <= i < j ==> search_clauses[i].clause.substitution_complete(make_subst(emap, subst))
                invariant forall i :: 0 <= i < j ==> search_clauses[i].valid()
            {
                var clause:Clause := rule.body[j];
                var search_clause, subst' := evarify(clause, subst, emap);
                subst := subst';
                search_clauses := search_clauses + [search_clause];
            }
            var flag := true;
            ghost var proofs : seq<Proof> := [];
            assert forall i :: 0 <= i < |search_clauses| ==> search_clauses[i].clause.substitution_complete(make_subst(emap, subst));
            for j := 0 to |search_clauses|
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant current_emap == old(current_emap)
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                // invariant forall e :: e in subst.Values ==> e in emap.evar_map
                invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
                invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                // invariant goal.valid_emap(emap)
                invariant flag ==> (|proofs| == j)
                invariant flag ==> (forall i :: 0 <= i < j ==> valid_proof(rules, search_clauses[i].clause, proofs[i]))
                invariant flag ==> forall i :: 0 <= i < j ==> search_clauses[i].clause.make_fact(make_subst(emap, subst)) == Last(proofs[i]).new_fact();
                invariant forall e :: e in subst.Values ==> e in emap.evar_map
            {
                var b',proof_j := search(rules, search_clauses[j], emap, depth - 1);
                if !b' {
                    flag := false;
                    break;
                } else {
                    proofs := proofs + [proof_j.value];
                }
                // current_emap := e;
            }
            if flag {
                var concreteSubst := make_subst(emap, subst);
                assert |proofs| == |search_clauses| == |rule.body|;
                assert forall i :: 0 <= i < |rule.body| ==> search_clauses[i].valid_emap(emap);
                assume forall i :: 0 <= i < |rule.body| ==> search_clauses[i].emap_fully_resolved(emap); // TODO This will depend on some range restriction reasoning
                assert forall i :: 0 <= i < |rule.body| ==> rule.body[i] == search_clauses[i].clause;
                assert forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, search_clauses[i].clause, proofs[i]);
                assert forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, rule.body[i], proofs[i]);
                assert forall i :: 0 <= i < |rule.body| ==> rule.body[i].make_fact(concreteSubst) == Last(proofs[i]).new_fact();
                var proof := combine_proofs(rules, rule, concreteSubst, proofs);
                return true, Some(proof);
            }
        }
        emap.copy(current_emap);
    }
    return false, None;
}

ghost method flatten_two_proofs(rules: seq<Rule>, subst: Substitution, goal1: Clause, proof1: Proof, goal2: Clause, proof2: Proof) returns (proof: Proof)
    requires valid_proof(rules, goal1, proof1)
    requires valid_proof(rules, goal2, proof2)
    requires goal1.substitution_concrete(subst)
    requires goal1.make_fact(subst) == Last(proof1).new_fact()
    requires goal2.substitution_concrete(subst)
    requires goal2.make_fact(subst) == Last(proof2).new_fact()
    ensures  valid_proof(rules, goal1, proof)
    ensures  goal1.make_fact(subst) == Last(proof).new_fact()
    ensures  goal2.make_fact(subst) in Last(proof).facts
    ensures  forall f :: f in Last(proof1).facts ==> f in Last(proof).facts
    ensures  forall f :: f in Last(proof2).facts ==> f in Last(proof).facts
{
    var proof2_facts := Last(proof2).facts + [ Last(proof2).new_fact() ];
    proof := proof2;
    assert valid_proof(rules, goal2, proof);
    assert forall j :: 0 <= j < |proof| ==> proof[j].rule in rules;
    assert forall j :: 1 <= j < |proof| ==> proof[j].facts == proof[j-1].facts + [ proof[j-1].new_fact() ] ;
    for i := 0 to |proof1|
        invariant |proof| == |proof2| + i
        invariant proof[..|proof2|] == proof2
        invariant forall j :: 0 <= j < |proof| ==> proof[j].valid()
        invariant forall j :: 0 <= j < |proof| ==> proof[j].rule in rules
        invariant forall j :: 0 <= j < i ==> proof[|proof2| + j].facts == proof2_facts + proof1[j].facts
        invariant forall j :: 0 <= j < i ==> proof1[j].new_fact() == proof[|proof2| + j].new_fact();
        invariant forall j :: 1 <= j < |proof| ==> proof[j].facts == proof[j-1].facts + [ proof[j-1].new_fact() ] 
        invariant forall j :: 0 <= j < i ==> proof[|proof2| + j].rule == proof1[j].rule
    {
        var proof_i_facts := proof2_facts + proof1[i].facts;
        assert i > 0 ==> proof1[i].facts == proof1[i-1].facts + [ proof1[i-1].new_fact() ];        
        proof := proof + [ProofStep(proof1[i].sub, proof1[i].rule, proof_i_facts)];
    }
}

ghost method combine_proofs(rules: seq<Rule>, rule: Rule, subst: Substitution, proofs: seq<Proof>) returns (proof: Proof)
    requires |rule.body| == |proofs| >= 1
    requires rule in rules
    requires forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, rule.body[i], proofs[i])
    requires rule.head.substitution_concrete(subst)
    requires forall i :: 0 <= i < |rule.body| ==> rule.body[i].substitution_concrete(subst) && rule.body[i].make_fact(subst) == Last(proofs[i]).new_fact();
    ensures  valid_proof(rules, rule.head, proof)
{
    proof := proofs[0];
    var goal := rule.body[0];
    for i := 1 to |proofs|
        invariant valid_proof(rules, goal, proof)
        invariant goal.substitution_concrete(subst)
        invariant goal.make_fact(subst) == Last(proof).new_fact()
        invariant goal == rule.body[i-1]
        invariant forall j :: 0 <= j < |proof| ==> proof[j].valid()
        invariant forall j :: 0 <= j < i - 1 ==> rule.body[j].make_fact(subst) in Last(proof).facts
    {
        var new_proof := flatten_two_proofs(rules, subst, rule.body[i], proofs[i], goal, proof);
        proof := new_proof;
        goal := rule.body[i];
    }
    var last_step := ProofStep(subst, rule, Last(proof).facts + [ Last(proof).new_fact() ]);
    proof := proof + [last_step];
}

method get_query_search_clause(query:Clause, emap:EvarMap) returns (sc:SearchClause)
    requires emap.inv()
    modifies emap
    ensures emap.inv()
    ensures sc.valid_emap(emap)
    ensures sc.clause == query
    ensures sc.valid()
{
    var evar_terms:seq<Evar> := [];
    var subst: EvarSubstitution := map[];
    for i := 0 to |query.terms|
        invariant emap.inv()
        invariant forall e:Evar :: e in evar_terms ==> e in emap.evar_map
        invariant forall e:Evar :: e in subst.Values ==> e in emap.evar_map
        invariant forall e:Evar :: e in subst.Values ==> e in evar_terms
    {
        var term := query.terms[i];
        match term {
            case Var(s) => {
                        var new_ev := emap.get_new_evar();
                        evar_terms := evar_terms + [new_ev];
                        subst := subst[term := new_ev];
                    }
            case Const(c) => {} // TODO: Create new evars and map them to the const?
        }
    }

    reveal ToSet();
    sc := SearchClause(query.name, evar_terms, query, subst);
}

method run_datalog(p:Program)
    requires |p| > 0
{
    var prog := p;
    var program_ok := check_program(prog);
    if program_ok {
        var query_rule := Last(p);
        var emap:EvarMap := new EvarMap();
        var query_sc:SearchClause := get_query_search_clause(query_rule.head, emap);
        var b,proof := search(prog, query_sc, emap, 0x1_0000_0000);
        assert (b == true ==> valid_query(prog, query_rule.head));
        print "Query returned ", b, "\n";
    } else {
        print "Invalid or unsupported datalog program";
    }
}