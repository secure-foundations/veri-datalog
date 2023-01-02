include "definitions.dfy"
include "evar.dfy"
include "search_clause.dfy"
include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Sequences/Seq.dfy"
import opened Wrappers
import opened Seq

method find_matching_rules(rules: seq<Rule>, goal:SearchClause) returns (c:seq<Rule>)
    requires valid_program(rules)
    ensures forall r:Rule :: r in c ==> r.head.name == goal.name && |r.head.terms| == |goal.evar_terms|
    // ensures forall r:Rule :: r in c ==> r.head == goal.clause
    ensures forall r:Rule :: r in c ==> r in rules && valid_rule(r)
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
    return matching_rules;
}

method unify(head_clause:Clause, goal:SearchClause, emap:EvarMap) returns (o:Option<EvarSubstitution>)//, e:EvarMap)
    requires emap.inv()
    requires valid_clause(head_clause)
    requires |head_clause.terms| == |goal.evar_terms|
    requires goal.valid()
    requires goal.valid_emap(emap)
    requires goal.name == head_clause.name
    modifies emap
    ensures emap.is_more_resolved()
    ensures goal.valid_emap(emap)
    ensures emap.inv()
    ensures o.Some? ==> o.value.valid()
    // ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    ensures o.Some? ==> forall e :: o.value.in2(e) ==> e in emap.evar_map
    // ensures o.Some? ==> forall v :: v in goal.clause.terms && v.Var? ==> o.value.in1(v) // IS WRONG
    ensures o.Some? ==> forall v :: v in head_clause.terms ==> o.value.in1(v)
    ensures head_clause.is_ground() && o.Some? ==> goal.emap_fully_resolved(emap) // o.value is empty map
    ensures head_clause.is_ground() && o.Some? ==> goal.clause.make_fact(make_subst(emap, goal.subst)) == head_clause
    // ensures o.Some? ==> goal.clause.make_fact(make_subst(emap,goal.subst)) == head_clause.make_fact(make_subst(emap,o.value))
    ensures emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    ensures o.Some? ==> forall i:nat | i < |head_clause.terms| :: o.value.get1(head_clause.terms[i]) == goal.evar_terms[i]
    // ensures forall v :: goal.subst.in1(v) && v.Var? && o.Some? ==> o.value.in1(v) && goal.subst.get1(v) == o.value.get1(v)
    // ensures o.Some? ==> forall i:nat | i < |head_clause.terms| ::
    //                       (if head_clause.terms[i].Var? then o.value.get1(head_clause.terms[i]) == goal.evar_terms[i]
    //                       else emap.evar_map[goal.evar_terms[i]].Some?)
    ensures o.Some? ==> forall j :: 0 <= j < |head_clause.terms| ==> head_clause.terms[j].Const? ==> emap.evar_map[goal.evar_terms[j]].Some? && Const(emap.evar_map[goal.evar_terms[j]].value) == head_clause.terms[j]
    // |goal.evar_terms| == |o.value.Values| // is this true?
    
{
    // check if all terms in clause have correct mapping in goal.evar_terms
    var subst:EvarSubstitution := new_bijective_map<VarTerm, Evar>();
    for i := 0 to |head_clause.terms|
        invariant emap.inv()
        invariant subst.valid()
        invariant goal.valid()
        invariant goal.valid_emap(emap)
        invariant forall e :: subst.in2(e) ==> e in emap.evar_map
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
        invariant emap.is_more_resolved()
        invariant forall j :: 0 <= j < i ==> subst.in1(head_clause.terms[j]) && subst.get1(head_clause.terms[j]) == goal.evar_terms[j]
        // invariant forall j:nat | j < i && head_clause.terms[j].Var? :: subst.get1(head_clause.terms[j]) == goal.evar_terms[j]
        invariant forall j :: 0 <= j < i ==> head_clause.terms[j].Const? ==> emap.evar_map[goal.evar_terms[j]].Some? && Const(emap.evar_map[goal.evar_terms[j]].value) == head_clause.terms[j]
        invariant forall j :: i <= j < |head_clause.terms| ==> !subst.in1(head_clause.terms[j])
        invariant forall j :: i <= j < |goal.evar_terms| ==> !subst.in2(goal.evar_terms[j])
        // invariant forall j:nat | j < i :: goal.subst.in1(goal.clause.terms[i]) && goal.clause.terms[i].Var? ==> subst.in1(goal.clause.terms[i]) && goal.subst.get1(goal.clause.terms[i]) == subst.get1(head_clause.terms[i])
        // invariant head_clause.is_ground() ==> forall j:nat :: j < i ==> goal.clause.make_fact(make_subst(emap, goal.subst)).terms[j] == head_clause.terms[j]
    {
        if head_clause.terms[i].Var? {
            //print "a";
            var variableName := head_clause.terms[i].s;
            // subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
            subst := subst.insert(head_clause.terms[i], goal.evar_terms[i]);
        } else if head_clause.terms[i].Const? {
            //print "b";
            var constant := head_clause.terms[i].c;
            var e := emap.lookup(goal.evar_terms[i]);
            match e {
                case None => {
                    subst := subst.insert(head_clause.terms[i], goal.evar_terms[i]);
                    emap.resolve(goal.evar_terms[i], constant);
                }
                case Some(constant') =>
                    if constant != constant' {
                        // ignore rule
                        return None;
                    }
                    else {
                        subst := subst.insert(head_clause.terms[i], goal.evar_terms[i]);
                    }
            }
        }
    }
    reveal ToSet();
    // assert(head_clause.is_ground() ==> forall i:nat :: i < |goal.clause.terms| ==> make_subst(emap, goal.subst)[goal.clause.terms[i]].c == emap.evar_map[goal.evar_terms[i]].value);
    // assert(head_clause.is_ground() ==> forall i:nat :: i < |goal.clause.terms| ==> make_subst(emap, goal.subst)[goal.clause.terms[i]] == goal.clause.make_fact(make_subst(emap, goal.subst)).terms[i]);
    // assert(head_clause.is_ground() ==> forall i:nat :: i < |goal.clause.terms| ==> goal.clause.make_fact(make_subst(emap, goal.subst)).terms[i] == head_clause.terms[i]);
    return Some(subst);
}

method evarify(clause:Clause, subst:EvarSubstitution, emap:EvarMap) 
    returns (sc:SearchClause, subst':EvarSubstitution)
    requires emap.inv()
    requires subst.valid()
    requires valid_clause(clause)
    requires forall e :: subst.in2(e) ==> e in emap.evar_map
    modifies emap
    ensures  subst'.valid()
    ensures  emap.inv()
    ensures  sc.subst.valid()
    ensures  sc.valid()
    ensures  sc.valid_emap(emap)
    ensures  forall e :: subst'.in2(e) ==> e in emap.evar_map
    ensures  forall e :: sc.subst.in2(e) ==> e in emap.evar_map
    ensures  emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    ensures  forall s :: subst.in1(s) ==> subst'.in1(s) && subst.get1(s) == subst'.get1(s)
    ensures  sc.clause == clause
    ensures  sc.clause.substitution_complete(make_subst(emap, subst'))
    // ensures  sc.subst.IsSubsetOf(subst') // sc.subst.Items() <= subst'.Items()
    ensures  forall v :: sc.subst.in1(v) && v.Var? ==> subst'.in1(v) && sc.subst.get1(v) == subst'.get1(v)
    // ensures forall e :: e in subst'
{
    subst' := subst;
    var local_subst:EvarSubstitution := new_bijective_map<VarTerm, Evar>();
    var evar_terms:seq<Evar> := [];
    reveal ToSet();
    for i := 0 to |clause.terms|
        invariant emap.inv()
        invariant subst'.valid()
        invariant local_subst.valid()
        // invariant forall j :: j < i ==> 
        invariant forall e :: e in evar_terms ==> e in emap.evar_map
        invariant forall e :: subst'.in2(e) ==> e in emap.evar_map
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map 
        invariant  forall s :: subst.in1(s) ==> subst'.in1(s) && subst.get1(s) == subst'.get1(s)
        invariant forall j :: 0 <= j < i ==> clause.terms[j].Var? ==> subst'.in1(clause.terms[j])
        invariant forall e :: local_subst.in2(e) ==> e in evar_terms
        // invariant local_subst.Keys() <= subst'.Keys()
        // invariant local_subst.Items() <= subst'.Items()
        // invariant local_subst.Values() <= subst'.Values()
        invariant forall j :: i <= j < |clause.terms| ==> !local_subst.in1(clause.terms[j])
        invariant forall j :: i <= j < |clause.terms| ==> (subst'.in1(clause.terms[j])) ==> !local_subst.in2(subst'.get1(clause.terms[j]))
        invariant |evar_terms| == i
        invariant reveal ToSet(); local_subst.Values() == ToSet(evar_terms)
        invariant forall j:nat | j < i :: local_subst.in1(clause.terms[j]) && (local_subst.get1(clause.terms[j]) == evar_terms[j])
        invariant forall v :: local_subst.in1(v) && v.Var? ==> subst'.in1(v) && local_subst.get1(v) == subst'.get1(v)
        invariant forall j:nat | 0 <= j < i :: clause.terms[j].Const? ==> emap.evar_map[evar_terms[j]] == Some(clause.terms[j].c)
        // invariant forall e :: e in local_subst.l_to_r ==> e in subst'.l_to_r
    {
        var term := clause.terms[i];
        match term {
            case Var(s) => {
                if subst'.in1(term) {
                    var ev := subst'.get1(term); // this should imply ev in emap.evar_map
                    evar_terms := evar_terms + [ev];
                    // local_subst := local_subst[term := ev];
                    // assert(!local_subst.in1(term));
                    // assert(!local_subst.in2(ev));
                    local_subst := local_subst.insert(term , ev);
                } else if !subst'.in1(term) { // TODO: THIS SHOULDN'T HAPPEN IF THE rule_restricted thing is there
                    var new_ev := emap.get_new_evar();
                    evar_terms := evar_terms + [new_ev];
                    // subst' := subst'[term := new_ev];
                    // InsertPreservesSubset(local_subst, subst', term, new_ev);
                    subst' := subst'.insert(term, new_ev);
                    // local_subst := local_subst[term := new_ev];
                    local_subst := local_subst.insert(term, new_ev);
                }
            }
            case Const(c) => {
                var new_ev := emap.get_new_evar();
                evar_terms := evar_terms + [new_ev];
                emap.resolve(new_ev, c);
                local_subst := local_subst.insert(term, new_ev);
            }
        }
    }
    assert(|evar_terms| == |clause.terms|);
    sc := SearchClause(clause.name, evar_terms, clause, local_subst);
}

method search (rules:seq<Rule>, goal:SearchClause, emap:EvarMap, depth: nat) returns (b:bool, ghost proof: Option<Proof>)//, e:EvarMap)
    requires valid_program(rules)
    requires emap.inv()
    requires goal.valid()
    requires goal.valid_emap(emap)
    // ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    modifies emap
    ensures emap.inv()
    ensures goal.valid_emap(emap) // TODO: Do we need to prove this at all times?
    ensures emap.monotonically_increasing() // ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    // ensures b ==> goal.emap_fully_resolved(emap)
    ensures b ==> goal.clause.substitution_concrete(make_subst(emap, goal.subst))
    ensures b ==> proof.Some? && valid_proof(rules, goal.clause.make_fact(make_subst(emap, goal.subst)), proof.value)
    // ensures b ==> proof.Some? && Last(proof.value).new_fact() == goal.clause.make_fact(make_subst(emap, goal.subst))
    // ensures emap.is_more_resolved'()
    decreases depth
{
    if (depth == 0) {
        return false, None;
    }
    var current_emap:EvarMap := new EvarMap.Init(emap);
    // find all rules that match current goal
    var matching_rules := find_matching_rules(rules, goal);
    assert(forall r :: r in matching_rules ==> valid_clause(r.head) && (forall c :: c in r.body ==> valid_clause(c)));
    // for all rules that match the current goal
    label AA: 
    for i := 0 to |matching_rules|
        invariant emap.inv()
        invariant current_emap.inv()
        invariant old@AA(current_emap.evar_map) == current_emap.evar_map
        invariant old@AA(current_emap.next_evar) == current_emap.next_evar
        // invariant unchanged@AA(current_emap)
        invariant forall j:nat | j < i :: valid_rule(matching_rules[j])
        // invariant goal.valid_emap(emap)
        invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
    {
        emap.copy(current_emap);
        var rule:Rule := matching_rules[i];
        assert(valid_clause(rule.head));
        var option_subst := unify(rule.head, goal, emap);
        
        var subst : EvarSubstitution;
        match option_subst {
            case None => continue;
            case Some(subst') => subst := subst';
        }

        var search_clauses:seq<SearchClause> := [];
        if |rule.body| == 0 {
            var concreteSubst := make_subst(emap, subst);
            var proofStep := ProofStep(map[], rule, []);
            assert rule in rules; // needed to use valid_program(rules) to conclude that valid_rule(rule) and then conclude that rule.head.is_ground() 
            // assume (goal.clause.make_fact(make_subst(emap, goal.subst)) == rule.head.make_fact(concreteSubst));
            return true, Some([proofStep]);
        } else {
            for j := 0 to |rule.body|
                invariant |search_clauses| == j
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant unchanged@AA(current_emap)
                invariant old@AA(current_emap.evar_map) == current_emap.evar_map
                invariant old@AA(current_emap.next_evar) == current_emap.next_evar
                invariant subst.valid()
                // invariant current_emap.evar_map == old(current_emap.evar_map)
                invariant forall sc :: sc in search_clauses ==> sc.valid()
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                invariant forall e :: subst.in2(e) ==> e in emap.evar_map
                invariant emap.monotonically_increasing() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
                invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                invariant forall i :: 0 <= i < j ==> rule.body[i] == search_clauses[i].clause
                invariant forall i :: 0 <= i < j ==> search_clauses[i].clause.substitution_complete(make_subst(emap, subst))
                invariant forall i :: 0 <= i < j ==> search_clauses[i].valid()
                invariant valid_rule(rule)
                // invariant forall v :: goal.subst.in1(v) && v.Var? ==> subst.in1(v) && goal.subst.get1(v) == subst.get1(v)
                invariant forall ii :: 0 <= ii < |goal.clause.terms| ==> subst.in1(rule.head.terms[ii]) && subst.get1(rule.head.terms[ii]) == goal.subst.get1(goal.clause.terms[ii])
                invariant forall ii :: 0 <= ii < |rule.head.terms| ==> rule.head.terms[ii].Const? ==> emap.evar_map[goal.evar_terms[ii]].Some? && Const(emap.evar_map[goal.evar_terms[ii]].value) == rule.head.terms[ii];
                invariant forall i :: 0 <= i < j ==> forall v :: search_clauses[i].subst.in1(v) && v.Var? ==> subst.in1(v) && search_clauses[i].subst.get1(v) == subst.get1(v)
                // invariant forall k in old(subst) ==> k in subst
            {
                var clause:Clause := rule.body[j];
                var search_clause, subst' := evarify(clause, subst, emap);
                subst := subst';
                search_clauses := search_clauses + [search_clause];
            }
            var flag := true;
            ghost var proofs : seq<Proof> := [];
            assert forall i :: 0 <= i < |search_clauses| ==> search_clauses[i].clause.substitution_complete(make_subst(emap, subst));
            label L: for j := 0 to |search_clauses|
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant unchanged@AA(current_emap)
                invariant old@AA(current_emap.evar_map) == current_emap.evar_map
                invariant old@AA(current_emap.next_evar) == current_emap.next_evar
                invariant subst.valid()
                invariant forall e :: subst.in2(e) ==> e in emap.evar_map
                // invariant current_emap == old(current_emap)
                invariant forall sc :: sc in search_clauses ==> sc.valid()
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                // invariant forall e :: e in subst.Values ==> e in emap.evar_map
                invariant emap.monotonically_increasing@L() // invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map
                // invariant emap.is_more_resolved'()
                // invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                // invariant goal.valid_emap(emap)
                // invariant flag ==> forall p :: p in proofs ==> p.Some?
                invariant flag ==> (|proofs| == j)
                invariant flag ==> (forall i :: 0 <= i < j ==> search_clauses[i].clause == rule.body[i])
                invariant forall c :: c in search_clauses ==> forall e :: c.subst.in2(e) ==> e in emap.evar_map
                invariant flag ==> (forall i :: 0 <= i < j ==> search_clauses[i].clause.substitution_concrete(make_subst(emap, search_clauses[i].subst)))
                invariant flag ==> (forall i :: 0 <= i < j ==> valid_proof(rules, search_clauses[i].clause.make_fact(make_subst(emap, search_clauses[i].subst)), proofs[i]))
                // invariant flag ==> (forall k :: 0 <= k < j ==> search_clauses[k].emap_fully_resolved(emap))
                invariant flag ==> forall k :: 0 <= k < j ==> search_clauses[k].clause.make_fact(make_subst(emap, search_clauses[k].subst)) == Last(proofs[k]).new_fact();
                invariant valid_rule(rule)
                // invariant goal.emap_fully_resolved(emap) // not true as an invariant
            {
                var b',proof_j := search(rules, search_clauses[j], emap, depth - 1);
                if !b' {
                    flag := false;
                    break;
                } else {
                    assert(proof_j.Some?);
                    proofs := proofs + [proof_j.value];
                }
                for k := 0 to j
                    invariant forall kk :: 0 <= kk < k ==> search_clauses[kk].valid_emap(emap)
                {
                    search_clauses[k].monotonically_increasing_preserves_valid_emap@L(emap);
                }
                assert (forall k :: 0 <= k < j ==> search_clauses[k].emap_fully_resolved(emap));
            }
            if flag {
                /*
                1. Use range restriction stuff to prove that emap_fully_resolved and substitution_concrete for the goal.clause
                2. Use the fact that apply(subst, rule.head):seq<Evar> == apply(goal.subst, goal.clause):seq<Evar>
                */
                var concreteSubst := make_subst(emap, subst);
                // assert |proofs| == |search_clauses| == |rule.body|;
                ////assert forall i :: 0 <= i < |rule.body| ==> rule.body[i] == search_clauses[i].clause;
                // assert forall i :: 0 <= i < |rule.body| ==> search_clauses[i].valid_emap(emap);
                // assume forall i :: 0 <= i < |rule.body| ==> search_clauses[i].emap_fully_resolved(emap); // TODO This will depend on some range restriction reasoning
                //// assert forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, search_clauses[i].clause.make_fact(make_subst(emap, search_clauses[i].subst)), proofs[i]);
                //// assert forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, search_clauses[i].clause.make_fact(concreteSubst), proofs[i]);
                // assert forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, rule.body[i], proofs[i]);
                // assert forall i :: 0 <= i < |rule.body| ==> rule.body[i].make_fact(concreteSubst) == Last(proofs[i]).new_fact();
                var proof := combine_proofs(rules, rule, concreteSubst, proofs);
                assert(goal.subst.valid());
                var goalSubst := make_subst(emap, goal.subst);
                // assert forall e:VarTerm | subst.in1(e) :: emap.evar_map[subst.get1(e)].Some?;
                // assert(forall e | e in goal.evar_terms :: e in subst.Values)
                // assert goal.emap_fully_resolved(emap);
                assert forall sc | sc in search_clauses :: forall v:VarTerm | v in sc.clause.terms :: concreteSubst[v].Const?;
                // assert forall e | e in goal.subst.Values() :: (exists sc | sc in search_clauses :: e in sc.subst.Values());
                // var pp:set<VarTerm>;
                // assert(forall v:VarTerm | v in rule.head.terms :: (exists c | c in rule.body :: v in c.terms));
                assert(seq(|search_clauses|, i requires 0 <= i < |search_clauses| => search_clauses[i].clause) == rule.body);
                // assert(forall v:VarTerm | v in rule.head.terms :: match_exists(v, rule.body));
                // assert(forall v:VarTerm | v in goal.clause.terms :: match_exists(v, seq(|search_clauses|, i => search_clauses[i].clause)));

                // assert(forall v:VarTerm | v in rule.head.terms :: (exists c | c in rule.body :: v in c.terms));
                // assert ToSet(goal.clause.terms) <= (set x:Term | ((forall sc :: sc in search_clauses && x in sc.clause.terms) :: x));
                // set x : T | P(x) :: x
                // assert forall t:VarTerm | t in goal.clause.terms :: emap.evar_map[goal.subst.get1(t)].Some?;
                /* 
                    assert forall i :: 0 <= i < |goal.clause.terms| ==> goal.subst.get1(goal.clause.terms[i]) == goal.evar_terms[i] == subst.get1(rule.head.terms[i])
                    goal.clause.make_fact(goalSubst).terms[i] == emap.evar_map[goal.subst.get1(goal.clause.terms[i])]
                    rule.head.make_fact(concreteSubst).terms[i] == emap.evar_map[subst.get1(rule.head.terms[i])]
                    ==> goal.clause.make_fact(goalSubst).terms[i] == rule.head.make_fact(concreteSubst).terms[i]
                */
                assert goal.clause.substitution_concrete(goalSubst);
                assert forall i :: 0 <= i < |goal.clause.terms| ==> goal.subst.get1(goal.clause.terms[i]) == goal.evar_terms[i] == subst.get1(rule.head.terms[i]);
                assert forall i :: 0 <= i < |goal.clause.terms| ==> goal.clause.make_fact(goalSubst).terms[i] == Const(emap.evar_map[goal.subst.get1(goal.clause.terms[i])].value);
                assert forall j :: 0 <= j < |rule.head.terms| ==> rule.head.terms[j].Const? ==> emap.evar_map[goal.evar_terms[j]].Some? && Const(emap.evar_map[goal.evar_terms[j]].value) == rule.head.terms[j];
                assert forall i :: 0 <= i < |goal.clause.terms| ==> rule.head.make_fact(concreteSubst).terms[i] == Const(emap.evar_map[subst.get1(rule.head.terms[i])].value);
                assert rule.head.make_fact(concreteSubst) == goal.clause.make_fact(goalSubst);
                return true, Some(proof);
            }
        }
        // emap.copy(current_emap);
    }
    return false, None;
}

ghost method flatten_two_proofs(rules: seq<Rule>, subst: Substitution, goal1: Fact, proof1: Proof, goal2: Fact, proof2: Proof) returns (proof: Proof)
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
    requires rule.head.substitution_concrete(subst)
    requires forall i :: 0 <= i < |rule.body| ==> rule.body[i].substitution_concrete(subst) 
    requires forall i :: 0 <= i < |rule.body| ==> valid_proof(rules, rule.body[i].make_fact(subst), proofs[i])
    requires forall i :: 0 <= i < |rule.body| ==> rule.body[i].make_fact(subst) == Last(proofs[i]).new_fact()
    ensures  valid_proof(rules, rule.head.make_fact(subst), proof)
{
    proof := proofs[0];
    var goal := rule.body[0].make_fact(subst);
    for i := 1 to |proofs|
        invariant valid_proof(rules, goal, proof)
        invariant goal.substitution_concrete(subst)
        invariant goal.make_fact(subst) == Last(proof).new_fact()
        invariant goal == rule.body[i-1].make_fact(subst)
        invariant forall j :: 0 <= j < |proof| ==> proof[j].valid()
        invariant forall j :: 0 <= j < i - 1 ==> rule.body[j].make_fact(subst) in Last(proof).facts
    {
        var new_proof := flatten_two_proofs(rules, subst, rule.body[i].make_fact(subst), proofs[i], goal, proof);
        proof := new_proof;
        goal := rule.body[i].make_fact(subst);
    }
    var last_step := ProofStep(subst, rule, Last(proof).facts + [ Last(proof).new_fact() ]);
    proof := proof + [last_step];
}

method get_query_search_clause(query:Clause, emap:EvarMap) returns (sc:SearchClause)
    requires emap.inv()
    requires valid_clause(query)
    modifies emap
    ensures emap.inv()
    ensures sc.subst.valid()
    ensures sc.valid()
    ensures sc.valid_emap(emap)
    ensures sc.clause == query
{
    reveal ToSet();
    var evar_terms:seq<Evar> := [];
    var subst: EvarSubstitution := new_bijective_map<VarTerm, Evar>();
    assert(subst.Values() == {});
    assert(ToSet(evar_terms) == {});
    for i := 0 to |query.terms|
        invariant emap.inv()
        invariant subst.valid()
        invariant |evar_terms| == i
        invariant reveal ToSet(); ToSet(evar_terms) == subst.Values()
        invariant forall e:Evar :: e in evar_terms ==> e in emap.evar_map
        invariant forall e:Evar :: subst.in2(e) ==> e in emap.evar_map
        invariant forall e:Evar :: subst.in2(e) ==> e in evar_terms
        invariant forall j :: i <= j < |query.terms| ==> !subst.in1(query.terms[j])
        invariant forall j:nat | j < i :: (subst.in1(query.terms[j]) && subst.get1(query.terms[j]) == evar_terms[j])
        invariant forall j:nat | j < i :: query.terms[j].Const? ==> emap.evar_map[evar_terms[j]] == Some(query.terms[j].c)
    {
        var term := query.terms[i];
        match term {
            case Var(s) => {
                        var new_ev := emap.get_new_evar();
                        evar_terms := evar_terms + [new_ev];
                        // subst := subst[term := new_ev];
                        subst := subst.insert(term, new_ev);
                    }
            case Const(c) => {
                        var new_ev := emap.get_new_evar();
                        evar_terms := evar_terms + [new_ev];
                        // subst := subst[term := new_ev];
                        subst := subst.insert(term, new_ev);
                        emap.resolve(new_ev, c);
            } 
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