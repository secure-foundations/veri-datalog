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
{
    var matching_rules : seq<Rule> := [];
    
    for i := 0 to |rules| // for rule in rules:
        invariant forall r:Rule :: r in matching_rules ==> r.head.name == goal.name && |r.head.terms| == |goal.evar_terms|
        // rules[i].name != goal.name || |rules[i].terms| != |goal.terms|
    {
        var rule := rules[i];
        if (rule.head.name == goal.name && |rule.head.terms| == |goal.evar_terms|) {
        // if (rule.name == goal.name && |rule.terms| == |goal.terms|) {
            matching_rules := matching_rules + [rule];
        }
    }
    return matching_rules;
}


method unify(head_clause:Clause, goal:SearchClause, emap:EvarMap) returns (o:Option<EvarSubstitution>)//, e:EvarMap)
    requires emap.inv()
    requires |head_clause.terms| == |goal.evar_terms|
    requires goal.valid_emap(emap)
    modifies emap
    ensures emap.is_more_resolved(old(emap))
    ensures goal.valid_emap(emap)
    ensures emap.inv()
    ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy

{
    // check if all terms in clause have correct mapping in goal.evar_terms
    var subst:EvarSubstitution := map[];
    for i := 0 to |head_clause.terms| 
        invariant emap.inv()
        invariant goal.valid_emap(emap)
        invariant forall e :: e in subst.Values ==> e in emap.evar_map
        invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
    {
        if head_clause.terms[i].Var? {
            print "a";
            var variableName := head_clause.terms[i].s;
            subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
        } else if head_clause.terms[i].Const? {
            print "b";
            var constant := head_clause.terms[i].c;
            var e := emap.lookup(goal.evar_terms[i]);
            match e {
                case None => {
                    emap.resolve(goal.evar_terms[i], constant);
                    assert(emap.inv());
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
    return Some(subst);
}

method evarify(clause:Clause, subst:EvarSubstitution, emap:EvarMap) 
    returns (sc:SearchClause, subst':EvarSubstitution)
    requires emap.inv()
    requires forall e :: e in subst.Values ==> e in emap.evar_map
    modifies emap
    ensures  emap.inv()
    // TODO: Stronger post condition on emap
    //ensures |emap.evar_map| > |old(emap.evar_map)| // TODO: Move this into EvarMap
    ensures  sc.valid_emap(emap)
    ensures  forall e :: e in subst'.Values ==> e in emap.evar_map
    ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
    ensures forall s :: s in subst ==> s in subst'
{
    subst' := subst;
    var evar_terms:seq<Evar> := [];
    for i := 0 to |clause.terms|
        invariant emap.inv()
        invariant forall e :: e in evar_terms ==> e in emap.evar_map
        invariant forall e :: e in subst'.Values ==> e in emap.evar_map
        invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map 
        invariant forall s :: s in subst ==> s in subst'
    {
        var term := clause.terms[i];
        match term {
            case Var(s) => {
                if term in subst'.Keys {
                    var ev := subst'[term]; // this should imply ev in emap.evar_map
                    evar_terms := evar_terms + [ev];
                } else if term !in subst' {
                    var new_ev := emap.get_new_evar();
                    evar_terms := evar_terms + [new_ev];
                    subst' := subst'[term := new_ev];
                }
            }
            case Const(c) => {
                var new_ev := emap.get_new_evar();
                evar_terms := evar_terms + [new_ev];
                emap.resolve(new_ev, c);
            }
        }
    }

    sc := SearchClause(clause.name, evar_terms, clause, subst');
}

method search (rules:seq<Rule>, goal:SearchClause, emap:EvarMap, depth: nat) returns (b:bool)//, e:EvarMap)
    requires emap.inv()
    requires goal.valid_emap(emap)
    // ensures o.Some? ==> forall e :: e in o.value.Values ==> e in emap.evar_map
    modifies emap
    ensures emap.inv()
    ensures goal.valid_emap(emap)
    ensures forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
    decreases depth
{
    if (depth == 0) {
        b := false;
        // e := emap;
        return;
    }
    print "Searching on ", goal, " with emap ", emap.evar_map, "\n";
    // find all rules that match current goal
    var matching_rules := find_matching_rules(rules, goal);
    print "\t matching_rules = ", matching_rules, "\n";

    assert(goal.valid_emap(emap));

    // for all rules that match the current goal
    for i := 0 to |matching_rules|
        invariant emap.inv()
        // invariant goal.valid_emap(emap)
        invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
        // invariant e.inv()
    {
        print "\t i = ", i, "\n"; 
        // var current_emap:EvarMap := emap; // TODO: Make a copy and not reference
        var current_emap:EvarMap := new EvarMap.Init(emap); // TODO: Check if this actually makes a copy
        assert (forall e :: e in emap.evar_map ==> e in current_emap.evar_map);
        assert current_emap.inv();
        var rule:Rule := matching_rules[i];
        print "\t matching_rule = ", rule, "\n";
        var option_subst := unify(rule.head, goal, emap);
        assert(goal.valid_emap(emap));
        print "\t option_subst = ", option_subst, "\n";
        //current_emap := e';
        var subst : EvarSubstitution;
        match option_subst {
            case None => continue;
            case Some(subst') => subst := subst';
        }
        assert emap.inv();
        assert current_emap.inv();

        var search_clauses:seq<SearchClause> := [];
        // TODO: What if rule.body is empty?
        if |rule.body| == 0 {
            // TODO: Track ghost fact db
            // assert(rule.Head in prog);
            // assert(rule.head is in Facts()); // do some proof stuff
            return true;
        } else {
            assert emap.inv();
            for j := 0 to |rule.body|
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant current_emap.evar_map == old(current_emap.evar_map)
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                invariant forall e :: e in subst.Values ==> e in emap.evar_map
                invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
                invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                // invariant goal.valid_emap(emap);
            {
                var clause:Clause := rule.body[j];
                var search_clause, subst' := evarify(clause, subst, emap);
                subst := subst';
                search_clauses := search_clauses + [search_clause];
            }
            // assert(goal.valid_emap(emap));

            var flag := true;
            for j := 0 to |search_clauses|
                invariant emap.inv()
                invariant current_emap.inv()
                // invariant current_emap == old(current_emap)
                invariant forall sc :: sc in search_clauses ==> sc.valid_emap(emap)
                invariant forall e :: e in old(emap.evar_map) ==> e in emap.evar_map // TODO: Make this a predicate inside evar.dfy
                invariant forall e :: e in old(emap.evar_map) ==> e in current_emap.evar_map // TODO: Make this a predicate inside evar.dfy
                // invariant goal.valid_emap(emap)
            {
                var b' := search(rules, search_clauses[j], emap, depth - 1);
                if !b' {
                    flag := false;
                }
                // current_emap := e;
            }
            // return true only if all search branches return true
            // return true if at least one rule works successfully
            if flag {
                return true;
            }
            // assert(goal.valid_emap(emap));
        }
        // emap := current_emap;
        assert(emap.inv());
        assert(current_emap.inv());
        // assert(goal.valid_emap(emap));
        emap.copy(current_emap);
        //current_emap := new EvarMap.Init(emap);
    }
    return false;
}

method get_query_search_clause(query:Clause, emap:EvarMap) returns (sc:SearchClause)
    requires emap.inv()
    modifies emap
    ensures emap.inv()
    ensures sc.valid_emap(emap)
{
    var evar_terms:seq<Evar> := [];
    var subst: EvarSubstitution := map[];
    for i := 0 to |query.terms|
        invariant emap.inv()
        invariant forall e:Evar :: e in evar_terms ==> e in emap.evar_map
        invariant forall e:Evar :: e in subst.Values ==> e in emap.evar_map
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

    sc := SearchClause(query.name, evar_terms, query, subst);
}

method run_datalog(p:Program)
    requires |p| > 0
{
    var prog := p;
    var query_rule := Last(p);

    var emap:EvarMap := new EvarMap();
    assert emap.inv();
    var query_sc:SearchClause := get_query_search_clause(query_rule.head, emap);
    var b := search(prog, query_sc, emap, 0x1_0000_0000);
    print "Query returned ", b, "\n";
}


// method run(raw_prog:Program)
//   requires |raw_prog| > 0
// {
//   var prog := DropLast(raw_prog);
//   var q := Last(raw_prog);
//   //print "Program is: ", prog, "\n";
//   //print "Query is: ", q, "\n";
//   //var valid_prog := check_program(prog);
//   var valid_query := check_rule(q);
//   //if valid_prog && valid_query {
//   if valid_query {
//     var b := query(prog, q);  
//     print "Query returned ", b, "\n";
//   } else {
//     print "Sorry, that's an invalid program and/or query\n";
//   }
// }