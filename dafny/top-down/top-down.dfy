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
{
    var matching_rules : seq<Rule> := [];
    
    for i := 0 to |rules| // for rule in rules:
        invariant true
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


method unify(head_clause:Clause, goal:SearchClause, emap:EvarMap) returns (o:Option<EvarSubstitution>, e:EvarMap)
{
    // check if all terms in clause have correct mapping in goal.evar_terms
    var subst:EvarSubstitution := map[];
    for i := 0 to |head_clause.terms| 
        invariant true
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
                case None => emap.resolve(goal.evar_terms[i], constant);
                case Some(constant') =>
                    if constant != constant' {
                        // ignore rule
                        return None,emap;
                    }
                    // } else {
                    //     subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
                    // }
            }
        }
    }
    return Some(subst),emap;
}

method evarify(clause:Clause, subst:EvarSubstitution, emap:EvarMap, rule:Rule) 
    returns (sc:SearchClause, subst':EvarSubstitution)
{
    subst' := subst;
    var evar_terms:seq<Evar> := [];
    for i := 0 to |clause.terms|
        invariant true
    {
        var term := clause.terms[i];
        match term {
            case Var(s) => {
                if term in subst.Keys {
                    var ev := subst[term];
                    evar_terms := evar_terms + [ev];
                } else if term !in subst {
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

    sc := SearchClause(clause.name, evar_terms, rule, subst');
}

method search (rules:seq<Rule>, goal:SearchClause, emap:EvarMap) returns (b:bool, e:EvarMap)
{
    print "Searching on ", goal, " with emap ", emap.evar_map, "\n";
    // find all rules that match current goal
    var matching_rules := find_matching_rules(rules, goal);
    print "\t matching_rules = ", matching_rules, "\n";

    // for all rules that match the current goal
    for i := 0 to |matching_rules|
        invariant true
    {
        print "\t i = ", i, "\n"; 
        // var current_emap:EvarMap := emap; // TODO: Make a copy and not reference
        var current_emap:EvarMap := new EvarMap.Init(emap); // TODO: Check if this actually makes a copy
        var rule:Rule := matching_rules[i];
        print "\t matching_rule = ", rule, "\n";
        var option_subst,e := unify(rule.head, goal, emap);
        print "\t option_subst = ", option_subst, "\n";
        current_emap := e;
        var subst : EvarSubstitution;
        match option_subst {
            case None => continue;
            case Some(subst') => subst := subst';
        }

        var search_clauses:seq<SearchClause> := [];
        // TODO: What if rule.body is empty?
        if |rule.body| == 0 {
            // TODO: Track ghost fact db
            // assert(rule.Head in prog);
            // assert(rule.head is in Facts()); // do some proof stuff
            return true, current_emap;
        } else {
            for j := 0 to |rule.body|
                invariant true
            {
                var clause:Clause := rule.body[j];
                var search_clause, subst' := evarify(clause, subst, current_emap, rule);
                subst := subst';
                search_clauses := search_clauses + [search_clause];
            }

            var flag := true;
            for j := 0 to |search_clauses|
                invariant true
            {
                var b',e := search(rules, search_clauses[j], current_emap);
                if !b' {
                    flag := false;
                }
                current_emap := e;
            }
            // return true only if all search branches return true
            // return true if at least one rule works successfully
            if flag {
                return true, current_emap;
            }
        }
    }
    return false, emap;
}

method get_query_search_clause(query:Clause, emap:EvarMap) returns (sc:SearchClause)
    requires emap.inv()
    modifies emap
    ensures emap.inv()
{
    var evar_terms:seq<Evar> := [];
    var subst: EvarSubstitution := map[];
    for i := 0 to |query.terms|
        invariant true
        invariant emap.inv()
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

    sc := SearchClause(query.name, evar_terms, Rule(query, []), subst);
}

method run_datalog(p:Program)
    requires |p| > 0
{
    var prog := p;
    var query_rule := Last(p);

    var emap:EvarMap := new EvarMap();
    assert emap.inv();
    var query_sc:SearchClause := get_query_search_clause(query_rule.head, emap);
    var b,_ := search(prog, query_sc, emap);
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