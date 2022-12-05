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


method unify(head_clause:Clause, goal:SearchClause, emap:EvarMap) returns (o:Option<EvarSubstitution>)
{
    // check if all terms in clause have correct mapping in goal.evar_terms
    var subst:EvarSubstitution;
    for i := 0 to |head_clause.terms| 
        invariant true
    {
        if head_clause.terms[i].Var? {
            var variableName := head_clause.terms[i].s;
            subst := subst[head_clause.terms[i] := goal.evar_terms[i]];
        } else if head_clause.terms[i].Const? {
            var constant := head_clause.terms[i].c;
            var e := emap.lookup(goal.evar_terms[i]);
            match e {
                case None => emap.resolve(goal.evar_terms[i], constant);
                case Some(constant') =>
                    if constant != constant {
                        // ignore rule
                        return None;
                    }
            }
        }
    }
    return Some(subst);
}

method evarify(clause:Clause, subst:EvarSubstitution, emap:EvarMap) 
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

    sc := SearchClause(clause.name, evar_terms);
}

method search (rules:seq<Rule>, goal:SearchClause, emap:EvarMap) returns (b:bool)
{
    // find all rules that match current goal
    var matching_rules := find_matching_rules(rules, goal);

    // for all rules that match the current goal
    for i := 0 to |matching_rules|
        invariant true
    {
        // var current_emap:EvarMap := emap; // TODO: Make a copy and not reference
        var current_emap:EvarMap := new EvarMap.Init(emap); // TODO: Check if this actually makes a copy
        var rule:Rule := rules[i];
        var option_subst := unify(rule.head, goal, emap);
        var subst : EvarSubstitution;
        match option_subst {
            case None => continue;
            case Some(subst') => subst := subst';
        }

        var search_clauses:seq<SearchClause> := [];
        // TODO: What if rule.body is empty?
        for j := 0 to |rule.body|
            invariant true
        {
            var clause:Clause := rule.body[j];
            var search_clause, subst' := evarify(clause, subst, current_emap);
            subst := subst';
            search_clauses := search_clauses + [search_clause];
        }

        for j := 0 to |search_clauses|
            invariant true
        {
            var b' := search(rules, search_clauses[j], current_emap);
        }
    }
}

method get_query_search_clause(query:Clause, emap:EvarMap) returns (sc:SearchClause)
{
    var evar_terms:seq<Evar> := [];
    for i := 0 to |query.terms|
        invariant true
    {
        var term := query.terms[i];
        match term {
            case Var(s) => {
                var new_ev := emap.get_new_evar();
                evar_terms := evar_terms + [new_ev];
                // subst' := subst'[term := new_ev];
            }
            case Const(c) => {} // TODO: Create new evars and map them to the const?
        }
    }

    sc := SearchClause(query.name, evar_terms);
}

method run_datalog(p:Program)
    requires |p| > 0
{
    var prog := DropLast(p); // remove the query from the list of rules
    var query_rule := Last(p);

    var emap:EvarMap := new EvarMap();
    var query_sc:SearchClause := get_query_search_clause(query_rule.head, emap);
    var b := search(prog, query_sc, emap);
}