include "def.dfy"
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

method find_matching_rules(rules: seq<Rule>, goal:SearchClause) returns (c:seq<Rules>)
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

// SearchClause : X(evarA, evarB)
// Rule : X(a,b) = Y(b,c), Z(c,d) ...........


method unify(head_clause:Clause, goal:SearchClause) returns (o:Option<EvarSubstitution>)
{
    // check if all terms in clause have correct mapping in goal.evar_terms
}

method search (rules:seq<Rule>, goal:SearchClause) returns (b:bool)

{
    // for rule in rules:
    var matching_rules := find_matching_rules(rules, goal);

    for i := 0 to |matching_rules|
        invariant true
    {
        match unify(rule.head, goal) {
            // case .. =>
            // case .. =>
        }
    }
}