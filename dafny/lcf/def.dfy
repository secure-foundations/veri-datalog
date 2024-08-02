datatype Result<A> = Ok(val : A) | Err {
  predicate IsFailure() { this.Err? }
  function PropagateFailure() : Result<A>
    requires IsFailure() {
    Err
  }
  function Extract() : A
    requires !IsFailure() {
    val
  }
}

datatype Const = Atom(val : string) | Nat(i : nat) | Str(s : string) | List(l : seq<Const>)

type Subst = map<string, Const>

predicate compatible_subst(s : Subst, t : Subst) {
  forall v :: v in s.Keys && v in t.Keys ==> s[v] == t[v]
}

function merge_subst(s : Subst, t : Subst) : (res : Result<Subst>)
  ensures res.Ok? ==> (
              && compatible_subst(s, t)
              && res.val.Keys == s.Keys + t.Keys
              && (forall v :: v in s ==> res.val[v] == s[v])
              && (forall v :: v in t ==> res.val[v] == t[v])
            )
{
  if compatible_subst(s, t) then Ok(s+t) else Err
}

datatype Term = Const(val : Const) | Var(v : string) {
  predicate complete_subst(s : Subst) {
    match this
    case Var(v) => v in s
    case Const(_) => true
  }
  predicate concrete() {
    Const?
  }
  function subst(s : Subst) : (res : Term)
    requires complete_subst(s)
    ensures res.concrete()
  {
    match this
    case Var(v) => Const(s[v])
    case Const(_) => this
  }
}

function strings(consts : seq<Const>) : Result<seq<string>> {
  if forall i :: 0 <= i < |consts| ==> consts[i].Str? then
    Ok(seq(|consts|, i requires 0 <= i < |consts| => consts[i].s))
  else Err
}

function string_join(sep : string, parts : seq<string>) : string {
  if |parts| == 0 then ""
  else if |parts| == 1 then parts[0]
  else parts[0] + sep + string_join(sep, parts[1..])
}

datatype Builtin = NatLeq | NatGeq | NatNeq | SubString | SplitString | Length | Member | Reverse {
  predicate valid(args : seq<Const>) {
    match this {
      case NatLeq | NatGeq | NatNeq => |args| == 2 && args[0].Nat? && args[1].Nat?
      case SubString => |args| == 5 && args[0].Str? && args[1].Nat? && args[2].Nat? && args[3].Nat? && args[4].Str?
      case SplitString => |args| == 3 && args[0].Str? && args[1].Str? && args[2].List?
      case Length => |args| == 2 && args[0].List? && args[1].Nat?
      case Member => |args| == 2 && args[1].List?
      case Reverse => |args| == 2 && args[0].List? && args[1].List?
    }
  }

  predicate eval(args : seq<Const>)
    requires valid(args)
  {
    match this {
      case NatGeq => args[0].i <= args[1].i
      case NatLeq => args[0].i >= args[1].i
      case NatNeq => args[0].i != args[1].i
      case SubString => (
        var str, before, len, after, sub := args[0], args[1], args[2], args[3], args[4];
        before.i+len.i+after.i == |str.s| &&
        str.s[before.i..before.i + len.i] == sub.s
      )
      case SplitString => (
        var str, sep, parts := args[0], args[1], args[2];
        match strings(parts.l) {
          case Ok(parts_strings) => str.s == string_join(sep.s, parts_strings)
          case Err => false
        }
      )
      case Length => (
        var l, n := args[0], args[1];
        |l.l| == n.i
      )
      case Member => (
        var e, l := args[0], args[1];
        e in l.l
      )
      case Reverse => (
        var l, r := args[0], args[1];
        |l.l| == |r.l| &&
        forall i :: 0 <= i < |l.l| ==> l.l[i] == r.l[|l.l|-1-i]
      )
    }
  }
}

datatype Prop =
  App(head : string, args : seq<Term>) |
  Eq(l : Term, r : Term) |
  BuiltinOp(b : Builtin, args : seq<Term>)
{
  predicate complete_subst(s : Subst) {
    match this
    case App(head, args) => forall i :: 0 <= i < |args| ==> args[i].complete_subst(s)
    case Eq(x, y) => x.complete_subst(s) && y.complete_subst(s)
    case BuiltinOp(_, args) => forall i :: 0 <= i < |args| ==> args[i].complete_subst(s)
  }
  predicate concrete() {
    match this
    case App(head, args) => forall i :: 0 <= i < |args| ==> args[i].concrete()
    case Eq(x, y) => x.concrete() && y.concrete()
    case BuiltinOp(_, args) => forall i :: 0 <= i < |args| ==> args[i].concrete()
  }
  function subst(s : Subst) : (res:Prop)
    requires complete_subst(s)
    ensures res.concrete()
  {
    match this
    case App(h, args) => App(h, seq(|args|, i requires 0 <= i < |args| => args[i].subst(s)))
    case Eq(x, y) => Eq(x.subst(s), y.subst(s))
    case BuiltinOp(b, args) => BuiltinOp(b, seq(|args|, i requires 0 <= i < |args| => args[i].subst(s)))
  }
  predicate symbolic() {
    this.App?
  }

  predicate valid()
    requires !symbolic()
    requires concrete() {
    match this
    case Eq(x, y) => x.val == y.val
    case BuiltinOp(b, args) => (
      var consts := seq(|args|, i requires 0 <= i < |args| => args[i].val);
      b.valid(consts) && b.eval(consts)
    )
  }
}

datatype Rule = Rule(head : Prop, body : seq<Prop>, id : nat) {
  predicate complete_subst(s : Subst) {
    head.complete_subst(s) && (forall i :: 0 <= i < |body| ==> body[i].complete_subst(s))
  }

  predicate concrete() {
    head.concrete() && forall i :: 0 <= i < |body| ==> body[i].concrete()
  }

  function subst(s : Subst) : (res:Rule)
    requires complete_subst(s)
    ensures res.concrete()
  {
    var body' := seq(|body|, i requires 0 <= i < |body| => body[i].subst(s));
    Rule(head.subst(s), body', id)
  }

  predicate wf() {
    head.symbolic()
  }
}

type RuleSet = rs:seq<Rule> | forall i :: 0 <= i < |rs| ==> rs[i].wf()
  witness []


datatype Proof = PStep(rule : Rule, s : Subst, branches : seq<Proof>) | QED(p : Prop) {
  function head() : Prop
    requires PStep? ==> rule.complete_subst(s)
  {
    match this
    case PStep(rule, s, branches) => rule.subst(s).head
    case QED(p) => p
  }
  predicate valid(rule_set : RuleSet) {
    match this
    case QED(p) => p.concrete() && !p.symbolic() && p.valid()
    case PStep(rule, s, branches) =>
      rule in rule_set &&
      rule.complete_subst(s) &&
      |rule.body| == |branches| &&
      var rule' := rule.subst(s);
      forall i :: 0 <= i < |rule'.body| ==>
                    branches[i].valid(rule_set) &&
                    rule'.body[i] == branches[i].head()
  }
}

datatype Thm = Thm(val : Prop, ghost p : Proof) {
  ghost predicate wf(rule_set : RuleSet) {
    p.valid(rule_set) && p.head() == val
  }

}

function mk_leaf(p : Prop) : (res : Result<Thm>)
  ensures p.concrete() && !p.symbolic() && p.valid() ==> res.Ok?
  ensures res.Ok? ==> res.val.val == p
{
  if p.concrete() && !p.symbolic() && p.valid()
  then
    Ok(Thm(p, QED(p)))
  else
    Err
}

function mk_thm(rs : RuleSet, i : nat, s : Subst, args : seq<Thm>) : (res : Result<Thm>)
  requires i < |rs|
  requires forall j :: 0 <= j < |args| ==> args[j].wf(rs)
  ensures rs[i].complete_subst(s) && |args| == |rs[i].body| && (forall j :: 0 <= j < |args| ==> args[j].val == rs[i].subst(s).body[j])
          ==> res.Ok?
  ensures res.Ok? ==> rs[i].complete_subst(s) && res.val.wf(rs) && res.val.val == rs[i].subst(s).head {
  var r := rs[i];
  if |args| == |r.body| && r.complete_subst(s) && (forall j :: 0 <= j < |args| ==> args[j].val == r.subst(s).body[j]) then
    var pfs := seq(|args|, i requires 0 <= i < |args| => args[i].p);
    var p := PStep(r, s, pfs);
    Ok(Thm(r.subst(s).head, p))
  else Err
}

function tst_nat() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(NatLeq, [Var("x"), Const(Nat(3))])], 0)]
}

function tst_nat_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(NatLeq, [Const(Nat(3)), Const(Nat(3))])).val;
  var s : Subst := map["x" := Nat(3)];
  Ok(mk_thm(tst_nat(), 0, s, [lf]).val)
}

function tst_sub_string() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(SubString, [Const(Str("hello world!")), Const(Nat(6)), Const(Nat(5)), Const(Nat(1)), Var("x")])], 0)]
}

function tst_sub_string_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(SubString, [Const(Str("hello world!")), Const(Nat(6)), Const(Nat(5)), Const(Nat(1)), Const(Str("world"))] )).val;
  var s : Subst := map["x" := Str("world")];
  Ok(mk_thm(tst_sub_string(), 0, s, [lf]).val)
}

function tst_split_string() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Var("x")])], 0)]
}

function tst_string_split_thm() : Result<Thm> {
  var prop := BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Const( List( [Str("a"), Str("b")]))]);
  assert prop.valid();
  var lf := mk_leaf(prop).val;
  var s : Subst := map["x" :=  List([Str("a"), Str("b")])];
  Ok(mk_thm(tst_split_string(), 0, s, [lf]).val)
}

function tst_length() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Length, [Const(List([Nat(1), Nat(2), Nat(3)])), Var("x")])], 0)]
}

function tst_length_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Length, [Const(List([Nat(1), Nat(2), Nat(3)])), Const(Nat(3))])).val;
  var s : Subst := map["x" := Nat(3)];
  Ok(mk_thm(tst_length(), 0, s, [lf]).val)
}

function tst_member() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Member, [Var("x"), Const(List([Nat(1), Nat(2), Nat(3)]))])], 0)]
}

function tst_member_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Member, [Const(Nat(2)), Const(List([Nat(1), Nat(2), Nat(3)]))])).val;
  var s : Subst := map["x" := Nat(2)];
  Ok(mk_thm(tst_member(), 0, s, [lf]).val)
}

function tst_reverse() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Reverse, [Const(List([Nat(1), Nat(2), Nat(3)])), Var("x")])], 0)]
}

function tst_reverse_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Reverse, [
                                Const(List([Nat(1), Nat(2), Nat(3)])),
                                Const(List([Nat(3), Nat(2), Nat(1)]))
                              ])).val;
  var s : Subst := map["x" := List([Nat(3), Nat(2), Nat(1)])];
  Ok(mk_thm(tst_reverse(), 0, s, [lf]).val)
}

//// Trace Reconstruction

datatype Port = Call | Unify | Redo | Exit | Fail

datatype Event = Event(port : Port, level : nat, prop : Prop, i : nat)

type Trace = seq<Event>

function unify_terms(s : seq<Term>, t : seq<Term>) : (res : Result<Subst>)
  requires forall i :: 0 <= i < |t| ==> t[i].concrete()
  ensures res.Ok? ==> |s| == |t| && forall i :: 0 <= i < |s| ==> s[i].complete_subst(res.val) && s[i].subst(res.val) == t[i]
{
  if |s| != |t| then Err else
  if s == [] then Ok(map[]) else
  match unify_terms(s[1..], t[1..])
  case Err => Err
  case Ok(subst) => match s[0]
    case Const(c) => if c == t[0].val then Ok(subst) else Err
    case Var(v) => if v !in subst || subst[v] == t[0].val then Ok(subst[v := t[0].val]) else Err
}

function unify(r : Prop, g : Prop) : (res : Result<Subst>)
  requires g.concrete()
  ensures res.Ok? ==> r.complete_subst(res.val) && r.subst(res.val) == g
{
  match (r, g)
  case (App(f1, args1), App(f2, args2)) =>
    if f1 == f2 then unify_terms(args1, args2) else Err
  case _ => Err
}

datatype Match = Match(s : Subst, thm : Thm)


//// Trace tree construction.

datatype TraceNode = TraceNode(i : nat, prop : Prop, children : seq<TraceNode>) {
  predicate wf() {
    prop.concrete()
    && forall j :: 0 <= j < |children| ==> children[j].wf()
  }

  method dump() {
    dump_indent("");
  }

  method dump_indent(indent : string) {
    print indent, "rule=", i, " prop=", prop, "\n";
    var i := 0;
    while i < |children| {
      children[i].dump_indent(indent+"  ");
      i := i + 1;
    }
  }
}

datatype Outcome = Success(nodes : seq<TraceNode>) | Failure {
  predicate wf() {
    match this {
      case Success(nodes) => forall i :: 0 <= i < |nodes| ==> nodes[i].wf()
      case Failure => true
    }
  }
}

// Process a sequence of trace events into a trace tree of the successful search path.
method build_trace_tree(trace : Trace, min_level : nat, bound : nat) returns (res : Result<(Outcome, Trace)>)
  ensures res.Ok? ==> res.val.0.wf() && |res.val.1| <= |trace|
  decreases bound
{
  if bound == 0 {
    return Err;
  }

  var nodes: seq<TraceNode> := [];
  var trace := trace;
  while |trace| > 0 && trace[0].level >= min_level
    invariant forall i :: 0 <= i < |nodes| ==> nodes[i].wf()
    decreases |trace|
  {
    // 1. Collects all rules that might match by having a head with the same name and number of arguments
    //      call is traced, once, if any rules might match.
    //      redo is also traced when the engine backtracks to find the next matching rule.
    var collect := trace[0];
    if collect.port != Call && collect.port != Redo {
      print "expected: call or redo\n";
      return Err;
    }
    var level := collect.level;
    trace := trace[1..];

    // 2. Finds the next matching rule whose head can be unified with the predicate
    //      unify is traced with the results of unification if one is found.
    //      fail is traced if no rule heads can be unified.
    if |trace| == 0 {
      print "unexpected end of trace\n";
      return Err;
    }
    var unify := trace[0];
    trace := trace[1..];
    if unify.level != level {
      print "level mismatch\n";
      return Err;
    }
    if unify.port == Fail {
      return Ok((Failure, trace));
    }
    if unify.port != Unify {
      print "expected: unify\n";
      return Err;
    }

    // 3. Applies variable assignments from unification to clauses in the rule
    //    body and continues at #1 with the updated clauses.
    var maybe_body := build_trace_tree(trace, level+1, bound-1);
    if maybe_body.Err? {
      print "recursion error\n";
      return Err;
    }
    var outcome := maybe_body.val.0;
    trace := maybe_body.val.1;
    if outcome.Failure? {
      continue;
    }

    // 4. After all of the body clauses of the matched rule have either succeeded, failed, or thrown an exception:
    //      exit is traced if all of them succeeded (meaning this rule is true).
    //      fail is traced if any of them failed (meaning this rule is false).
    //      exception is traced if any of them threw an exception.
    if |trace| == 0 {
      print "unexpected end of trace\n";
      return Err;
    }
    var exit := trace[0];
    trace := trace[1..];
    if !exit.prop.concrete() {
      print "non concrete exit\n";
      return Err;
    }

    match exit.port {
      case Exit => {
        var node := TraceNode(unify.i, exit.prop, outcome.nodes);
        nodes := nodes + [node];
        continue;
      }
      case Fail => {
        return Ok((Failure, trace));
      }
      case _ => {
        print "expected: exit or fail\n";
        return Err;
      }
    }
  }
  return Ok((Success(nodes), trace));
}

// Lookup rule with the given id.
method lookup_rule(rs : RuleSet, id : nat) returns (res : Result<nat>)
  ensures res.Ok? ==> res.val < |rs| && rs[res.val].id == id
{
  var i := 0;
  while i < |rs| {
    if rs[i].id == id {
      return Ok(i);
    }
    i := i+1;
  }
  return Err;
}

// Derive a theorem from a trace tree node.
method reconstruct(node : TraceNode, g : Prop, rs : RuleSet) returns (res : Result<Match>)
  requires node.wf()
  ensures res.Ok? ==> res.val.thm.wf(rs)
{
  // Which rule are we applying.
  var ri: nat;
  var maybe_ri := lookup_rule(rs, node.i);
  match maybe_ri {
    case Ok(index) => ri := index;
    case Err => {
      print "could not find rule\n";
      return Err;
    }
  }
  var r := rs[ri];

  // Reconstruct the rule body.
  if |node.children| != |r.body| {
    print "rule body length mismatch\n";
    return Err;
  }

  var s: Subst := map[];
  var args: seq<Thm> := [];
  var i := 0;
  while i < |r.body|
    invariant forall j :: 0 <= j < |args| ==> args[j].wf(rs)
  {
    var subgoal := r.body[i];
    var res := reconstruct(node.children[i], r.body[i], rs);
    match res {
      case Ok(m) => {
        var maybe_subst := merge_subst(s, m.s);
        match maybe_subst {
          case Ok(subst) => s := subst;
          case Err => {
            print "failed to merge substitutions\n";
            return Err;
          }
        }
        args := args + [m.thm];
      }
      case Err => {
        print "failed subgoal trace\n";
        return Err;
      }
    }
    i := i+1;
  }

  // Unify exit with goal.
  var goal_subst: Subst;
  var maybe_subst := unify(g, node.prop);
  match maybe_subst {
    case Ok(subst) => {
      goal_subst := subst;
    }
    case Err => {
      print "failed to unify with exit\n";
      return Err;
    }
  }

  var maybe_merged := merge_subst(s, goal_subst);
  match maybe_merged {
    case Ok(merged) => s := merged;
    case Err => {
      print "failed to merge substitution\n";
      return Err;
    }
  }

  // Deduce theorem.
  var maybe_thm := mk_thm(rs, ri, s, args);
  match maybe_thm {
    // TODO(mbm): trim down the subst?
    case Ok(thm) => {
      return Ok(Match(goal_subst, thm));
    }
    case Err => {
      print "failed to deduce thm\n";
      return Err;
    }
  }
}

/*
//// Incomplete experiment at a more functional style for trace reconstruction.

function pop(trace : Trace, port : Port) : (res : Result<(Event, Trace)>)
{
  if |trace| == 0 || trace[0].port != port then Err
  else Ok((trace[0], trace[1..]))
}

datatype Matches = Matches(s : Subst, args: seq<Thm>) {
  function merge(m : Match) : Result<Matches> {
    match merge_subst(s, m.s) {
      case Ok(sbst) => Ok(Matches(sbst, args + [m.thm]))
      case Err => Err
    }
  }
}

function body(trace : Trace, rs : RuleSet, gs : seq<Prop>, bound : nat) : (res : Result<(Matches, Trace)>)
  decreases bound, 0
{
  if bound == 0 then Err
  else if |gs| == 0 then Ok((Matches(map[], []), trace))
  else match reconstruct(trace, rs, gs[0], bound-1) {
         case Ok((m, rest)) => match body(rest, rs, gs[1..], bound-1) {
           case Ok((ms, rest)) => match ms.merge(m) {
             case Ok(merged) => Ok((merged, rest))
             case Err => Err
           }
           case Err => Err
         }
         case Err => Err
       }
}

function reconstruct(trace : Trace, rs : RuleSet, gs : Prop, bound : nat) : (res : Result<(Match, Trace)>)
  decreases bound, 1
{
  if bound == 0 then Err
  else match pop(trace, Unify) {
         case Ok((u, rest)) =>
           if u.i >= |rs| then Err // TODO: require this property
           else match body(rest, rs, rs[u.i].body, bound-1) {
                  case Ok((ms, rest)) => match pop(rest, Exit) {
                    case Ok((e, rest)) => Err
                    case Err => Err
                  }
                  case Err => Err
                }
         case Err => Err
       }
}

datatype Matches = Matches(s : Subst, args: seq<Thm>) {
  ghost predicate wf(rs : RuleSet) { forall j :: 0 <= j < |args| ==> args[j].wf(rs) }

  function merge(m : Match) : Result<Matches> {
    match merge_subst(s, m.s) {
      case Ok(sbst) => Ok(Matches(sbst, args + [m.thm]))
      case Err => Err
    }
  }
}

function body(nodes : seq<TraceNode>, gs : seq<Prop>, rs : RuleSet) : (res : Result<Matches>)
  requires forall i :: 0 <= i < |nodes| ==> nodes[i].wf()
  ensures res.Ok? ==> res.val.wf(rs)
{
  if |nodes| != |gs| then Err
  else if |gs| == 0 then Ok(Matches(map[], []))
  else match reconstruct(nodes[0], gs[0], rs) {
         case Ok(m) => match body(nodes[1..], gs[1..], rs) {
           case Ok(ms) => ms.merge(m)
           case Err => Err
         }
         case Err => Err
       }
}

function reconstruct(node : TraceNode, g : Prop, rs : RuleSet) : (res : Result<Match>)
  requires node.wf()
  ensures res.Ok? ==> res.val.thm.wf(rs)
{
  if node.i >= |rs| then Err
  else match body(node.children, rs[node.i].body, rs) {
         case Ok(ms) => match unify(g, node.prop) {
           case Ok(goal_subst) => match merge_subst(goal_subst, ms.s) {
             case Ok(s) => match mk_thm(rs, node.i, s, ms.args) {
               case Ok(thm) => Ok(Match(s, thm))
               case Err => Err
             }
             case Err => Err
           }
           case Err => Err
         }
         case Err => Err
       }
}


*/

function mk_fact(head : string, args : seq<string>, id : nat) : Rule {
  Rule(App(head, seq(|args|, i requires 0 <= i < |args| => Const(Atom(args[i])))), [], id)
}

function connectivity_rules() : RuleSet {
  [
    // connected(A, B) :- edge(A, B).
    /*0*/Rule(
      App("connected", [Var("A"), Var("B")]),
      [App("edge", [Var("A"), Var("B")])],
      0
    ),
    // connected(A, B) :- edge(A, M), connected(M, B).
    /*1*/Rule(
      App("connected", [Var("A"), Var("B")]),
      [App("edge", [Var("A"), Var("M")]), App("connected", [Var("M"), Var("B")])],
      1
    ),
    // query(S, D) :- source(S), destination(D), connected(S, D).
    /*2*/Rule(
      App("query", [Var("S"), Var("D")]),
      [
        App("source", [Var("S")]),
        App("destination", [Var("D")]),
        App("connected", [Var("S"), Var("D")])
      ],
      2
    ),

    // edge("n1", "n3").
    // edge("n1", "n2").
    // edge("n0", "n1").
    /*3*/mk_fact("edge", ["n1", "n3"], 3),
    /*4*/mk_fact("edge", ["n1", "n2"], 4),
    /*5*/mk_fact("edge", ["n0", "n1"], 5),

    // source("n0").
    // destination("n3").
    /*6*/mk_fact("source", ["n0"], 6),
    /*7*/mk_fact("destination", ["n3"], 7)
  ]
}

function connectivity_trace() : (trace : Trace)
  ensures |trace| > 0
{
  [
    //   Call: (15) query(_6418, _6420)
    Event(Call, 15, App("query", [Var("_6418"), Var("_6420")]), 2),
    //   Unify: (15) query(_6418, _6420)
    Event(Unify, 15, App("query", [Var("_6418"), Var("_6420")]), 2),
    //    Call: (16) source(_6418)
    Event(Call, 16, App("source", [Var("_6418")]), 6),
    //    Unify: (16) source("n0")
    Event(Unify, 16, App("source", [Const(Atom("n0"))]), 6),
    //    Exit: (16) source("n0")
    Event(Exit, 16, App("source", [Const(Atom("n0"))]), 6),
    //    Call: (16) destination(_6420)
    Event(Call, 16, App("destination", [Var("_6420")]), 6),
    //    Unify: (16) destination("n3")
    Event(Unify, 16, App("destination", [Const(Atom("n3"))]), 7),
    //    Exit: (16) destination("n3")
    Event(Exit, 16, App("destination", [Const(Atom("n3"))]), 7),
    //    Call: (16) connected("n0", "n3")
    Event(Call, 16, App("connected", [Const(Atom("n0")), Const(Atom("n3"))]), 0),
    //    Unify: (16) connected("n0", "n3")
    Event(Unify, 16, App("connected", [Const(Atom("n0")), Const(Atom("n3"))]), 0),
    //     Call: (17) edge("n0", "n3")
    Event(Call, 17, App("edge", [Const(Atom("n0")), Const(Atom("n3"))]), 0),
    //     Fail: (17) edge("n0", "n3")
    Event(Fail, 17, App("edge", [Const(Atom("n0")), Const(Atom("n3"))]), 0),
    //    Redo: (16) connected("n0", "n3")
    Event(Redo, 16, App("connected", [Const(Atom("n0")), Const(Atom("n3"))]), 1),
    //    Unify: (16) connected("n0", "n3")
    Event(Unify, 16, App("connected", [Const(Atom("n0")), Const(Atom("n3"))]), 1),
    //     Call: (17) edge("n0", _16264)
    Event(Call, 17, App("edge", [Const(Atom("n0")), Var("_16264")]), 5),
    //     Unify: (17) edge("n0", "n1")
    Event(Unify, 17, App("edge", [Const(Atom("n0")), Const(Atom("n1"))]), 5),
    //     Exit: (17) edge("n0", "n1")
    Event(Exit, 17, App("edge", [Const(Atom("n0")), Const(Atom("n1"))]), 5),
    //     Call: (17) connected("n1", "n3")
    Event(Call, 17, App("connected", [Const(Atom("n1")), Const(Atom("n3"))]), 0),
    //     Unify: (17) connected("n1", "n3")
    Event(Unify, 17, App("connected", [Const(Atom("n1")), Const(Atom("n3"))]), 0),
    //      Call: (18) edge("n1", "n3")
    Event(Call, 18, App("edge", [Const(Atom("n1")), Const(Atom("n3"))]), 3),
    //      Unify: (18) edge("n1", "n3")
    Event(Unify, 18, App("edge", [Const(Atom("n1")), Const(Atom("n3"))]), 3),
    //      Exit: (18) edge("n1", "n3")
    Event(Exit, 18, App("edge", [Const(Atom("n1")), Const(Atom("n3"))]), 3),
    //     Exit: (17) connected("n1", "n3")
    Event(Exit, 17, App("connected", [Const(Atom("n1")), Const(Atom("n3"))]), 0),
    //    Exit: (16) connected("n0", "n3")
    Event(Exit, 16, App("connected", [Const(Atom("n0")), Const(Atom("n3"))]), 1),
    //   Exit: (15) query("n0", "n3")
    Event(Exit, 15, App("query", [Const(Atom("n0")), Const(Atom("n3"))]), 2)
  ]
}

method run_connectivity_example() {
  var rs := connectivity_rules();
  var trace := connectivity_trace();
  run(rs, trace);
}

method run(rs : RuleSet, trace : Trace) {
  // Dump rules.
  print "rules:\n";
  var i := 0;
  while i < |rs| {
    print rs[i], "\n";
    i := i+1;
  }
  print "\n";

  // Dump trace.
  print "trace:\n";
  i := 0;
  while i < |trace| {
    print trace[i], "\n";
    i := i+1;
  }
  print "\n";

  // Build tree.
  var res := build_trace_tree(trace, 0, 0x1000_0000_0000);
  if res.Err? {
    print "error\n";
    return;
  }
  var outcome := res.val.0;
  if outcome.Failure? {
    print "failure\n";
    return;
  }
  if |outcome.nodes| == 0 {
    print "no nodes";
    return;
  }

  print "tree:\n";
  i := 0;
  while i < |outcome.nodes| {
    outcome.nodes[i].dump();
    i := i+1;
  }
  print "\n";

  // Deduce theorem.
  var root := outcome.nodes[0];
  var maybe_match := reconstruct(root, root.prop, rs);
  if maybe_match.Err? {
    print "reconstruction error\n";
    return;
  }
  print "thm: ", maybe_match.val.thm, "\n";
  print "OK\n";
}

/*
method Main() {
  run_trace_tree_build();
  // run_trace_reconstruction();
}

//// Extremely toy top-down ////

function collect_result<A>(xs : seq<Result<A>>) : (res:Result<seq<A>>)
    ensures res.Ok? ==> |res.val| == |xs| && forall j :: 0 <= j < |xs| ==> xs[j].Ok? && res.val[j] == xs[j].val
    {
        if xs == [] then Ok([]) else
        if xs[0].Ok? then
            match collect_result(xs[1..])
                case Ok(ys) => Ok([xs[0].val] + ys)
                case Err => Err
        else Err
    }

function unify_vars(s : seq<string>, t : seq<string>) : (res : Result<map<string, string>>)
    ensures res.Ok? ==> |s| == |t| && forall i :: 0 <= i < |s| ==> s[i] in res.val && res.val[s[i]] == t[i]
{
    if |s| != |t| then Err else
    if s == [] then Ok(map[]) else
        match unify_vars(s[1..], t[1..])
            case Err => Err
            case Ok(sbst) =>
                if (s[0] !in sbst) || (sbst[s[0]] == t[0]) then
                    Ok(sbst[s[0] := t[0]])
                else Err
}

function unify(r : Prop, g : Prop) : (res : Result<Subst>)
    ensures res.Ok? ==> r.complete_subst(res.val) && r.subst(res.val) == g
    {
        match (r, g)
            case (Const(v1), Const(v2)) => if v1 == v2 then Ok(map[]) else Err
            case (App(f1, args1), App(f2, args2)) =>
                if f1 == f2 then
                    match unify_vars(args1, args2)
                        case Ok(s) =>
                            assert seq(|args1|, i requires 0 <= i < |args1| => s[args1[i]]) == args2;
                            Ok(s)
                        case Err => Err
                else Err
            case _ => Err
    }

function find_unify(rs : RuleSet, goal : Prop) : (res:Result<(nat, Subst)>)
    ensures res.Ok? ==> res.val.0 < |rs| && unify(rs[res.val.0].head, goal) == Ok(res.val.1)
    {
        if rs == [] then Err else
        match unify(rs[0].head, goal)
            case Err =>
                (match find_unify(rs[1..], goal)
                    case Err => Err
                    case Ok((i, s)) => Ok((i+1, s))
                )
            case Ok(res) => Ok((0,res))
    }



// TODO:
// - only tries the first matching rule it finds
// - only works on rules without existential quantification (e.g., more variables in the body)
// - does not memoize subgoals
function top_down(rs : RuleSet, goal : Prop, bound : nat) : (res:Result<Thm>)
    ensures res.Ok? ==> res.val.wf(rs) && res.val.val == goal

    decreases bound {
        if bound == 0 then Err else
        // Find a rule that unifies with the goal; obtain rule index i, substitution s
        match find_unify(rs, goal)
            case Err => Err
            case Ok((i, s)) =>
                var rule := rs[i];
                // If the substitution s is actually good for the _entire_ rule,
                if rule.complete_subst(s) then
                    // Call top_down recursively on the rule arguments; fail if top down fails on any of them
                    var arg_thms_result := collect_result(seq(|rule.body|, j requires 0 <= j < |rule.body| =>
                        var subgoal := rule.subst(s).body[j];
                        top_down(rs, subgoal, bound-1)
                    ));
                    if arg_thms_result.Ok? then
                        // We have actually proven that mk_thm will now succeed; get the theorem and return it
                        Ok(mk_thm(rs, i, s, arg_thms_result.val).val)
                    else Err
                else Err

}

///// Also works bottom up //////

function find_new_subst(rs : RuleSet, thms : seq<Thm>) : (res : Result<(nat, Subst, seq<Thm>)>)
    requires forall i :: 0 <= i < |thms| ==> thms[i].wf(rs)
    ensures res.Ok? ==>
        res.val.0 < |rs| &&
        forall j :: 0 <= j < |res.val.2| ==> res.val.2[j].wf(rs)

function bottom_up(rs : RuleSet, acc : seq<Thm>, bound : nat) : seq<Thm>
    requires forall i :: 0 <= i < |acc| ==> acc[i].wf(rs)
    decreases bound
{
    if bound == 0 then acc else
        match find_new_subst(rs, acc)
            case Err => acc
            case Ok((i, s, args)) =>
            match mk_thm(rs, i, s, args)
                case Err => acc
                case Ok(new_thm) => bottom_up(rs, [new_thm] + acc, bound - 1)
}
*/

/*
///// Obsolete attempt at trace reconstruction.

function trace_expect(trace : Trace, port : Port) : (res : Result<(Event, Trace)>)
{
  if |trace| == 0 || trace[0].port != port then Err
  else Ok((trace[0], trace[1..]))
}

method trace_call(rs : RuleSet, g : Prop, trace : Trace, bound : nat) returns (res : Result<(Match, Trace)>)
  ensures res.Ok? ==> res.val.0.thm.wf(rs)
  decreases bound // TODO(mbm): use |trace| to prove termination
{
  if bound == 0 {
    print "exhausted bound\n";
    return Err;
  }

  // Expect the first trace to be Unify.
  // TODO(mbm): handle Call and Redo trace events
  var maybe_next := trace_expect(trace, Unify);
  if maybe_next.Err? {
    return Err;
  }
  var u := maybe_next.val.0;
  var trace := maybe_next.val.1;

  // Unify port tells us which rule we are applying.
  if u.i >= |rs| {
    print "bad rule index\n";
    return Err;
  }
  var r := rs[u.i];

  // Expect to see traces for the rule body.
  // NOTE: fragile assumption that the trace visits the rule body in the same order
  var s: Subst := map[];
  var args: seq<Thm> := [];
  var i := 0;
  while i < |r.body|
    invariant forall j :: 0 <= j < |args| ==> args[j].wf(rs)
  {
    var subgoal := r.body[i];
    var res := trace_call(rs, subgoal, trace, bound-1);
    match res {
      case Ok((m, rest)) => {
        var maybe_subst := merge_subst(s, m.s);
        match maybe_subst {
          case Ok(subst) => s := subst;
          case Err => {
            print "failed to merge substitutions\n";
            return Err;
          }
        }
        args := args + [m.thm];
        trace := rest;
      }
      case Err => {
        print "failed subgoal trace\n";
        return Err;
      }
    }
    i := i+1;
  }

  // Exit.
  // TODO(mbm): handle Fail and Redo
  if |trace| == 0 {
    print "empty trace\n";
    return Err;
  }

  var exit := trace[0];
  trace := trace[1..];
  if exit.port != Exit {
    print "unexpected trace port\n";
    return Err;
  }

  if !exit.prop.concrete() {
    print "expect concrete exit\n";
    return Err;
  }

  // Unify exit with goal.
  print "unify: g=", g, " exit=", exit.prop, "\n";
  var goal_subst: Subst;
  var maybe_subst := unify(g, exit.prop);
  match maybe_subst {
    case Ok(subst) => {
      goal_subst := subst;
    }
    case Err => {
      print "failed to unify with exit\n";
      return Err;
    }
  }

  var maybe_merged := merge_subst(s, goal_subst);
  match maybe_merged {
    case Ok(merged) => s := merged;
    case Err => {
      print "failed to merge substitution\n";
      return Err;
    }
  }

  // Deduce theorem.
  print "mk_thm: i=", u.i, " s=", s, " args=", args, "\n";
  var maybe_thm := mk_thm(rs, u.i, s, args);
  match maybe_thm {
    // TODO(mbm): trim down the subst?
    case Ok(thm) => {
      print "mk_thm: success\n";
      return Ok((Match(goal_subst, thm), trace));
    }
    case Err => {
      print "failed to deduce thm\n";
      return Err;
    }
  }
}

method run_trace_reconstruction() {
  var rs := connectivity_rules();
  var trace := connectivity_trace();
  var g := trace[0].prop;
  var res := trace_call(rs, g, trace, 0x1000_0000_0000);
  match res {
    case Ok(thm) => print "ok\n";
    case Err => print "FAIL\n";
  }
}

*/
