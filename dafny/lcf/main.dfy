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

datatype Rule = Rule(head : Prop, body : seq<Prop>) {
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
    Rule(head.subst(s), body')
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
  [Rule(App("foo", [Var("x")]), [BuiltinOp(NatLeq, [Var("x"), Const(Nat(3))])])]
}

function tst_nat_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(NatLeq, [Const(Nat(3)), Const(Nat(3))])).val;
  var s : Subst := map["x" := Nat(3)];
  Ok(mk_thm(tst_nat(), 0, s, [lf]).val)
}

/*
function tst_sub_string() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(SubString, [Const(Str("hello world!")), Const(Nat(6)), Const(Nat(5)), Const(Nat(1)), Var("x")])])]
}

function tst_sub_string_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(SubString, [Const(Str("hello world!")), Const(Nat(6)), Const(Nat(5)), Const(Nat(1)), Const(Str("world"))] )).val;
  var s : Subst := map["x" := Str("world")];
  Ok(mk_thm(tst_sub_string(), 0, s, [lf]).val)
}

function tst_split_string() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Var("x")])])]
}

function tst_string_split_thm() : Result<Thm> {
  var prop := BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Const( List( [Str("a"), Str("b")]))]);
  assert prop.valid();
  var lf := mk_leaf(prop).val;
  var s : Subst := map["x" :=  List([Str("a"), Str("b")])];
  Ok(mk_thm(tst_split_string(), 0, s, [lf]).val)
}

function tst_length() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Length, [Const(List([Nat(1), Nat(2), Nat(3)])), Var("x")])])]
}

function tst_length_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Length, [Const(List([Nat(1), Nat(2), Nat(3)])), Const(Nat(3))])).val;
  var s : Subst := map["x" := Nat(3)];
  Ok(mk_thm(tst_length(), 0, s, [lf]).val)
}

function tst_member() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Member, [Var("x"), Const(List([Nat(1), Nat(2), Nat(3)]))])])]
}

function tst_member_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Member, [Const(Nat(2)), Const(List([Nat(1), Nat(2), Nat(3)]))])).val;
  var s : Subst := map["x" := Nat(2)];
  Ok(mk_thm(tst_member(), 0, s, [lf]).val)
}

function tst_reverse() : RuleSet {
  [Rule(App("foo", [Var("x")]), [BuiltinOp(Reverse, [Const(List([Nat(1), Nat(2), Nat(3)])), Var("x")])])]
}

function tst_reverse_thm() : Result<Thm> {
  var lf := mk_leaf(BuiltinOp(Reverse, [
                                Const(List([Nat(1), Nat(2), Nat(3)])),
                                Const(List([Nat(3), Nat(2), Nat(1)]))
                              ])).val;
  var s : Subst := map["x" := List([Nat(3), Nat(2), Nat(1)])];
  Ok(mk_thm(tst_reverse(), 0, s, [lf]).val)
}
*/

//// Trace Reconstruction

datatype Port = Call | Unify | Redo | Exit | Fail

datatype Event = Event(port : Port, level : nat, prop : Prop, i : nat)

type Trace = seq<Event>

datatype Frame = Frame(level : nat, s : Subst, args: seq<Thm>)

method verify_trace(rs : RuleSet, trace : Trace) returns (res : Result<Thm>)
  //ensures res.Ok? ==> res.val.prop == Last(trace).prop
{
  var stack: seq<Frame> := [];
  var level := 0;
  var i := 0;
  while i < |trace| {
    var event := trace[i];
    i := i+1;

    match event.port {
      case Unify => {
        if event.level <= level {
          return Err;
        }
        var s: Subst := map[];
        var frame := Frame(level, s, []);
        stack := stack + [frame];
        level := frame.level;
      }

      case Exit => continue;

      case Call => continue;
      case Redo => continue;
      case Fail => continue;
    }
  }
  return Err;
}

function mk_fact(head : string, args : seq<string>) : Rule {
  Rule(App(head, seq(|args|, i requires 0 <= i < |args| => Const(Atom(args[i])))), [])
}

function connectivity_rules() : RuleSet {
  [
    // connected(A, B) :- edge(A, B).
    Rule(
      App("connected", [Var("A"), Var("B")]),
      [App("edge", [Var("A"), Var("B")])]
    ),
    // connected(A, B) :- edge(A, M), connected(M, B).
    Rule(
      App("connected", [Var("A"), Var("B")]),
      [App("edge", [Var("A"), Var("M")]), App("edge", [Var("M"), Var("B")])]
    ),
    // query(S, D) :- source(S), destination(D), connected(S, D).
    Rule(
      App("query", [Var("S"), Var("D")]),
      [
        App("source", [Var("S")]),
        App("destination", [Var("D")]),
        App("connected", [Var("S"), Var("D")])
      ]
    ),

    // edge("n1", "n3").
    // edge("n1", "n2").
    // edge("n0", "n1").
    mk_fact("edge", ["n1", "n3"]),
    mk_fact("edge", ["n1", "n2"]),
    mk_fact("edge", ["n0", "n1"]),

    // source("n0").
    // destination("n1").
    mk_fact("source", ["n0"]),
    mk_fact("destination", ["n1"])
  ]
}

function connectivity_trace() : Trace {
  [
    //   Call: (15) query(_6418, _6420)
    //   Unify: (15) query(_6418, _6420)
    Event(Unify, 15, App("query", [Var("_6418"), Var("_6420")]), 0),
    //    Call: (16) source(_6418)
    //    Unify: (16) source("n0")
    Event(Unify, 16, App("source", [Const(Atom("n0"))]), 0)
    //    Exit: (16) source("n0")
    //    Call: (16) destination(_6420)
    //    Unify: (16) destination("n3")
    //    Exit: (16) destination("n3")
    //    Call: (16) connected("n0", "n3")
    //    Unify: (16) connected("n0", "n3")
    //     Call: (17) edge("n0", "n3")
    //     Fail: (17) edge("n0", "n3")
    //    Redo: (16) connected("n0", "n3")
    //    Unify: (16) connected("n0", "n3")
    //     Call: (17) edge("n0", _16264)
    //     Unify: (17) edge("n0", "n1")
    //     Exit: (17) edge("n0", "n1")
    //     Call: (17) connected("n1", "n3")
    //     Unify: (17) connected("n1", "n3")
    //      Call: (18) edge("n1", "n3")
    //      Unify: (18) edge("n1", "n3")
    //      Exit: (18) edge("n1", "n3")
    //     Exit: (17) connected("n1", "n3")
    //    Exit: (16) connected("n0", "n3")
    //   Exit: (15) query("n0", "n3")
  ]
}

// method Main() {
//
// }

/*



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
