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

function atom_strings(consts : seq<Const>) : Result<seq<string>> {
  if forall i :: 0 <= i < |consts| ==> consts[i].Atom? then
    Ok(seq(|consts|, i requires 0 <= i < |consts| => consts[i].val))
  else Err
}

function lower_char(c : char) : char {
  var i := c as int;
  if 65 <= i <= 90 then ((i + 32) as char) else c
}

function lower_string(s : string) : string {
  if |s| == 0 then s
  else if |s| == 1 then [lower_char(s[0])]
  else [lower_char(s[0])] + lower_string(s[1..])
}

datatype Builtin = NatLeq | NatGeq | NatNeq | NatLt | NatGt | SubString | StringLower | SplitString | StringChars | Length | Member | Reverse | Nth1 {
  predicate valid(args : seq<Const>) {
    match this {
      case NatLeq | NatGeq | NatNeq | NatLt | NatGt => |args| == 2 && args[0].Nat? && args[1].Nat?
      case SubString => |args| == 5 && args[0].Str? && args[1].Nat? && args[2].Nat? && args[3].Nat? && args[4].Str?
      case StringLower => |args| == 2 && args[0].Str? && args[1].Str?
      case SplitString => |args| == 4 && args[0].Str? && args[1].Str? && args[2].Str? && args[3].List?
        && args[2].s == "" // TODO: add support for padding (this line rejects any predicates that attempt to use the padding feature)
      case StringChars => |args| == 2 && args[0].Str? && args[1].List?
      case Length => |args| == 2 && args[0].List? && args[1].Nat?
      case Member => |args| == 2 && args[1].List?
      case Reverse => |args| == 2 && args[0].List? && args[1].List?
      case Nth1 => |args| == 3 && args[0].Nat? && args[1].List? && |args[1].l| > 0 && args[0].i > 0 && args[0].i <= |args[1].l|
    }
  }

  predicate eval(args : seq<Const>)
    requires valid(args)
  {
    match this {
      case NatGeq => args[0].i >= args[1].i
      case NatLeq => args[0].i <= args[1].i
      case NatNeq => args[0].i != args[1].i
      case NatLt => args[0].i < args[1].i
      case NatGt => args[0].i > args[1].i
      case SubString => (
        var str, before, len, after, sub := args[0], args[1], args[2], args[3], args[4];
        before.i+len.i+after.i == |str.s| &&
        str.s[before.i..before.i + len.i] == sub.s
      )
      case StringLower => lower_string(args[0].s) == args[1].s
      case SplitString => (
        var str, sep, pad, parts := args[0], args[1], args[2], args[3];
        match strings(parts.l) {
          case Ok(parts_strings) => str.s == string_join(sep.s, parts_strings) // TODO: add support for padding
          case Err => false
        }
      )
      case StringChars => (
        match atom_strings(args[1].l) {
          case Ok(parts_strings) => args[0].s == string_join("", parts_strings)
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
      case Nth1 => args[1].l[args[0].i-1] == args[2]
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
  [Rule(App("foo", [Var("x")]), [BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Const(Str("")), Var("x")])], 0)]
}

function tst_string_split_thm() : Result<Thm> {
  var prop := BuiltinOp(SplitString, [Const(Str("a.b")), Const(Str(".")), Const(Str("")), Const( List( [Str("a"), Str("b")]))]);
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
  case (BuiltinOp(f1, args1), BuiltinOp(f2, args2)) =>
    if f1 == f2 then unify_terms(args1, args2) else Err
  case (Eq(left1, right1), Eq(left2, right2)) => (
    var x := unify_terms([left1], [left2]);
    var y := unify_terms([right1], [right2]);
    match (x, y)
    case (Ok(xval), Ok(yval)) => merge_subst(xval, yval)
    case _ => Err
  )
  case _ => Err
}

method print_event(e: Event) {
  var j := e.level;
  while j > 11 {
    print "  ";
    j := j - 1;
  }
  print e.prop;
  print "\n";
}

/*
 * This method takes the trace output of a program and that program's rules, and then returns
 * a proof of the correctness of that program.
 */
method build_proof_tree(trace: Trace, rs: RuleSet) returns (res : Result<(Thm, Trace)>)
  requires forall j :: 0 <= j < |trace| ==> trace[j].prop.concrete()
  requires |trace| > 0
  ensures res.Ok? ==> forall j :: 0 <= j < |res.val.1| ==> res.val.1[j].prop.concrete()
  ensures res.Ok? ==> |res.val.1| <= |trace|
  ensures res.Ok? ==> res.val.0.wf(rs)
  decreases |trace|
{
  // Here, the last element of the trace is popped and stored in head.
  var trace' := trace;
  var head := trace'[|trace'|-1];
  trace' := trace'[..|trace'|-1];

  match head.prop {
    case Eq(l, r) => {
      var maybe_leaf := mk_leaf(Eq(l, r));
      match maybe_leaf {
        case Ok(thm) => {
          print_event(head); // for debugging
          return Ok((thm, trace'));
        }
        case Err => {
          print "failed to deduce eq\n";
          return Err;
        }
      }
    }
    case BuiltinOp(b, args) => {
      var maybe_leaf := mk_leaf(BuiltinOp(b, args));
      match maybe_leaf {
        case Ok(thm) => {
          print_event(head); // for debugging
          return Ok((thm, trace'));
        }
        case Err => {
          print "failed to deduce builtin\n";
          return Err;
        }
      }
    }
    case App(_, _) => { // This triggers if head's prop is a fact or a non-builtin predicate.
      // The rule used by the prop is stored.
      var ri: nat;
      var maybe_ri := lookup_rule(rs, head.i);
      match maybe_ri {
        case Ok(index) => ri := index;
        case Err => {
          print "could not find rule\n";
          return Err;
        }
      }
      var r := rs[ri];

      var args: seq<Thm> := []; // `args` holds the child theorems of this part of the proof tree.
      var assignment := map[]; // `assignment` is the substitution used for holding the variable assignment at this part of the proof tree.
      // Here, the variable information that can be determined directly from the prop is stored in `assignment`.
      var maybe_assignment := unify(r.head, head.prop);
      match maybe_assignment {
        case Ok(substitution) => assignment := substitution;
        case Err => {
          print "could not create assignment\n";
          return Err;
        }
      }

      // The program loops through the rule's children in the search for trace events that match with them.
      for i := |r.body| downto 0
        invariant forall j :: 0 <= j < |trace'| ==> trace'[j].prop.concrete()
        invariant |trace'| < |trace|
        invariant forall j :: 0 <= j < |args| ==> args[j].wf(rs)
      {
        // This while loop skips over all ineligble trace events until it finds one that matches with the next child rule.
        while |trace'| > 0
          invariant forall j :: 0 <= j < |trace'| ==> trace'[j].prop.concrete()
          invariant |trace'| < |trace|
          decreases |trace'|
        {
          if trace'[|trace'|-1].level != head.level + 1 {
            trace' := trace'[..|trace'|-1];
            continue;
          }
          var new_subst := map[];
          var maybe_new_subst := unify(r.body[i], trace'[|trace'|-1].prop);
          match maybe_new_subst {
            case Ok(substitution) => new_subst := substitution;
            case Err => {
              trace' := trace'[..|trace'|-1];
              continue;
            }
          }
          var maybe_assignment := merge_subst(assignment, new_subst);
          match maybe_assignment {
            case Ok(substitution) => assignment := substitution;
            case Err => {
              trace' := trace'[..|trace'|-1];
              continue;
            }
          }
          break;
        }
        if |trace'| == 0 {
          print "trace consumed earlier than expected\n";
          return Err;
        }

        // The succesfully matched trace event is used to create a sub proof tree.
        var res := build_proof_tree(trace', rs);
        if res.Err? {
          print "error\n";
          return Err;
        }
        trace' := res.val.1; // The trace is updated to reflect the popping of elements inside the recursion.
        args := [res.val.0] + args; // The sub proof tree is stored in this list.
      }

      // The proof trees from the children are used to make the proof for this part of the tree.
      var maybe_thm := mk_thm(rs, ri, assignment, args);
      match maybe_thm {
        case Ok(thm) => {
          print_event(head); // for debugging
          return Ok((thm, trace'));
        }
        case Err => {
          print "failed to deduce thm\n";
          return Err;
        }
      }
    }
  }
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

  // Deduce theorem.
  if |trace| == 0 {
    print "There is no trace because it did not succeed.\n";
    return;
  }
  if !(forall j :: 0 <= j < |trace| ==> trace[j].prop.concrete()) {
    print "The trace is not entirely concrete.\n";
    return;
  }
  print "tree:\n"; // if there was a flag that disabled printing in build_proof_tree, this line should be disabled as well
  var maybe_match := build_proof_tree(trace, rs);
  print "\n"; // if there was a flag that disabled printing in build_proof_tree, this line should be disabled as well
  if maybe_match.Err? {
    print "reconstruction error\n";
    return;
  }
  print "thm: ", maybe_match.val.0, "\n";
  print "OK\n";
}
