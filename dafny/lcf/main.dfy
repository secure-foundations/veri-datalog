
datatype Const = Atom(val : string) | Nat(i : nat)
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

datatype NatPred = Leq | Geq | Neq {
    function eval(x : nat, y:nat) : bool {
        match this
          case Leq => x <= y
          case Geq => x >= y
          case Neq => x != y
    }
}

datatype Prop = App(head : string, args : seq<Term>) | Eq(l : Term, r : Term) | NatPred(p : NatPred, l : Term, r : Term) {
    predicate complete_subst(s : Subst) { 
        match this
            case App(head, args) => forall i :: 0 <= i < |args| ==> args[i].complete_subst(s)
            case Eq(x, y) => x.complete_subst(s) && y.complete_subst(s)
            case NatPred(_, x, y) => x.complete_subst(s) && y.complete_subst(s)
    }
    predicate concrete() {
        match this
            case App(head, args) => forall i :: 0 <= i < |args| ==> args[i].concrete()
            case Eq(x, y) => x.concrete() && y.concrete()
            case NatPred(_, x, y) => x.concrete() && y.concrete()
    }
    function subst(s : Subst) : (res:Prop)    
        requires complete_subst(s)
        ensures res.concrete()
        {
        match this
            case App(h, args) => App(h, seq(|args|, i requires 0 <= i < |args| => args[i].subst(s))) 
            case Eq(x, y) => Eq(x.subst(s), y.subst(s))
            case NatPred(p, x, y) => NatPred(p, x.subst(s), y.subst(s))
    }
    predicate symbolic() { 
        this.App?
    }

    predicate valid()
        requires !symbolic()
        requires concrete() {
        match this  
            case Eq(x, y) => x.val == y.val
            case NatPred(p, x, y) => x.val.Nat? && y.val.Nat? && (p.eval(x.val.i, y.val.i) == true)
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

function tst() : RuleSet {
    [Rule(App("foo", [Var("x")]), [NatPred(Leq, Var("x"), Const(Nat(3)))])]
} 

function tst_thm() : Result<Thm> { 
    var lf := mk_leaf(NatPred(Leq, Const(Nat(3)), Const(Nat(3)))).val;
    var s : Subst := map["x" := Nat(3)];
    Ok(mk_thm(tst(), 0, s, [lf]).val)
}


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