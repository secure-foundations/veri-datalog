type Subst = map<string, string>

datatype Term = App(head : string, args : seq<string>) | Const(val :string) {
    predicate complete_subst(s : Subst) {
        match this 
            case Const(v) => true
            case App(head, args) =>  forall i :: 0 <= i < |args| ==> args[i] in s
    }
    function subst(s : Subst) : Term
        requires complete_subst(s)
     { 
        match this
            case Const(v) => this
            case App(head, args) => 
                var args' :=
                    seq(|args|, i requires 0 <= i < |args| => s[args[i]]);
                App(head, args')
    }

}

datatype Rule = Rule(head : Term, body : seq<Term>) {
    predicate complete_subst(s : Subst) { 
        head.complete_subst(s) && (forall i :: 0 <= i < |body| ==> body[i].complete_subst(s))
    }

    function subst(s : Subst) : Rule 
        requires complete_subst(s)
    {
        var body' := seq(|body|, i requires 0 <= i < |body| => body[i].subst(s));
        Rule(head.subst(s), body')
    }
}

type RuleSet = seq<Rule>

datatype Proof = PStep(rule : Rule, s : Subst, branches : seq<Proof>) {
    function head() : Term
        requires rule.complete_subst(s) {
            rule.subst(s).head
    }
    predicate valid(rule_set : RuleSet) { 
        rule.complete_subst(s) &&
        |rule.body| == |branches| &&
        var rule' := rule.subst(s);
        forall i :: 0 <= i < |branches| ==>
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

datatype Thm = Thm(val : Term, ghost p : Proof) {
    ghost predicate wf(rule_set : RuleSet) {
        p.valid(rule_set) && p.head() == val
    }

}

function mk_thm(rs : RuleSet, i : nat, s : Subst, args : seq<Thm>) : (res : Result<Thm>)
        requires i < |rs| 
        requires forall j :: 0 <= j < |args| ==> args[j].wf(rs) 
        ensures res.Ok? ==> rs[i].complete_subst(s) && res.val.wf(rs) && res.val.val == rs[i].subst(s).head {
            var r := rs[i];
            if |args| == |r.body| && r.complete_subst(s) && (forall j :: 0 <= j < |args| ==> args[j].val == r.subst(s).body[j]) then
                var pfs := seq(|args|, i requires 0 <= i < |args| => args[i].p);
                var p := PStep(r, s, pfs); 
                Ok(Thm(r.subst(s).head, p))
            else Err
    }

///// Below here, everything is untrusted /////

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