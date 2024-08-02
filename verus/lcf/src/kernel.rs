use crate::string_hash_map::TmpStringHashMap;
use vstd::assert_seqs_equal;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

pub enum Const {
    Atom(String),
    Nat(u64),
    Str(String),
}

impl PartialEq for Const {
    //allows for Const types to be evaluated for equality and aid Verus verifier; not fully sufficient.
    //Must call const_eq for Atoms and Strs
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Const::Atom(s), Const::Atom(t)) => s == t,
            (Const::Nat(u), Const::Nat(v)) => u == v,
            (Const::Str(s), Const::Str(t)) => s == t,
            (Const::Atom(_), Const::Nat(_)) | (Const::Nat(_), Const::Atom(_)) => false,
            (Const::Atom(_), Const::Str(_)) | (Const::Str(_), Const::Atom(_)) => false,
            (Const::Str(_), Const::Nat(_)) | (Const::Nat(_), Const::Str(_)) => false,
        }
    }
}

impl Const {
    // uses eq from impl Partial Eq to prove equality between items
    pub fn const_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Const::Atom(s), Const::Atom(t)) => s.eq(t),
            (Const::Nat(u), Const::Nat(v)) => u == v,
            (Const::Str(s), Const::Str(t)) => s.eq(t),
            _ => false,
        }
    }
}

impl Clone for Const {
    //explicitly copies and instantiates the original value so that it fixes borrowing errors.
    //it is needed when you want to borrow a value that will produce an error when you try to
    fn clone(&self) -> (res: Self)
        ensures
            self.deep_view() == res.deep_view(),
    {
        match self {
            Const::Atom(s) => Const::Atom(s.clone()),
            Const::Nat(n) => Const::Nat(*n),
            Const::Str(s) => Const::Str(s.clone()),
        }
    }
}

pub enum SpecConst {
    Atom(Seq<char>),
    Nat(u64),
    Str(Seq<char>),
}

impl DeepView for Const {
    type V = SpecConst;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Const::Atom(s) => SpecConst::Atom(s.view()),
            Const::Nat(n) => SpecConst::Nat(*n),
            Const::Str(s) => SpecConst::Str(s.view()),
        }
    }
}

// Utilizing TmpStringHashMap from string_hash_map.rs
type Subst = TmpStringHashMap<Const>;

// Using a map with spec-level types to reason about Subst
type SpecSubst = Map<Seq<char>, SpecConst>;

//checks if all elements of one specSubst type are present in the other
// specific triggers were chosen because auto triggers could not be determined by the verifier
spec fn compatible_subst(s: SpecSubst, t: SpecSubst) -> bool {
    forall|v: String| (#[trigger] s[v@]) == (#[trigger] t[v@])
}

pub enum Term {
    Const(Const),
    Var(String),
}

pub enum SpecTerm {
    Const(SpecConst),
    Var(Seq<char>),
}

impl DeepView for Term {
    type V = SpecTerm;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Term::Const(c) => SpecTerm::Const(c.deep_view()),
            Term::Var(s) => SpecTerm::Var(s.view()),
        }
    }
}

impl Clone for Term {
    //explicitly copies and instantiates the original value into a new item so that it fixes borrowing errors.
    //it is needed when you want to borrow a value that will produce an error when you try to
    fn clone(&self) -> (res: Self)
        ensures
            self.deep_view() == res.deep_view(),
    {
        match self {
            Term::Var(s) => Term::Var(s.clone()),
            Term::Const(c) => Term::Const(c.clone()),
        }
    }
}

impl PartialEq for Term {
    //allows for Term types to be evaluated for equality and aid Verus verifier; not fully sufficient.
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Term::Const(c), Term::Const(d)) => c == d,
            (Term::Var(s), Term::Var(t)) => s == t,
            (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,
        }
    }
}

impl SpecTerm {
    //returns true if the map contains the key when it a Var variant, or if it is Const variant
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        match self {
            SpecTerm::Var(v) => s.contains_key(v),
            SpecTerm::Const(_) => true,
        }
    }

    //checks if SpecTerm is a base type
    pub open spec fn spec_concrete(self) -> bool {
        self is Const
    }

    //reasons about substitution from Var variants to Const or does nothing if it is a Const variant
    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecTerm)
        recommends
            self.spec_complete_subst(s),
    {
        match self {
            SpecTerm::Var(v) => {
                let u_option = s.index(v);
                SpecTerm::Const(u_option)
            },
            SpecTerm::Const(_) => self,
        }
    }
}

impl Term {
    //proves equality for Term types
    pub fn term_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Term::Const(s), Term::Const(t)) => Const::const_eq(&s, &t),
            (Term::Var(u), Term::Var(v)) => u.eq(v),
            _ => false,
        }
    }

    //checks whether Term items are either Const or are Vars with a key in the Subst TmpStringHashMap
    pub fn complete_subst(self, s: &Subst) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        match self {
            Term::Var(v) => s.contains_key(v.as_str()),
            Term::Const(_) => true,
        }
    }

    //checks if term variant is a base type
    pub fn concrete(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        match self {
            Term::Const(_) => true,
            Term::Var(_) => false,
        }
    }

    //performs a substitution to achieve a Const variant of Term
    pub fn subst(self, s: &Subst) -> (res: Term)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view().spec_concrete(),
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
    {
        match self {
            Term::Var(v) => {
                let u_option = s.get(v.as_str());
                Term::Const(u_option.unwrap().clone())
            },
            Term::Const(_) => self,
        }
    }
}

//#[verifier::external_body] needed because the verifier does not support the equality relation we are trying to leverage
#[verifier::external_body]
//checks whether 2 Vec<Term>s are equal or not
pub fn terms_eq(a: &Vec<Term>, b: &Vec<Term>) -> (res: bool)
    ensures
        res <==> a.deep_view() == b.deep_view(),
{
    a == b
}

pub enum Prop {
    App(String, Vec<Term>),
    Eq(Term, Term),
}

pub enum SpecProp {
    App(Seq<char>, Seq<SpecTerm>),
    Eq(SpecTerm, SpecTerm),
}

impl DeepView for Prop {
    type V = SpecProp;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Prop::App(s, v) => SpecProp::App(s.view(), v.deep_view()),
            Prop::Eq(t, e) => SpecProp::Eq(t.deep_view(), e.deep_view()),
        }
    }
}

impl Clone for Prop {
    //#[verifier::external_body] needed to satisfy postcondition on line 253.
    #[verifier::external_body]
    //explicitly copies and instantiates the original value into a new item so that it fixes borrowing errors.
    //it is needed when you want to borrow a value that will produce an error when you try to
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        match self {
            Prop::App(s, v) => Prop::App(s.clone(), v.clone()),
            Prop::Eq(t, e) => Prop::Eq(t.clone(), e.clone()),
        }
    }
}

impl PartialEq for Prop {
    //aids verus verifier in reasoning about equality; not fully sufficient - must call prop_eq for certain types
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Prop::App(s, v), Prop::App(t, w)) => s == t && v == w,
            (Prop::Eq(a, b), Prop::Eq(c, d)) => a == c && b == d,
            (Prop::App(_, _), Prop::Eq(_, _)) | (Prop::Eq(_, _), Prop::App(_, _)) => false,
        }
    }
}

impl SpecProp {
    //checks if Prop variants contain key to map; calls spec_complete_subst from Term
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        match self {
            SpecProp::App(head, args) => forall|i: int|
                #![auto]
            //forall checks every index in list of SpecTerms in args to check if they are complete substitutions

                0 <= i < args.len() ==> args[i].spec_complete_subst(s),
            SpecProp::Eq(x, y) => x.spec_complete_subst(s) && y.spec_complete_subst(s),
        }
    }

    //checks if Prop variants are of base types
    pub open spec fn spec_concrete(self) -> bool {
        match self {
            SpecProp::App(head, args) => forall|i: int|
                #![auto]
            //forall checks every index in list of SpecTerms in args to check if they are concrete

                0 <= i < args.len() ==> args[i].spec_concrete(),
            SpecProp::Eq(x, y) => x.spec_concrete() && y.spec_concrete(),
        }
    }

    //checks if SpecProp is an App variant
    pub open spec fn spec_symbolic(self) -> bool {
        self is App
    }

    //checks whether valid SpecProp types are concrete and are equal
    pub open spec fn spec_valid(self) -> bool {
        if self.spec_symbolic() || !(self.spec_concrete()) {
            false
        } else {
            match self {
                SpecProp::Eq(x, y) => match (x, y) {
                    (SpecTerm::Const(x), SpecTerm::Const(y)) => x == y,
                    (SpecTerm::Var(x), SpecTerm::Var(y)) => false,
                    (SpecTerm::Const(_), SpecTerm::Var(_))
                    | (SpecTerm::Var(_), SpecTerm::Const(_)) => false,
                },
                SpecProp::App(s, v) => false,
            }
        }
    }

    //reasons about substitution of SpecProp variants to SpecTerms
    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecProp)
        recommends
            self.spec_complete_subst(s),
    {
        match self {
            SpecProp::App(h, args) => {
                let new_sequence = args.map_values(|p: SpecTerm| p.spec_subst(s));
                SpecProp::App(h, new_sequence)
            },
            SpecProp::Eq(x, y) => SpecProp::Eq(x.spec_subst(s), y.spec_subst(s)),
        }
    }
}

impl Prop {
    //proves equality for Prop types. uses term_eq and terms_eq
    pub fn prop_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Prop::App(a, b), Prop::App(c, d)) => a.eq(c) && terms_eq(b, d),
            (Prop::Eq(h, i), Prop::Eq(j, k)) => Term::term_eq(h, j) && Term::term_eq(i, k),
            _ => false,
        }
    }

    //checks whether Prop variants are concrete and elements are equal to each other
    pub fn valid(self) -> (res: bool)
        requires
            !self.deep_view().spec_symbolic(),
            self.deep_view().spec_concrete(),
        ensures
            res <==> self.deep_view().spec_valid(),
    {
        match self {
            Prop::Eq(x, y) => match (x, y) {
                //const_eq was needed here because the verifier cannot evaluate x == y on its own
                (Term::Const(x), Term::Const(y)) => Const::const_eq(&x, &y),
                (Term::Var(x), Term::Var(y)) => false,
                (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,
            },
            Prop::App(s, v) => false,
        }
    }

    //checks whether Prop is an App variant
    pub fn symbolic(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_symbolic(),
    {
        match self {
            Prop::App(_, _) => true,
            Prop::Eq(_, _) => false,
        }
    }

    //checks whether Prop variants are base types
    pub fn concrete(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        match self {
            Prop::App(head, args) => {
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                     //specific placement of trigger after calling deep_view on all elements of args of type Term to SpecTerm

                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                //Next block of code uses a flag calculation instead of forall statement
                let mut flag = true;
                for i in 0..args.len()
                    invariant
                        0 <= i <= args.len(),
                        //forall statement used in invariant to reason about concrete property for all indices of args seq
                        flag <==> forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_concrete(),
                {
                    flag = args[i].clone().concrete() && flag;
                }
                flag
            },
            Prop::Eq(x, y) => x.concrete() && y.concrete(),
        }
    }

    //checks if Prop variants contain key in Susbt TmpStringHashMap
    pub fn complete_subst(&self, s: &Subst) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        match self {
            Prop::App(head, args) => {
                //assertion uses forall in App case to show that spec and exec versions are equal
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                //Next block of code uses a flag calculation instead of forall statement
                let mut flag = true;
                for i in 0..args.len()
                    invariant
                        0 <= i <= args.len(),
                        //forall statement used in invariant to reason about complete_subst property for all indices of args seq
                        flag <==> forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_complete_subst(s.deep_view()),
                {
                    flag = args[i].clone().complete_subst(s) && flag;
                }
                flag
            },
            Prop::Eq(x, y) => x.clone().complete_subst(s) && y.clone().complete_subst(s),
        }
    }

    //performs substitution on Prop types and converts them to base types
    pub fn subst(&self, s: &Subst) -> (res: Prop)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
            res.deep_view().spec_concrete(),
    {
        match self {
            Prop::App(h, args) => {
                //assertion uses forall in App case to show that spec and exec versions are equal
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                let mut v = Vec::<Term>::new();
                for i in 0..args.len()
                //loop invariants reason about properties such as complete_subst, concrete, and the result of subst

                    invariant
                        0 <= i <= args.len(),
                        v.len() == i,
                        forall|j: int|
                            0 <= j < args.deep_view().len() ==> (
                            #[trigger] args[j as int].deep_view().spec_complete_subst(
                                s.deep_view(),
                            )),
                        //forall statement reasons about the result and the input having functions applied in
                        forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_subst(s.deep_view())
                                == v[j].deep_view(),
                        //forall statement showing that all elements in result are concrete
                        forall|j: int| #![auto] 0 <= j < i ==> v[j].deep_view().spec_concrete(),
                {
                    v.push(args[i].clone().subst(s));
                }
                //lemma that asserts that two seqs are equal using map_values on SpecTerm type

                proof {
                    assert_seqs_equal!(v.deep_view(), args.deep_view().map_values(|p: SpecTerm| p.spec_subst(s.deep_view())));
                }
                ;
                Prop::App(h.clone(), v)
            },
            Prop::Eq(x, y) => Prop::Eq(x.clone().subst(s), y.clone().subst(s)),
        }
    }
}

pub struct Rule {
    pub head: Prop,
    pub body: Vec<Prop>,
    pub id: u64,
}

pub struct SpecRule {
    pub head: SpecProp,
    pub body: Seq<SpecProp>,
    pub id: u64,
}

impl DeepView for Rule {
    type V = SpecRule;

    open spec fn deep_view(&self) -> Self::V {
        SpecRule { head: self.head.deep_view(), body: self.body.deep_view(), id: self.id }
    }
}

impl PartialEq for Rule {
    //allows for Rule types to be evaluated for equality and aid Verus verifier; not fully sufficient.
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        self.head == other.head && self.body == other.body && self.id == other.id
    }
}

impl Clone for Rule {
    //#[verifier::external_body] needed to satisfy postcondition on line 513
    #[verifier::external_body]
    //explicitly copies and instantiates the original value into a new item so that it fixes borrowing errors.
    //it is needed when you want to borrow a value that will produce an error when you try to
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        Rule { head: self.head.clone(), body: self.body.clone(), id: self.id.clone() }
    }
}

impl SpecRule {
    //checks all items in SpecRule for being complete substitutions in SpecSubst
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        &&& self.head.spec_complete_subst(
            s,
        )
        //forall statement checking if all indices in the seq of props
        &&& forall|i: int| #![auto] 0 <= i < self.body.len() ==> self.body[i].spec_complete_subst(s)
    }

    //checks if SpecRule contains items that are all base types
    pub open spec fn spec_concrete(self) -> bool {
        self.head.spec_concrete() && forall|i: int|
            #![auto]
        //forall statement that checks if all indices in seq of props are concrete

            0 <= i < self.body.len() ==> self.body[i].spec_concrete()
    }

    //checks if SpecRule's SpecProp item is of type App before being entered into SpecRuleset
    pub open spec fn spec_wf(self) -> bool {
        self.head.spec_symbolic()
    }

    //reasons about a substitution for SpecRule to SpecProp
    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecRule)
        recommends
            self.spec_complete_subst(s),
    {
        let new_sequence = self.body.map_values(|p: SpecProp| p.spec_subst(s));
        let result = SpecRule { head: self.head.spec_subst(s), body: new_sequence, id: self.id };
        result
    }
}

impl Rule {
    //performs a substition from type Rule to Prop
    pub fn subst(&self, s: &Subst) -> (res: Rule)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view().spec_concrete(),
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
            res.body.view().len() == self.body.view().len(),
    {
        let mut v = Vec::<Prop>::new();
        //assertion uses forall statement to show the two positions of deep_view are the same result
        assert(forall|k: int|
            0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                == self.deep_view().body[k]);
        for i in 0..self.body.len()
            invariant
        //loop invariants reason about properties such as complete_subst, concrete, and the result of subst

                0 <= i <= self.body.len(),
                v.len() == i,
                forall|i: int|
                    #![auto]
                //forall statement that checks all indices in body to see if they are complete subsitutions

                    0 <= i < self.body.deep_view().len()
                        ==> self.body[i].deep_view().spec_complete_subst(s.deep_view()),
                forall|j: int|
                    #![auto]
                //forall statement that checks all indices in body to check if the result is the same as the body index calling subst

                    0 <= j < i ==> self.body[j].deep_view().spec_subst(s.deep_view())
                        == v[j].deep_view(),
                //forall statement that checks all indices of the result for concreteness
                forall|j: int| #![auto] 0 <= j < i ==> v[j].deep_view().spec_concrete(),
        {
            v.push(self.body[i].subst(s));
        }
        //lemma that asserts that two seqs are equal using map_values on SpecProp type

        proof {
            assert_seqs_equal!(v.deep_view(), self.body.deep_view().map_values(|p: SpecProp| p.spec_subst(s.deep_view())));
        }
        ;
        let result = Rule { head: self.head.subst(s), body: v, id: self.id };
        result
    }

    //checks if all items in Rule are complete substitutions
    pub fn complete_subst(&self, s: &Subst) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        self.head.complete_subst(s) && {
            //assertion uses forall in body of rule to show that spec and exec versions are equal
            assert(forall|k: int|
                0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                    == self.deep_view().body[k]);
            //using flag to check if all elements in the body are complete substitutions
            let mut flag = true;
            for i in 0..self.body.len()
                invariant
                    0 <= i <= self.body.len(),
                    flag <==> forall|j: int|
                        #![auto]
                    //invariant forall checks all body elements if they are complere susbtitutions using deep_view

                        0 <= j < i ==> self.body[j].deep_view().spec_complete_subst(s.deep_view()),
            {
                flag = self.body[i].clone().complete_subst(s) && flag
            }
            flag
        }
    }

    //checks whether Rule type contains only base types
    pub fn concrete(&self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        self.head.clone().concrete() && {
            //assertion uses forall for body in rule to show that spec and exec versions are equal
            assert(forall|k: int|
                0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                    == self.deep_view().body[k]);
            //using flag to check if all elements in the body are concrete
            let mut flag = true;
            for i in 0..self.body.len()
                invariant
                    0 <= i <= self.body.len(),
                    flag <==> forall|j: int|
                        #![auto]
                    //invariant forall checks if all indices in body are concrete

                        0 <= j < i ==> self.body[j].deep_view().spec_concrete(),
            {
                flag = self.body[i].clone().concrete() && flag
            }
            flag
        }
    }

    //checks if Rule contains App variants before adding it to Ruleset
    pub fn wf(&self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_wf(),
    {
        self.head.clone().symbolic()
    }
}

pub struct RuleSet {
    pub rs: Vec<Rule>,
}

pub struct SpecRuleSet {
    pub rs: Seq<SpecRule>,
}

impl DeepView for RuleSet {
    type V = SpecRuleSet;

    open spec fn deep_view(&self) -> Self::V {
        SpecRuleSet { rs: self.rs.deep_view() }
    }
}

impl SpecRuleSet {
    //checks if all items in SpecRuleset are well-formed
    pub open spec fn spec_wf(self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.rs.len() ==> self.rs[i].spec_wf()
    }
}

impl RuleSet {
    //checks whether all items in RuleSet are well-formed
    pub fn wf(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_wf(),
    {
        //using flag to check if all elements in the body are well formed
        let mut flag = true;
        assert(forall|k: int|
            0 <= k < self.rs.len() ==> (#[trigger] self.rs[k].deep_view())
                == self.deep_view().rs[k]);
        for i in 0..self.rs.len()
            invariant
                0 <= i <= self.rs.len(),
                //invariant forall checks all body elements if they are well formed using deep_view
                flag <==> forall|j: int| #![auto] 0 <= j < i ==> self.rs[j].deep_view().spec_wf(),
        {
            flag = self.rs[i].wf() && flag
        }
        flag
    }
}

pub enum Proof {
    Pstep(Rule, Subst, Vec<Proof>),
    QED(Prop),
}

pub enum SpecProof {
    Pstep(SpecRule, SpecSubst, Seq<SpecProof>),
    QED(SpecProp),
}

impl DeepView for Proof {
    type V = SpecProof;

    closed spec fn deep_view(&self) -> Self::V;
}

//#[verifier::external_body] needed due to issue verus-lang/verus#1222
#[verifier::external_body]
//allows us to reason about deep_view
pub proof fn axiom_proof_deep_view(pf: &Proof)
    ensures
//these matches statements ensure that exec and spec values are the same

        pf matches Proof::Pstep(r, s, v) ==> (#[trigger] pf.deep_view()) matches SpecProof::Pstep(
            spec_r,
            spec_s,
            spec_v,
        ) && r.deep_view() == spec_r && s.deep_view() == spec_s && v.deep_view() == spec_v,
        pf matches Proof::QED(p) ==> pf.deep_view() matches SpecProof::QED(spec_p) && p.deep_view()
            == spec_p,
{
}

impl PartialEq for Proof {
    //allows for Rule types to be evaluated for equality and aid Verus verifier; not fully sufficient.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Proof::Pstep(a, b, c), Proof::Pstep(d, e, f)) => a == d && b == e && c == f,
            (Proof::QED(p), Proof::QED(q)) => p == q,
            (Proof::Pstep(_, _, _), Proof::QED(_))
            | (Proof::QED(_), Proof::Pstep(_, _, _)) => false,
        }
    }
}

impl Clone for Proof {
    //#[verifier::external_body] needed because the verifier thinks it found a cycle
    #[verifier::external_body]
    //explicitly copies and instantiates the original value into a new item so that it fixes borrowing errors.
    //it is needed when you want to borrow a value that will produce an error when you try to
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        match self {
            Proof::Pstep(r, s, v) => Proof::Pstep(r.clone(), s.clone(), v.clone()),
            Proof::QED(p) => Proof::QED(p.clone()),
        }
    }
}

impl SpecProof {
    //checking if the Proof is valid by applying specs on its SpecRuleSet items
    pub open spec fn spec_valid(self, rule_set: SpecRuleSet) -> bool
        decreases self,
    {
        match self {
            SpecProof::QED(p) => p.spec_concrete() && !p.spec_symbolic() && p.spec_valid(),
            SpecProof::Pstep(rule, s, branches) => rule_set.rs.contains(rule)
                && rule.spec_complete_subst(s) && rule.body.len() == branches.len() && {
                let rule1 = rule.spec_subst(s);
                //forall statement goes through all indices of the branches and subsituted rule bodies to check for equality
                forall|i: int|
                    #![auto]
                    0 <= i < rule1.body.len() ==> branches[i].spec_valid(rule_set) && rule1.body[i]
                        == branches[i].spec_head()
            },
        }
    }

    //reasons about the substition of the Prop element in Proof that is the Rule in Pstep and is itself in QQED
    pub open spec fn spec_head(self) -> SpecProp
        recommends
            self matches SpecProof::Pstep(rule, s, branches) ==> rule.spec_complete_subst(s),
    {
        match self {
            SpecProof::Pstep(rule, s, branches) => rule.spec_subst(s).head,
            SpecProof::QED(p) => p,
        }
    }
}

impl Proof {
    //performs a substition of the Prop element in Proof that is the Rule in Pstep and is itself in QED (just clones itself in QED)
    pub fn head(&self) -> (res: Prop)
        requires
            self matches Proof::Pstep(rule, s, branches) ==> rule.deep_view().spec_complete_subst(
                s.deep_view(),
            ),
        ensures
            res.deep_view() <==> self.deep_view().spec_head(),
    {
        //lemma shows that exec and spec variants are equal
        proof { axiom_proof_deep_view(self) }
        ;
        match self {
            Proof::Pstep(rule, s, branches) => rule.subst(s).head,
            Proof::QED(p) => p.clone(),
        }
    }
}

pub struct Thm {
    pub val: Prop,
    pub p: Proof,
}

pub struct SpecThm {
    pub val: SpecProp,
    pub p: SpecProof,
}

impl DeepView for Thm {
    type V = SpecThm;

    open spec fn deep_view(&self) -> Self::V {
        SpecThm { val: self.val.deep_view(), p: self.p.deep_view() }
    }
}

impl SpecThm {
    //checks whether the SpecRuleSet is valid and if p substituted to head is equal to the val argument of the SpecThm
    pub open spec fn spec_wf(self, rule_set: SpecRuleSet) -> bool {
        self.p.spec_valid(rule_set) && self.p.spec_head() == self.val
    }
}

//used in the thm derivation process to create terminal points on branches of proof trees
pub fn mk_leaf(p: &Prop) -> (res: Result<Thm, ()>)
    ensures
        p.deep_view().spec_concrete() && !p.deep_view().spec_symbolic()
            && p.deep_view().spec_valid() ==> res.is_Ok(),
        res matches Ok(v) ==> v.val == p,
{
    if p.clone().concrete() && !p.clone().symbolic() && p.clone().valid() {
        Ok(Thm { val: p.clone(), p: Proof::QED(p.clone()) })
    } else {
        Err(())
    }
}

//#[verifier::loop_isolation(false)] in order to satisfy invariants and meet recommendations
#[verifier::loop_isolation(false)]
//produces a thm after being passed the Ruleset and Vec<Thm> to be used to validate predicates based on rule and fact encodings
pub fn mk_thm(rs: &RuleSet, k: usize, s: &Subst, args: &Vec<Thm>) -> (res: Result<Thm, ()>)
    requires
        k < rs.rs.len(),
        //forall statement makes sure that all theorems are well formed
        forall|j: int| #![auto] 0 <= j < args.len() ==> args[j].deep_view().spec_wf(rs.deep_view()),
    ensures
//ensures block specifies conditions that must be met in order for the thm to be valid at termination

        ((rs.rs[k as int].deep_view().spec_complete_subst(s.deep_view()) && args.len()
            == rs.rs[k as int].body.len() && (forall|j: int|
            #![auto]
            0 <= j < args.len() ==> args[j].deep_view().val
                == rs.rs[k as int].deep_view().spec_subst(s.deep_view()).body[j])) ==> res.is_Ok()),
        res matches Ok(thm) ==> rs.rs[k as int].deep_view().spec_complete_subst(s.deep_view())
            && thm.deep_view().spec_wf(rs.deep_view()) && thm.deep_view().val
            == rs.rs[k as int].deep_view().spec_subst(s.deep_view()).head,
{
    let r = rs.rs[k].clone();
    //assertion states that using deep_view of the original ruleset and accesing elements results in the same as line 900
    assert(rs.deep_view().rs[k as int] == r.deep_view());

    if args.len() != r.body.len() || !r.complete_subst(&s) {
        return Err(());
    }
    //flag is used to check conditions for successful thm production

    let mut flag = true;
    let r_subst = r.subst(&s);
    for i in 0..args.len()
        invariant
            0 <= i <= args.len(),
            r_subst.body.view().len() == r.body.view().len(),
            r_subst.deep_view() == r.deep_view().spec_subst(s.deep_view()),
            flag <==> forall|j: int|
                #![auto]
            //invariant forall shows that different placements od deep_view have same result

                0 <= j < i ==> args[j as int].deep_view().val == r_subst.deep_view().body[j as int],
    {
        flag = (Prop::prop_eq(&r_subst.body[i], &args[i].val) && flag);
        assert(flag ==> args[i as int].deep_view().val == r_subst.deep_view().body[i as int]);
    }
    //if all properties were satisfied

    if !flag {
        return Err(());
    }
    let mut pfs: Vec<Proof> = Vec::new();
    for i in 0..args.len()
        invariant
            pfs.len() == i,
            0 <= i <= args.len(),
            forall|j: int|
                #![auto]
            //invariant forall checks if all indices of pfs are valid

                0 <= j < i ==> pfs[j].deep_view().spec_valid(rs.deep_view()),
            forall|j: int|
                #![auto]
            //invariant forall checks if all indices of pfs.head() == r_subst.body[j]

                0 <= j < i ==> r_subst.deep_view().body[j] == pfs[j].deep_view().spec_head(),
    {
        pfs.push(args[i].p.clone());
        proof { axiom_proof_deep_view(&args[i as int].p) }
        ;
    }
    let p = Proof::Pstep(r.clone(), s.clone(), pfs);
    let thm = Thm { val: r_subst.head, p: p };
    proof { axiom_proof_deep_view(&p) }
    ;
    Ok(thm)
}

//Edge-connectivity example using the following Datalog program:
/*
connected(a, b) :- edge(a, b).
connected(a, c) :- connected(a, b), edge(b, c).
edge("x", "y").
edge("x", "f").
edge("y", "z").
edge("z", "w").

The query is ?- connected("x","w").
*/

//constructs a RuleSet from user-defined rules and facts (rules without bodies)
pub fn tst_connected() -> (res: RuleSet)
    ensures
        res.rs.len() == 6,
{
    RuleSet {
        rs:
            vec![
            Rule {
                head: Prop::App(
                    "connected".to_string(),
                    vec![Term::Var("a".to_string()), Term::Var("b".to_string())],
                ),
                body: vec![
                    Prop::App(
                        "edge".to_string(),
                        vec![Term::Var("a".to_string()), Term::Var("b".to_string())],
                    ),
                ],
                id: 0,
            },
            Rule {
                head: Prop::App(
                    "connected".to_string(),
                    vec![Term::Var("a".to_string()), Term::Var("c".to_string())],
                ),
                body: vec![
                    Prop::App(
                        "connected".to_string(),
                        vec![Term::Var("a".to_string()), Term::Var("b".to_string())],
                    ),
                    Prop::App(
                        "edge".to_string(),
                        vec![Term::Var("b".to_string()), Term::Var("c".to_string())],
                    ),
                ],
                id: 1,
            },
            Rule {
                head: Prop::App(
                    "edge".to_string(),
                    vec![
                        Term::Const(Const::Atom("x".to_string())),
                        Term::Const(Const::Atom("y".to_string())),
                    ],
                ),
                body: vec![],
                id: 2,
            },
            Rule {
                head: Prop::App(
                    "edge".to_string(),
                    vec![
                        Term::Const(Const::Atom("x".to_string())),
                        Term::Const(Const::Atom("f".to_string())),
                    ],
                ),
                body: vec![],
                id: 3,
            },
            Rule {
                head: Prop::App(
                    "edge".to_string(),
                    vec![
                        Term::Const(Const::Atom("y".to_string())),
                        Term::Const(Const::Atom("z".to_string())),
                    ],
                ),
                body: vec![],
                id: 4,
            },
            Rule {
                head: Prop::App(
                    "edge".to_string(),
                    vec![
                        Term::Const(Const::Atom("z".to_string())),
                        Term::Const(Const::Atom("w".to_string())),
                    ],
                ),
                body: vec![],
                id: 5,
            },
        ],
    }
}

//makes thms for steps in proof tree and checks the final one
pub fn tst_connected_thm() -> (res: Result<Thm, ()>) {
    let rs = tst_connected();

    //Dafny example
    /* var s1 : Subst := map["a" := Atom("x"), "b" := Atom("y")];
       var thm1 := mk_thm(rs, 0, s1, []); */

    let mut s1 = TmpStringHashMap::<Const>::new();
    s1.insert("a".to_string(), Const::Atom("x".to_string()));
    s1.insert("b".to_string(), Const::Atom("y".to_string()));
    let thm1 = mk_thm(&rs, 0, &s1, &vec![]);

    let mut s2 = TmpStringHashMap::<Const>::new();
    s2.insert("a".to_string(), Const::Atom("x".to_string()));
    s2.insert("c".to_string(), Const::Atom("y".to_string()));
    let thm2 = mk_thm(&rs, 1, &s2, &vec![]);

    let mut s3 = TmpStringHashMap::<Const>::new();
    s3.insert("a".to_string(), Const::Atom("y".to_string()));
    s3.insert("b".to_string(), Const::Atom("z".to_string()));
    let thm3 = mk_thm(&rs, 0, &s3, &vec![]);

    let mut s4 = TmpStringHashMap::<Const>::new();
    s4.insert("a".to_string(), Const::Atom("x".to_string()));
    s4.insert("c".to_string(), Const::Atom("z".to_string()));
    let thm4 = mk_thm(&rs, 1, &s4, &vec![]);

    let mut s5 = TmpStringHashMap::<Const>::new();
    s5.insert("a".to_string(), Const::Atom("z".to_string()));
    s5.insert("b".to_string(), Const::Atom("w".to_string()));
    let thm5 = mk_thm(&rs, 0, &s5, &vec![]);

    let mut s6 = TmpStringHashMap::<Const>::new();
    s6.insert("a".to_string(), Const::Atom("x".to_string()));
    s6.insert("c".to_string(), Const::Atom("w".to_string()));
    let thm6 = mk_thm(&rs, 1, &s6, &vec![]);

    match thm6 {
        Ok(val) => Ok(val),
        Err(_) => Err(()),
    }
}

} // verus!
