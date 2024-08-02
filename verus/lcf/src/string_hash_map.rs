use vstd::prelude::*;
use std::collections::HashMap;


verus!{


#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
pub struct TmpStringHashMap<Value> {
    m: HashMap<String, Value>,
}

impl<Value> View for TmpStringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    closed spec fn view(&self) -> Self::V;
}

impl<Value> DeepView for TmpStringHashMap<Value> 
    where Value: DeepView
{
    type V = Map<Seq<char>, <Value as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        self
            .view()
            .map_values(|v: Value| v.deep_view())
    }
}


impl<Value:PartialEq> PartialEq for TmpStringHashMap<Value> {
    fn eq(&self, other :&Self) -> bool{
        self.m == other.m
    } 
}

impl<Value: Clone + DeepView> Clone for TmpStringHashMap<Value> {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self) 
        ensures self.deep_view() == res.deep_view()
    {
        Self { m: self.m.clone() }
    }
}

impl<Value> TmpStringHashMap<Value> {
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    pub open spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: String, v: Value)
        ensures
            self@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    #[verifier::external_body]
    pub fn contains_key(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<Seq<char>, Value>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast proof fn axiom_string_hash_map_spec_len<Value>(m: &TmpStringHashMap<Value>)
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_hash_map_axioms {
    axiom_string_hash_map_spec_len,
}

}

// Test
verus!{

fn test()
{
    let mut m = TmpStringHashMap::<i8>::new();
    let mut n = TmpStringHashMap::<i8>::new();
    assert(m@ == Map::<Seq<char>, i8>::empty());
    assert(n@ == Map::<Seq<char>, i8>::empty());

    let three: String = "three".to_string();
    let six: String = "six".to_string();
    m.insert(three.clone(), 4);
    m.insert(six.clone(), -8);
    assert(!(three@ =~= six@)) by {
        reveal_strlit("three");
        reveal_strlit("six");
    }
    assert(m@[three@] == 4);

    let b = m.contains_key(three.as_str());
    assert(b);

    assert(m.len() == 2) by {
        axiom_string_hash_map_spec_len(&m);
    }
    let n = m.len();
    assert(n == 2);

    let v = m.get(six.as_str());
    match v {
        Some(v) => assert(*v == -8),
        None => assert(false),
    };

    m.clear();
    assert(!m@.contains_key(three@));
    let b = m.contains_key(three.as_str());
    assert(!b);
}

}

