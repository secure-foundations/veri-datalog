include "std-lib/src/Wrappers.dfy"

import opened Wrappers

datatype bijective_map<T1, T2> = bijective_map(l_to_r : map<T1, T2>, r_to_l : map<T2, T1>)
{

    lemma bijection() 
        ensures forall e1:T1, e2:T2 :: e1 in l_to_r && e2 in r_to_l ==> ((l_to_r[e1] == e2) <==> (r_to_l[e2] == e1))
    {}

    function sel(t1:T1) : Option<T2>
    {
        if t1 in l_to_r.Keys then Some(l_to_r[t1]) else None
    }

    function sel2(t2:T2) : Option<T1>
    {
        if t2 in r_to_l then Some(r_to_l[t2]) else None
    }

    function update(t1:T1, t2:T2) : bijective_map<T1, T2>
    {
        bijective_map(l_to_r[t1 := t2], r_to_l[t2 := t1])
    }
}

// newtype k = x:bijective_map | true