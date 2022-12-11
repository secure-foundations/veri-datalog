include "std-lib/src/Wrappers.dfy"
include "std-lib/src/Collections/Maps/Maps.dfy"

module BijectiveMap {
    import opened Wrappers
    import opened Maps

    datatype BijectiveMap<T1, T2> = BijectiveMap(l_to_r:map<T1, T2>, r_to_l:map<T2, T1>) {
        predicate valid() {
            (forall k:T1 :: k in l_to_r ==>
                l_to_r[k] in r_to_l && r_to_l[l_to_r[k]] == k)
            && (forall k:T2 :: k in r_to_l ==> 
                r_to_l[k] in l_to_r && l_to_r[r_to_l[k]] == k)
            // && |l_to_r.Values| == |r_to_l.Values|
            && |l_to_r| == |r_to_l| // Dafny should ideally figure this out by itself
            // && (forall t1:T1, t2:T2 :: (t1, t2) in l_to_r.Items ==> (t2, t1) in r_to_l.Items)
            // && (forall t1:T1, t2:T2 :: (t2, t1) in r_to_l.Items ==> (t1, t2) in l_to_r.Items)
        }

        // function method {:opaque} in1(e:T1) : bool
        //     requires valid()
        //     ensures in1(e) == (e in l_to_r)
        // {
        //     e in l_to_r
        // }

        function method in1(e:T1) : bool
            requires valid()
            ensures in1(e) == (e in l_to_r)
        {
            e in l_to_r
        }

        function method in2(e:T2) : bool
            requires valid()
            ensures in2(e) == (e in r_to_l)
        {
            e in r_to_l
        }

        function method get1(e:T1) : T2
            requires valid()
            requires in1(e)
            requires e in l_to_r
            ensures get1(e) == l_to_r[e]
        {
            l_to_r[e]
        }

        function method insert(e1:T1, e2:T2) : BijectiveMap<T1, T2>
            requires valid()
            // requires !in1(e1) && !in2(e2)
            requires (e1 !in l_to_r && e2 !in r_to_l)
                     || (e1 in l_to_r && e2 == l_to_r[e1] && e2 in r_to_l && e1 == r_to_l[e2])
            ensures insert(e1, e2).valid()
            ensures insert(e1, e2) == BijectiveMap(l_to_r[e1 := e2], r_to_l[e2 := e1])
            ensures insert(e1, e2).in1(e1)
            ensures insert(e1, e2).in2(e2)
        {
            BijectiveMap(l_to_r[e1 := e2], r_to_l[e2 := e1])
        }

        function method equal(b:BijectiveMap<T1, T2>) : bool
            requires valid()
        {
            forall e1:T1 :: e1 in l_to_r ==> e1 in b.l_to_r
            && forall e2:T2 :: e2 in r_to_l ==> e2 in b.r_to_l
        }


        function Values() : set<T2>
            requires valid() // Needed?
        {
            r_to_l.Keys
        }

        function Keys() : set<T1>
            requires valid() // Needed?
        {
            l_to_r.Keys
        }

        function Items() : set<(T1, T2)>
            requires valid() // Needed?
        {
            l_to_r.Items
        }

        predicate {:opaque} IsSubsetOf(b:BijectiveMap<T1,T2>)
            requires valid()
            requires b.valid()
        {
            // Items() <= b.Items()
            IsSubset(l_to_r, b.l_to_r) && IsSubset(r_to_l, b.r_to_l)
        }

        // lemma lemma_domain_sizes(b:BijectiveMap<T1, T2>)
        //     requires b.valid()
        //     ensures b.valid()
        //     ensures |b.l_to_r| == |b.r_to_l|
        // {
        //     // assert(forall k :: k in l_to_r ==> l_to_r[k] in r_to_l);
        //     // assert (|l_to_r.Values| == |r_to_l.Keys|);
        //     // assert (|l_to_r| == |l_to_r.Values|);
        //     if |b.l_to_r| == 0 {
        //         assert(|b.l_to_r| == |b.r_to_l|);
        //     } else {
        //         var K:T1;
        //         assume (K in b.l_to_r);
        //     }
        // }

        // lemma lemma_domain_range_sizes()
        //     requires valid()
        //     ensures valid()
        //     ensures l_to_r.Values == r_to_l.Keys
        //     ensures |l_to_r.Values| == |r_to_l.Keys|

        //     ensures r_to_l.Values == l_to_r.Keys
        //     ensures |r_to_l.Values| == |l_to_r.Keys|
        // {
        //     lemma_domain_sizes();
        //     // assume(|l_to_r| == |r_to_l|);
        // }

        // lemma same_size()
        //     requires valid()
        //     ensures |l_to_r| == |r_to_l|
        // {
        //     assert(|l_to_r.Items| == |r_to_l.Items|);
        // }

        // method foo() 
        //     requires valid()
        //     ensures valid()
        // {
        //     assert(|l_to_r| == |r_to_l|);
        //     // assert(valid());
        // }
    }

    method new_bijective_map<T1, T2> () returns (b:BijectiveMap<T1, T2>)
        ensures b.valid()
        ensures forall e1:T1 :: b.in1(e1) == false
        ensures forall e2:T2 :: b.in2(e2) == false
        ensures b.Keys() == {}
        ensures b.Values() == {}
        ensures b.Items() == {}
    {
        return BijectiveMap(map[], map[]);
    }

    // lemma InsertItems<T1,T2>(b:BijectiveMap<T1,T2>, e1:T1, e2:T2)
    //     requires b.valid()
    //     requires !b.in1(e1) && !b.in2(e2) 
    //     ensures  (b.insert(e1, e2).Items() == b.Items() + {(e1, e2)});
    // {
    //     assert(b.Values() == b.l_to_r.Values);
    //     assert(b.insert(e1, e2).Keys() == b.Keys() + {e1});
    //     assert(b.insert(e1, e2).Values() == b.Values() + {e2});
    //     // assert(b.insert(e1, e2).Items() == b.Items() + {(e1, e2)});
        
    // }

    lemma InsertPreservesSubset<T1, T2>(b1:BijectiveMap<T1,T2>, b2:BijectiveMap<T1,T2>, e1:T1, e2:T2)
        requires b1.valid()
        requires b2.valid()
        requires reveal b1.IsSubsetOf(); b1.IsSubsetOf(b2)
        requires !b1.in1(e1) && !b1.in2(e2) && !b2.in1(e1) && !b2.in2(e2)
        ensures (b1.insert(e1,e2)).IsSubsetOf(b2.insert(e1,e2))
    {
        reveal b1.IsSubsetOf();
    }

}


