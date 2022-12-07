module BijectiveMap {
    datatype BijectiveMap<T1(!new), T2(!new)> = BijectiveMap(l_to_r:map<T1, T2>, r_to_l:map<T2, T1>) {
        predicate valid() {
            (forall k:T1 :: k in l_to_r ==>
                l_to_r[k] in r_to_l && r_to_l[l_to_r[k]] == k)
            && (forall k:T2 :: k in r_to_l ==> 
                r_to_l[k] in l_to_r && l_to_r[r_to_l[k]] == k)
            // && (forall t1:T1, t2:T2 :: (t1, t2) in l_to_r.Items ==> (t2, t1) in r_to_l.Items)
            // && (forall t1:T1, t2:T2 :: (t2, t1) in r_to_l.Items ==> (t1, t2) in l_to_r.Items)
        }

        lemma same_size()
            requires valid()
            ensures |l_to_r| == |r_to_l|
        {
            assert(|l_to_r.Items| == |r_to_l.Items|);
        }

        // method foo() 
        //     requires valid()
        //     ensures valid()
        // {
        //     assert(|l_to_r| == |r_to_l|);
        //     // assert(valid());
        // }
    }
}