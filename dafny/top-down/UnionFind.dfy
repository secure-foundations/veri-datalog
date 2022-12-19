datatype Option<A> = | Some(v : A) | None
    
class UFMap<K(==), V(==)> { 
    var ctr : nat
    var ids : map<K, nat>
    var vals : map<nat, V>

    predicate Valid()
    reads this
    {
        (forall j | j in ids :: ids[j] < ctr)
        &&
        (forall j | j in ids :: ids[j] in vals)
    }

    method Init() 
    modifies this
    ensures Valid()
    ensures ids == map[]
    ensures vals == map[]
    { 
        ctr := 0;
        ids := map[];
        vals := map[];
    }

    method Insert(i : K, v : V)
    modifies this
    requires Valid()
    ensures Valid()
    ensures i in ids
    ensures vals[ids[i]] == v
    {
        if i !in ids {
            ids := ids[i := this.ctr];
            vals := vals[this.ctr := v];
            ctr := ctr + 1;
        }
        else {
            vals := vals[ids[i] := v];
        }
    }

    function method Get(i : K) : (res : Option<V>)
    reads this
    requires Valid()
    ensures res.Some? ==> i in ids && res == Some(vals[ids[i]])
    ensures res.None? ==> i !in ids
     { 
        if i in ids then Some(vals[ids[i]]) else None
    }

    method Union(i : K, j : K)
    modifies this
    modifies this
    requires Valid()
    requires i in ids && j in ids
    ensures Valid()
    ensures ids.Keys == old(ids.Keys)
    ensures forall k | k in ids && ids[k] != ids[j] :: ids[k] == old(ids[k]);
    ensures forall k | k in ids && ids[k] == ids[j] :: ids[k] == old(ids[i]);
     {
        var toUpdate := map k | k in ids && ids[k] == ids[j] :: ids[i];
        ids := ids + toUpdate;
    }

    function method EqualKey(i : K, j : K) : (res : bool)
        reads this
        requires i in ids && j in ids 
        requires Valid()
        ensures res ==> Get(i) == Get(j)
    {
        ids[i] == ids[j]
    }

}
