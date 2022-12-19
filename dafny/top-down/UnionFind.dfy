datatype Option<A> = | Some(v : A) | None
    
class UFMap { 
    var ctr : nat
    var ids : map<nat, nat>
    var vals : map<nat, nat>

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
    { 
        ctr := 0;
        ids := map[];
    }

    method Insert(i : nat, v : nat)
    modifies this
    requires Valid()
    ensures Valid()
    {
        ids := ids[i := this.ctr];
        vals := vals[this.ctr := v];
        ctr := ctr + 1;
    }

    function method Get(i : nat) : (res : Option<nat>)
    reads this
    requires Valid()
    ensures res.Some? ==> i in ids && res == Some(vals[ids[i]])
    ensures res.None? ==> i !in ids
     { 
        if i in ids then Some(vals[ids[i]]) else None
    }

    method Union(i : nat, j : nat)
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

    function method EqualKey(i : nat, j : nat) : (res : bool)
        reads this
        requires i in ids && j in ids 
        requires Valid()
        ensures res ==> Get(i) == Get(j)
    {
        ids[i] == ids[j]
    }

}
