datatype Option<A> = | Some(v : A) | None
    
class UFMap<K(!new, ==), V(==)> { 
    var ctr : nat
    var ids : map<K, nat>
    var vals : map<nat, V>

    ghost predicate Valid()
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
        ensures forall v :: Get(v) == None
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
        ensures forall j | j in ids && !EqualKey(j, i) :: Get(j) == old(Get(j))
        ensures forall j | j in ids && EqualKey(j, i) :: Get(j) == Some(v)
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

    function Get(i : K) : (res : Option<V>)
        reads this
        requires Valid()
    { 
        if i in ids then Some(vals[ids[i]]) else None
    }

    function Elem(i : K) : bool
        reads this
    { 
        i in ids
    } 

    function EqualKey(i : K, j : K) : (res : bool)
        reads this
        requires Valid()
    {
        (i !in ids && j !in ids) ||
        (i in ids && j in ids && 
        ids[i] == ids[j])
    }

    method Union(i : K, j : K)
        modifies this
        modifies this
        requires Valid()
        requires Elem(i) && Elem(j)
        ensures Valid()
        ensures forall k :: Elem(k) == old(Elem(k)) 
        ensures forall k | Elem(k) && !(EqualKey(k, j)) :: Get(k) == old(Get(k))
        ensures forall k | Elem(k) && (EqualKey(k, j)) :: Get(k) == Get(i)
        ensures EqualKey(i, j)
    {
        var toUpdate := map k | k in ids && ids[k] == ids[j] :: ids[i];
        ids := ids + toUpdate;
    }


}
