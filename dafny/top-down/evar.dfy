include "std-lib/src/Wrappers.dfy"
include "definitions.dfy"
include "bijective_map.dfy"

import opened Wrappers
import opened BijectiveMap

// datatype Evar = Evar(e:int)
type Evar = nat

// type EvarSubstitution = map<Term, Evar>
type EvarSubstitution = BijectiveMap<Term, Evar>
class EvarMap {
    var evar_map: map<Evar, Option<string>>; // this string should be changed to whatever the const type is
    var next_evar: Evar;

    constructor()
        ensures this.evar_map == map[]
        ensures this.next_evar == 0
        ensures fresh(this)
        ensures inv()
    {
        // TODO: If the below lines are not written, then will they take default values?
        evar_map := map[];
        next_evar := 0;
        new;
    }

    // TODO: Check if this implements a copy constructor
    constructor Init(emap:EvarMap)
        requires emap.inv()
        ensures this.evar_map == emap.evar_map
        ensures this.next_evar == emap.next_evar
        ensures fresh(this)
        ensures this != emap
        ensures this.inv()
    {
        this.evar_map := map e : Evar | e in emap.evar_map :: emap.evar_map[e];
        this.next_evar := emap.next_evar;
        new;
    }

    predicate inv 
        reads this
    {
        && (next_evar >= 0)
        && (next_evar !in  evar_map)
        && (forall i:nat :: i < next_evar <==> i in evar_map)
    }

    method get_new_evar() returns (e:Evar) 
        modifies this
        requires inv()
        ensures e == old(next_evar)
        ensures next_evar == old(next_evar) + 1
        ensures evar_map == old(evar_map)[e := None]
        ensures |evar_map| == |old(evar_map)| + 1 // TODO: Can probably remove this
        ensures evar_map.Keys == old(evar_map).Keys + {e}
        ensures inv()
    {
        evar_map := evar_map[next_evar := None];
        next_evar := next_evar + 1;
        return next_evar - 1;
    }

    method resolve(e:Evar, v:string) returns ()
        modifies this
        requires inv()
        requires e in evar_map
        requires evar_map[e] == None
        ensures inv()
        ensures evar_map == old(evar_map)[e := Some(v)]
        ensures |evar_map| == |old(evar_map)| // TODO: Can remove this
        ensures evar_map.Keys == old(evar_map).Keys
        ensures this.is_more_resolved()
    {
        //print "\t\tresolving ", e, " to ", v, " in ", this.evar_map, "\n";
        evar_map := evar_map[e := Some(v)];
    }

    function method lookup(e:Evar) : Option<string>
        reads this
        requires inv()
        requires e in evar_map
        ensures inv()
        ensures lookup(e) == evar_map[e]
    {
        evar_map[e]
    }

    method copy(emap:EvarMap) returns ()
        requires emap.inv()
        requires this.inv()
        requires this != emap
        modifies this
        ensures this.evar_map == emap.evar_map
        ensures this.next_evar == emap.next_evar
        ensures this.inv()
        ensures unchanged(emap)
    {
        this.evar_map := emap.evar_map;
        this.next_evar := emap.next_evar;
    }

    twostate predicate is_more_resolved()
        reads this
    {
        // no new keys added
        old(this.evar_map).Keys == this.evar_map.Keys 

        // all values that are Some, remain Some with the same const
        && forall e:Evar | e in old(this.evar_map) :: (old(this.evar_map)[e].Some? ==> old(this.evar_map)[e] == this.evar_map[e])
    }

    twostate predicate monotonically_increasing()
        reads this
    {
        // no new keys added
        old(this.evar_map).Keys <= this.evar_map.Keys

        // all values that are Some, remain Some with the same const
        && forall e:Evar | e in old(this.evar_map) :: (old(this.evar_map)[e].Some? ==> old(this.evar_map)[e] == this.evar_map[e])
    }

    // twostate predicate monotonically_increasing()
    //     reads this
    // {
    //     forall e :: e in old(this.evar_map) ==> e in this.evar_map // TODO: Is a subset check better for the verifier?
    // }

    predicate fully_resolved() 
        reads this
    {
        forall e :: e in evar_map ==> evar_map[e].Some?
    }
}


function method make_subst(emap: EvarMap, esubst: EvarSubstitution) : Substitution
    reads emap
    requires emap.inv()
    requires esubst.valid()
    requires forall e:Evar :: esubst.in2(e) ==> e in emap.evar_map
    ensures  emap.fully_resolved() ==> forall t :: t in make_subst(emap, esubst).Values  ==> t.Const?
    ensures  forall v:Term :: esubst.in1(v) ==> v in make_subst(emap, esubst)
    // ensures forall v:VarTerm :: (esubst.in1(v) && esubst.get1(v) in emap.evar_map) 
    //                     ==> (make_subst(emap, esubst)[v].Const?)
    ensures  forall v:VarTerm :: v in esubst.l_to_r ==> (emap.evar_map[esubst.get1(v)].Some? ==> (make_subst(emap, esubst)[v] == Const(emap.evar_map[esubst.get1(v)].value)))
    // ensures  forall v:VarTerm :: esubst.in1(v) ==> (emap.evar_map[esubst.get1(v)].Some? ==> (make_subst(emap, esubst)[v] == Const(emap.evar_map[esubst.get1(v)].value)))
{
    // reveal esubst.in1();
    // map v:Term | esubst.in1(v) :: (
    map v:Term | v in esubst.l_to_r :: ( // TODO: use in1()
        match emap.evar_map[esubst.get1(v)]
            case Some(c) => Const(c)
            case None    => v
    )
}


// function method make_subst(emap: EvarMap, esubst: EvarSubstitution) : Substitution
//     reads emap
//     requires emap.inv()
//     requires forall e:Evar :: e in esubst.Values ==> e in emap.evar_map
//     ensures  emap.fully_resolved() ==> forall t :: t in make_subst(emap, esubst).Values  ==> t.Const?
//     ensures  forall v:VarTerm :: v in esubst ==> v in make_subst(emap, esubst)
// {
//     // reveal esubst.in1();
//     // map v:Term | esubst.in1(v) :: (
//     map v:Term | v in esubst :: ( // TODO: use in1()
//         match emap.evar_map[esubst[v]]
//             case Some(c) => Const(c)
//             case None    => v
//     )
// }
