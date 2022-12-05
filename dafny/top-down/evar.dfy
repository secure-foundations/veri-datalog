include "std-lib/src/Wrappers.dfy"
include "definitions.dfy"

import opened Wrappers

// datatype Evar = Evar(e:int)
type Evar = int

class EvarMap {
    var evar_map: map<Evar, Option<string>>; // this string should be changed to whatever the const type is
    var next_evar: Evar;

    constructor()
        ensures this.evar_map == map[]
        ensures this.next_evar == 0
        ensures fresh(this)
    {
        // TODO: If the below lines are not written, then will they take default values?
        evar_map := map[];
        next_evar := 0;
        new;
    }

    // TODO: Check if this implements a copy constructor
    constructor Init(emap:EvarMap)
        ensures this.evar_map == emap.evar_map
        ensures this.next_evar == emap.next_evar
        ensures fresh(this)
    {
        this.evar_map := emap.evar_map;
        this.next_evar := emap.next_evar;
        new;
    }

    predicate inv 
        reads this
    {
        (next_evar !in  evar_map)
        && (forall i :: i < next_evar <==> i in evar_map)
    }

    method get_new_evar() returns (e:Evar) 
        modifies this
        requires inv()
        ensures e == old(next_evar)
        ensures next_evar == old(next_evar) + 1
        ensures evar_map == old(evar_map)[e := None]
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
        ensures inv()
        ensures evar_map == old(evar_map)[e := Some(v)]
    {
        print "\t\tresolving ", e, " to ", v, " in ", this.evar_map, "\n";
        evar_map := evar_map[e := Some(v)];
    }

    method lookup(e:Evar) returns (o:Option<string>)
    {
        if e in evar_map {
            return evar_map[e];
        } else {
            return None;
        }
    }
}

type EvarSubstitution = map<VarTerm, Evar>