include "std-lib/src/Wrappers.dfy"
include "def.dfy"

import opened Wrappers

datatype Evar = Evar(e:int)

// datatype Option<t> = Some (val:t) | None

class Evar2 {
    var evar_map: map<int, Option<int>>;
    var next_evar: int;

    predicate inv 
        reads this
    {
        (next_evar !in  evar_map)
        && (forall i :: i < next_evar <==> i in evar_map)
    }

    method get_new_evar() returns (e:int) 
        modifies this
        requires inv()
        ensures e == old(next_evar)
        ensures next_evar == old(next_evar) + 1
        ensures inv()
    {
        evar_map := evar_map[next_evar := None];
        next_evar := next_evar + 1;
        return next_evar - 1;
    }

    method resolve(e:int, v:int) returns ()
        modifies this
        requires inv()
        requires e in evar_map
        ensures inv()
        ensures evar_map == old(evar_map)[e := Some(v)]
    {
        evar_map := evar_map[e := Some(v)];
    }    
}

type EvarSubstitution = map<Term, Evar2>