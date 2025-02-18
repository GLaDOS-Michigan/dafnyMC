module Manhole {

datatype Walker = W(x:int, y:int)
datatype State = S(w:Walker, radius:int)

predicate Init(s:State) {
    && s.w.x == 0
    && s.w.y == 5
    && s.radius == 3
}

predicate MoveNorth(s:State, s':State) {
    && s'.w.x == s.w.x
    && s'.w.y == s.w.y + 1
    && s'.radius == s.radius
}

predicate MoveSouthEast(s:State, s':State) {
    && s'.w.x == s.w.x + 1
    && s'.w.y == s.w.y - 1
    && s'.radius == s.radius
}

predicate Next(s:State, s':State) {
    || MoveNorth(s, s')
    || MoveSouthEast(s, s')
}

predicate InManhole(s:State) {
    s.w.x * s.w.x + s.w.y*s.w.y <= s.radius * s.radius
}

predicate Safety(s:State) {
    !InManhole(s)
}

}

/**
tla_Init == tla_s \in Manhole_State /\ Manhole_Init(tla_s)
tla_Next == tla_s' \in Manhole_State /\ Manhole_Next(tla_s, tla_s')
tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)

tla_Safety == Manhole_Safety(tla_s) 
**/