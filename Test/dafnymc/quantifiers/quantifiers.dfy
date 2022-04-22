module Datatype {

predicate existential(n:int, S:set<int>) {
    exists x :: x in S && x > n
}

predicate existential2(n:int, S:set<int>) {
    exists x,y :: x in S && y in S && x + y == n
}

/*
MCInt == 0..20
tla_Init == tla_s \in 0..10 /\ tla_s = 0
tla_Next == tla_s \in 0..10 /\ tla_s' = tla_s + 1
tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)

tla_Safety == existential(tla_s, {1,2,3,8}) \* User input
*/

}