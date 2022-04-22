// Chapter 3 Exercise 1

//#title Coke Machine
//#desc The first state machine specification exercise: fill in actions.
//#elide
//#elide Its complexity is about the same as the library. We
//#elide provide the boilerplate for everything, but leave the state
//#elide transitions as an exercise.
//#elide It comes with a safety proof that we expect the students to use as an
//#elide oracle for whether they got the state transitions right.

// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity some cokes.
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add a number of cokes to the machine

module Machine {

datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate Init(c:Constants, v:CokeMachine) {
    && c.capacity >= 0
    && v.numCokes == 0
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes > 0
    && v'.numCokes == v.numCokes - 1
}

predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock >= 0
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
}

predicate Next(c:Constants, v:CokeMachine, v':CokeMachine) {
    || Purchase(c, v, v')
    || (exists num :: Restock(c, v, v', num))
}

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

predicate Inv(c:Constants, v:CokeMachine) {
    0 <= v.numCokes <= c.capacity
}

lemma SafetyProof()
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v')
        ensures Inv(c, v')
    {
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }
    }
}

lemma NonTrivialPurchase()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes
{
    var c := Constants(7);
    var v := CokeMachine(1);
    var v' := CokeMachine(0);
    assert Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes;
}

lemma NonTrivialRestock()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes
{
    var c := Constants(7);
    var v := CokeMachine(4);
    var v' := CokeMachine(7);
    assert Restock(c, v, v', 3);
    assert Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes;
}

/* 
tla_Init == tla_c \in Constants /\ tla_s \in CokeMachine /\ Init(tla_c, tla_s)
tla_Next == tla_s' \in CokeMachine /\ Next(tla_c, tla_s, tla_s')
tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)

tla_Safety == Inv(tla_c, tla_s)
*/
}