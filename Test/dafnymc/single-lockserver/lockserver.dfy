// Chapter 3 Exercise 3 
/* Modified by tony to 
    1. remove members in datatype declarations.
    2. have cap on the number of steps to take in total
*/

//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

/*
Model a lock service that consists of a single server and an
arbitrary number of clients.
The state of the system includes the server's state (whether the server
knows that some client holds the lock, and if so which one)
and the clients' states (for each client, whether that client knows
it holds the lock).
The system should begin with the server holding the lock.
An acquire step atomically transfers the lock from the server to some client.
(Note that we're not modeling the network yet -- the lock disappears from
the server and appears at a client in a single atomic transition.)
A release step atomically transfers the lock from the client back to the server.
The safety property is that no two clients ever hold the lock
simultaneously.
*/

datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired
datatype Constants = Constants(clientCount: nat) 

predicate ValidIdx(c:Constants, idx: int) {
    0 <= idx < c.clientCount
}

datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>)

predicate WF(c: Constants, v: Variables) {
    |v.clients| == c.clientCount
}

predicate Init(c:Constants, v:Variables) {
  && WF(c, v)
  && v.server.Unlocked?
  && |v.clients| == c.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

predicate Acquire(c:Constants, v:Variables, v':Variables, id:int) {
  && WF(c, v)
  && WF(c, v')
  && ValidIdx(c, id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
}

predicate Release(c:Constants, v:Variables, v':Variables, id:int) {
  && WF(c, v)
  && WF(c, v')
  && ValidIdx(c, id)

  && v.clients[id].Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
}

datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
    case AcquireStep(id) => Acquire(c, v, v', id)
    case ReleaseStep(id) => Release(c, v, v', id)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  forall i,j ::
    (&& 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?) ==> i == j
}

/*
CONSTANT
\* @type: [tag : Str, clientCount : Int];
    tla_c
VARIABLE
\* @type: [tag : Str, server : {tag : Str} | {tag : Str, id : Int}, clients : Seq({tag : Str} | {tag : Str})];
    tla_s


tla_Init == /\ tla_c \in Constants 
            /\ tla_s \in Variables 
            /\ Init(tla_c, tla_s)
tla_Next == /\ tla_s' \in Variables 
            /\ Next(tla_c, tla_s, tla_s')
tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)
tla_Safety == Safety(tla_c, tla_s) 
*/