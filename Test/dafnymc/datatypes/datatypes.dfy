module Datatype {

datatype Number = Num(n:int) 

datatype Server = Unlocked | Client(id: nat)
datatype Client = Released | Acquired
datatype Bob = B

predicate ClientRelease(v:seq<Client>, v':seq<Client>, id:int) {
    && 0 <= id < |v|
    && v' == v[id := Released]
}

predicate ServerUnlock(v:seq<Server>, v':seq<Server>, id:int) {
    && 0 <= id < |v|
    && v' == v[id := Unlocked]
}

predicate ServerGrant(v:seq<Server>, v':seq<Server>, id:int) {
    && 0 <= id < |v|
    && v' == v[id := Client(20)]
}

}