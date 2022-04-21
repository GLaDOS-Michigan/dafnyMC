module Datatype {

datatype Number = Num(n:int) {
    predicate GoodSize() {
        n < 0 < 10
    }

    function Add(i:int) : int {
        n + i
    }
}
}