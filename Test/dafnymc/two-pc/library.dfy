module Library {
    
function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
{
    theSeq[|theSeq|-1]
}
}