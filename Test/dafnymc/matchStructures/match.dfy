module MatchStructures {

datatype Breakfast = Pumpernickel | Bagel(toasted:bool) | Coffee(milk:bool, sugars:nat)

method WhatsForBreakfast_imp(b: Breakfast) returns (s:string) {
    match b {
        case Pumpernickel => 
            return "Pumpernickel";
        case Bagel(toast) => 
            return (if toast then "toasted bagel" else "chewy bagel");
        case Coffee(milk, sugars) => return 
            if milk then 
                if sugars>0 then "kopi" 
                else "kopi C kosong"
            else
                if sugars>0 then "kopi O" 
                else "kopi O kosong";
    }
}

function WhatsForBreakfast_func(b: Breakfast) : string { 
    match b {
        case Pumpernickel => "Pumpernickel"
        case Bagel(toast) => 
            if toast then "toasted bagel" else "chewy bagel"
        case Coffee(milk, sugars) => 
            if milk then 
                if sugars>0 then "kopi" 
                else "kopi C kosong"
            else
                if sugars>0 then "kopi O" 
                else "kopi O kosong"
    }
}

}