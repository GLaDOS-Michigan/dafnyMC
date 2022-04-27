
(******     Runtime Definitions     *****)
int == Int
nat == Nat
bool == BOOLEAN

\* TRUE iff the element e \in sequence s
tla_Contains(s, e) == \E i \in 1..Len(s) : s[i] = e

(******   End Runtime Definitions   *****)


