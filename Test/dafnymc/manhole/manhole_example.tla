--------------------------------- MODULE manhole_example ---------------------------------

EXTENDS Integers

int == Int

VARIABLE s  \* Use a single variable to capture entire system state

Walker == [ x : int, y : int ]
State == [ w : Walker, radius : int ]

Init ==  /\ s \in State  \* Declare type of s
         /\ s.w.x = 0
         /\ s.w.y = 5
         /\ s.radius = 3

MoveNorth == /\ s'.w.x = s.w.x
             /\ s'.w.y = s.w.y + 1
             /\ s'.radius = s.radius

MoveSouthEast == /\ s'.w.x = s.w.x + 1
                 /\ s'.w.y = s.w.y - 1
                 /\ s'.radius = s.radius

Next == \/ MoveNorth
        \/ MoveSouthEast

Spec == Init /\ [][Next]_<<s>>

InManhole == s.w.x * s.w.x + s.w.y*s.w.y <= s.radius * s.radius

Safety == ~InManhole

==========================================================================================
