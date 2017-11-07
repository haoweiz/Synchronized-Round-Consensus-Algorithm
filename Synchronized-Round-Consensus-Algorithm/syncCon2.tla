------------------------------ MODULE syncCon2 ------------------------------
EXTENDS Integers,Sequences,FiniteSets,TLC
CONSTANTS N,FAILNUM
ASSUME N <= 5 /\ 0 <= FAILNUM /\ FAILNUM <= 4
Nodes == 1..N
Process == 1..N
(*
--algorithm syncCon2
{variables FailNum = FAILNUM;
  up = [n \in Nodes |-> TRUE];
  pt = [n \in Nodes |-> 0];
  t = [n \in Nodes |-> FALSE];
  d = [n \in Nodes |-> -1];
  mb = [n \in Nodes |-> {}];

  define{
  SetMin(S) == CHOOSE i \in S : \A j \in S:i <= j
  }

  macro MaybeFail(){
    if(FailNum > 0 /\ up[self])
      {either
        {up[self] := FALSE;FailNum := FailNum - 1;}
         or skip;};
  }

  fair process(n \in Process)
  variable v = 0,Q = {};
  {
P:await(up[self] /\ \A s \in Nodes : mb[s] = {} /\ (\A i \in Nodes : pt[i] = pt[self]) /\ t[self] = FALSE);{
  if(pt[self] = 0) v := self; \*If in round 0, each node broadcast its own value
  else v := d[self];\*If in other round, each node broadcast the minimum value it received.
  Q := Nodes;\*Broadcast value to Nodes, if one node is crashed, we needn't broad value to it.
PS:while(up[self] /\ Q # {}){
     with(p \in Q){
       MaybeFail();\*In process n, each time we add v to mb[p], this process might be fail, and once the process
                   \*fail, we set up[self] fail and after that, all operations will be invalid.
       if(up[self]=TRUE)\*Test if operations have been failed before
         mb[p] := mb[p] \union {v}; \*In process n, add v to mb[1] to mb[N]
       Q := Q \ {p};\*For each element p in Q, we have to broadcast value v to mb[p], after adding v to mb[p],
                    \*remove p from Q in case of adding v to mb[p] again.
     };
   };
   if(up[self]) pt[self] := pt[self] + 1;
   if(up[self] = FALSE) Nodes := Nodes \ {self};\*If this process crashed, remove this node from nodes
PR:await(up[self] /\ (\A i \in Nodes : pt[i] = pt[self]));\*Wait until all process finished
   d[self]:=SetMin(mb[self]);
   mb[self] := {};\*The mailbox should be empty before every round begin.
   if(\A i \in Nodes : d[self] = d[i]) {
      t[self] := TRUE; \*If all d[i] in Nodes are the same, the result 
                       \*is consensus, then this process terminate normally.
   }                                                   
   else goto P;\*If some d[i] in Nodes is different, some nodes must be crashed, so go to the next round.
  };
 }
}
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S : \A j \in S:i <= j

VARIABLES v, Q

vars == << FailNum, up, pt, t, d, mb, pc, v, Q >>

ProcSet == (Process)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Process |-> 0]
        /\ Q = [self \in Process |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ (up[self] /\ \A s \in Nodes : mb[s] = {} /\ (\A i \in Nodes : pt[i] = pt[self]) /\ t[self] = FALSE)
           /\ IF pt[self] = 0
                 THEN /\ v' = [v EXCEPT ![self] = self]
                 ELSE /\ v' = [v EXCEPT ![self] = d[self]]
           /\ Q' = [Q EXCEPT ![self] = Nodes]
           /\ pc' = [pc EXCEPT ![self] = "PS"]
           /\ UNCHANGED << FailNum, up, pt, t, d, mb >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                            /\ IF up'[self]=TRUE
                                  THEN /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                                  ELSE /\ TRUE
                                       /\ mb' = mb
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ IF up[self] = FALSE
                             THEN /\ Nodes' = Nodes \ {self}
                             ELSE /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] /\ (\A i \in Nodes : pt[i] = pt[self]))
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ mb' = [mb EXCEPT ![self] = {}]
            /\ IF \A i \in Nodes : d'[self] = d'[i]
                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P"]
                       /\ t' = t
            /\ UNCHANGED << FailNum, up, pt, v, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Process: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Process : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

agreement == (\A i, j \in Nodes: t[i] /\ t[j] => d[i] = d[j])

=============================================================================
\* Modification History
\* Last modified Tue Oct 24 21:28:08 EDT 2017 by lenovo
\* Created Tue Oct 24 00:19:48 EDT 2017 by lenovo
