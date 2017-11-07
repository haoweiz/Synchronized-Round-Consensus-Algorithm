------------------------------ MODULE syncCon1 ------------------------------



EXTENDS Integers,Sequences,FiniteSets,TLC
CONSTANTS N,FAILNUM
ASSUME N <= 5 /\ 0 <= FAILNUM /\ FAILNUM <= 4
Nodes == 1..N

(*
--algorithm syncCon1
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

  fair process(n \in Nodes)
  variable v = 0, Q = {};
  {
P:if(up[self]){
  v := self;
  Q := Nodes;
PS:while(up[self] /\ Q # {}){
     with(p \in Q){
       MaybeFail();\*In process n, each time we add v to mb[p], this process might be fail, and once the process
                   \*fail, we set up[self] fail and after that, all operations will be invalid.
       if(up[self]) mb[p] := mb[p] \union {v}; \*In process n, add v to mb[1] to mb[N]
       Q := Q \ {p};\*For each element p in Q, we have to broadcast value v to mb[p], after adding v to mb[p],
                      \*remove p from Q in case of adding v to mb[p] again.   
           
     };
   };
   if(up[self]) pt[self] := pt[self] + 1;
PR:await(up[self] /\ (\A i \in Nodes : pt[i] = pt[self]) /\ Q = {}); \*If no operations are failed and all process enter in round 1
   d[self]:=SetMin(mb[self]);\*Set the minimum of mb[p] to d[self], if success, all d[p] will be the same.
   print d[self];
   t[self]:=TRUE;\*The process is terminated
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

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self]
                 THEN /\ v' = [v EXCEPT ![self] = self]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
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
                            /\ IF up'[self]
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
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] /\ (\A i \in Nodes : pt[i] = pt[self]) /\ Q[self] = {})
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ PrintT(d'[self])
            /\ t' = [t EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

agreement == (\A i, j \in Nodes: t[i] /\ t[j] => d[i] = d[j])

=============================================================================
\*When no crash happened, the program will excute without any problems and all d[i] 
\*will be the same. However, if some nodes crash, some mailbox will lose some value,
\*these value might include the minumum value, so the result we get might not be the
\*minimum value. 



\* Modification History
\* Last modified Tue Oct 24 21:42:03 EDT 2017 by lenovo
\* Created Wed Oct 11 00:01:22 EDT 2017 by lenovo
