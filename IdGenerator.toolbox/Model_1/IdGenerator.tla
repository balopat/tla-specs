---------------------------- MODULE IdGenerator ----------------------------

EXTENDS Integers, TLC

CONSTANT  NumberOfProcesses

(*

--fair algorithm IdGenerator {

  variable lastIdUsed = 42, processIds = [ i \in 1.. NumberOfProcesses |-> 0];
  
  define {
    AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
    IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => processIds[i] # processIds[j])
    Invariant == AllIsDone => IdsAreAllDifferent
  }

  process(id \in 1 .. NumberOfProcesses) {
    update: lastIdUsed := lastIdUsed + 1;
    sepRead: processIds[self] := lastIdUsed
    
  }

}

*)

\* BEGIN TRANSLATION
VARIABLES lastIdUsed, processIds, pc

(* define statement *)
AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => processIds[i] # processIds[j])
Invariant == AllIsDone => IdsAreAllDifferent


vars == << lastIdUsed, processIds, pc >>

ProcSet == (1 .. NumberOfProcesses)

Init == (* Global variables *)
        /\ lastIdUsed = 42
        /\ processIds = [ i \in 1.. NumberOfProcesses |-> 0]
        /\ pc = [self \in ProcSet |-> "update"]

update(self) == /\ pc[self] = "update"
                /\ lastIdUsed' = lastIdUsed + 1
                /\ pc' = [pc EXCEPT ![self] = "sepRead"]
                /\ UNCHANGED processIds

sepRead(self) == /\ pc[self] = "sepRead"
                 /\ processIds' = [processIds EXCEPT ![self] = lastIdUsed]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED lastIdUsed

id(self) == update(self) \/ sepRead(self)

Next == (\E self \in 1 .. NumberOfProcesses: id(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Dec 04 17:50:50 EST 2015 by balopat
\* Created Fri Dec 04 17:18:27 EST 2015 by balopat
