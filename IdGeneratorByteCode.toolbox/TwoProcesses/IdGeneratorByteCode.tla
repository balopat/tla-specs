------------------------ MODULE IdGeneratorByteCode ------------------------


EXTENDS Integers, Sequences,  TLC

CONSTANT  NumberOfProcesses, Locking

(*

--fair algorithm IdGenerator {

  variable  
  object = [lastId |-> 42, lock |-> 0],    
  stacks = [ i \in 1..NumberOfProcesses |-> <<>>],
  returnValue = [i\in 1..NumberOfProcesses |-> -1] 
  ;
  
  define {
    Last(S) == S[Len(S)]
    Pop(S) == SubSeq(S, 1, Len(S)-1)
    AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
    AllstackssAreEmpty ==  (\A i \in 1 .. NumberOfProcesses: stacks[i] = <<>>)
    IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => returnValue[i] # returnValue[j])
    IdGeneratorInvariant == AllIsDone => AllstackssAreEmpty /\ IdsAreAllDifferent
  }

  (* update and read are now one atomic step *)
  process(id \in 1 .. NumberOfProcesses) {
   checkLocking: 
   if (Locking) {
        waitForLock: await object.lock = 0;
        lock: object.lock := self;
   };
    \* Load _this_ onto the operand stacks 
    aload0: stacks[self] := Append(stacks[self], object);
    \* copy the top of the stacks 
    dup: stacks[self] := Append(stacks[self], Last(stacks[self]));
    \* retrieve the value of field lastId from the object and store it back on the top of the stacks
    getfield_lastId: 
          with (lastId = Last(stacks[self]).lastId) {
            stacks[self] := Append(Pop(stacks[self]), lastId);
          };
    \* push the integer constant 1 on the stacks 
    iconst_1: stacks[self] := Append(stacks[self], 1);
     \* integer add the top two values on the top of the stacks
    iadd: 
        with (a = Last(stacks[self]), b = Last(Pop(stacks[self]))) {
            stacks[self] := Append(Pop(Pop(stacks[self])) , a+b);
        };
        
    dup_x1: 
        stacks[self] := <<Last(stacks[self])>> \o stacks[self];
     putfield: 
        object.lastId := Last(stacks[self]);
        stacks[self] := Pop(Pop(stacks[self])) ;
     ret: 
        returnValue[self] := Last(stacks[self]);
        stacks[self] := Pop(stacks[self]);
     if (Locking) {        
        unlock: object.lock := 0;
     };
  }
}*)



\* BEGIN TRANSLATION
VARIABLES object, stacks, returnValue, pc

(* define statement *)
Last(S) == S[Len(S)]
Pop(S) == SubSeq(S, 1, Len(S)-1)
AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
AllstackssAreEmpty ==  (\A i \in 1 .. NumberOfProcesses: stacks[i] = <<>>)
IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => returnValue[i] # returnValue[j])
IdGeneratorInvariant == AllIsDone => AllstackssAreEmpty /\ IdsAreAllDifferent


vars == << object, stacks, returnValue, pc >>

ProcSet == (1 .. NumberOfProcesses)

Init == (* Global variables *)
        /\ object = [lastId |-> 42, lock |-> 0]
        /\ stacks = [ i \in 1..NumberOfProcesses |-> <<>>]
        /\ returnValue = [i\in 1..NumberOfProcesses |-> -1]
        /\ pc = [self \in ProcSet |-> "checkLocking"]

checkLocking(self) == /\ pc[self] = "checkLocking"
                      /\ IF Locking
                            THEN /\ pc' = [pc EXCEPT ![self] = "waitForLock"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "aload0"]
                      /\ UNCHANGED << object, stacks, returnValue >>

waitForLock(self) == /\ pc[self] = "waitForLock"
                     /\ object.lock = 0
                     /\ pc' = [pc EXCEPT ![self] = "lock"]
                     /\ UNCHANGED << object, stacks, returnValue >>

lock(self) == /\ pc[self] = "lock"
              /\ object' = [object EXCEPT !.lock = self]
              /\ pc' = [pc EXCEPT ![self] = "aload0"]
              /\ UNCHANGED << stacks, returnValue >>

aload0(self) == /\ pc[self] = "aload0"
                /\ stacks' = [stacks EXCEPT ![self] = Append(stacks[self], object)]
                /\ pc' = [pc EXCEPT ![self] = "dup"]
                /\ UNCHANGED << object, returnValue >>

dup(self) == /\ pc[self] = "dup"
             /\ stacks' = [stacks EXCEPT ![self] = Append(stacks[self], Last(stacks[self]))]
             /\ pc' = [pc EXCEPT ![self] = "getfield_lastId"]
             /\ UNCHANGED << object, returnValue >>

getfield_lastId(self) == /\ pc[self] = "getfield_lastId"
                         /\ LET lastId == Last(stacks[self]).lastId IN
                              stacks' = [stacks EXCEPT ![self] = Append(Pop(stacks[self]), lastId)]
                         /\ pc' = [pc EXCEPT ![self] = "iconst_1"]
                         /\ UNCHANGED << object, returnValue >>

iconst_1(self) == /\ pc[self] = "iconst_1"
                  /\ stacks' = [stacks EXCEPT ![self] = Append(stacks[self], 1)]
                  /\ pc' = [pc EXCEPT ![self] = "iadd"]
                  /\ UNCHANGED << object, returnValue >>

iadd(self) == /\ pc[self] = "iadd"
              /\ LET a == Last(stacks[self]) IN
                   LET b == Last(Pop(stacks[self])) IN
                     stacks' = [stacks EXCEPT ![self] = Append(Pop(Pop(stacks[self])) , a+b)]
              /\ pc' = [pc EXCEPT ![self] = "dup_x1"]
              /\ UNCHANGED << object, returnValue >>

dup_x1(self) == /\ pc[self] = "dup_x1"
                /\ stacks' = [stacks EXCEPT ![self] = <<Last(stacks[self])>> \o stacks[self]]
                /\ pc' = [pc EXCEPT ![self] = "putfield"]
                /\ UNCHANGED << object, returnValue >>

putfield(self) == /\ pc[self] = "putfield"
                  /\ object' = [object EXCEPT !.lastId = Last(stacks[self])]
                  /\ stacks' = [stacks EXCEPT ![self] = Pop(Pop(stacks[self]))]
                  /\ pc' = [pc EXCEPT ![self] = "ret"]
                  /\ UNCHANGED returnValue

ret(self) == /\ pc[self] = "ret"
             /\ returnValue' = [returnValue EXCEPT ![self] = Last(stacks[self])]
             /\ stacks' = [stacks EXCEPT ![self] = Pop(stacks[self])]
             /\ IF Locking
                   THEN /\ pc' = [pc EXCEPT ![self] = "unlock"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED object

unlock(self) == /\ pc[self] = "unlock"
                /\ object' = [object EXCEPT !.lock = 0]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << stacks, returnValue >>

id(self) == checkLocking(self) \/ waitForLock(self) \/ lock(self)
               \/ aload0(self) \/ dup(self) \/ getfield_lastId(self)
               \/ iconst_1(self) \/ iadd(self) \/ dup_x1(self)
               \/ putfield(self) \/ ret(self) \/ unlock(self)

Next == (\E self \in 1 .. NumberOfProcesses: id(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Dec 11 09:12:54 EST 2015 by balopat
\* Created Thu Dec 10 19:27:24 EST 2015 by balopat
