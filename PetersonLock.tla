---------------------------- MODULE PetersonLock ----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

(** --algorithm PetersonLock
variables flag = [i \in 1..2 |-> FALSE], victim = 0;

procedure Lock(index) 
variables another_index = 0;
begin
  FlagRaising:
    flag[index] := TRUE;
  VictimAppointment:
    victim := index;
  AnotherIndex:
    another_index := (3 - index);
  Awaiting:
    await (flag[another_index] /\ victim = index);
    return;
end procedure;

procedure Unlock(index) 
begin
   RunUnlock:
    flag[index] := FALSE;
    return;
end procedure;

fair process criticalResource \in 1..2
begin
   CallLock:
    call Lock(self);
   CallUnlock:
    call Unlock(self);
end process;

end algorithm; **)
\* BEGIN TRANSLATION
\* Parameter index of procedure Lock at line 7 col 16 changed to index_
CONSTANT defaultInitValue
VARIABLES flag, victim, pc, stack, index_, another_index, index

vars == << flag, victim, pc, stack, index_, another_index, index >>

ProcSet == ({1, 2})

Init == (* Global variables *)
        /\ flag = [i \in 1..2 |-> FALSE]
        /\ victim = 0
        (* Procedure Lock *)
        /\ index_ = [ self \in ProcSet |-> defaultInitValue]
        /\ another_index = [ self \in ProcSet |-> 0]
        (* Procedure Unlock *)
        /\ index = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "CallLock"]

FlagRaising(self) == /\ pc[self] = "FlagRaising"
                     /\ flag' = [flag EXCEPT ![index_[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "VictimAppointment"]
                     /\ UNCHANGED << victim, stack, index_, another_index, 
                                     index >>

VictimAppointment(self) == /\ pc[self] = "VictimAppointment"
                           /\ victim' = index_[self]
                           /\ pc' = [pc EXCEPT ![self] = "AnotherIndex"]
                           /\ UNCHANGED << flag, stack, index_, another_index, 
                                           index >>

AnotherIndex(self) == /\ pc[self] = "AnotherIndex"
                      /\ another_index' = [another_index EXCEPT ![self] = (3 - index_[self])]
                      /\ pc' = [pc EXCEPT ![self] = "Awaiting"]
                      /\ UNCHANGED << flag, victim, stack, index_, index >>

Awaiting(self) == /\ pc[self] = "Awaiting"
                  /\ (flag[another_index[self]] /\ victim = index_[self])
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ another_index' = [another_index EXCEPT ![self] = Head(stack[self]).another_index]
                  /\ index_' = [index_ EXCEPT ![self] = Head(stack[self]).index_]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << flag, victim, index >>

Lock(self) == FlagRaising(self) \/ VictimAppointment(self)
                 \/ AnotherIndex(self) \/ Awaiting(self)

RunUnlock(self) == /\ pc[self] = "RunUnlock"
                   /\ flag' = [flag EXCEPT ![index[self]] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ index' = [index EXCEPT ![self] = Head(stack[self]).index]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << victim, index_, another_index >>

Unlock(self) == RunUnlock(self)

CallLock(self) == /\ pc[self] = "CallLock"
                  /\ /\ index_' = [index_ EXCEPT ![self] = self]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Lock",
                                                              pc        |->  "CallUnlock",
                                                              another_index |->  another_index[self],
                                                              index_    |->  index_[self] ] >>
                                                          \o stack[self]]
                  /\ another_index' = [another_index EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "FlagRaising"]
                  /\ UNCHANGED << flag, victim, index >>

CallUnlock(self) == /\ pc[self] = "CallUnlock"
                    /\ /\ index' = [index EXCEPT ![self] = self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Unlock",
                                                                pc        |->  "Done",
                                                                index     |->  index[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "RunUnlock"]
                    /\ UNCHANGED << flag, victim, index_, another_index >>

criticalResource(self) == CallLock(self) \/ CallUnlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Lock(self) \/ Unlock(self))
           \/ (\E self \in {1, 2}: criticalResource(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : /\ WF_vars(criticalResource(self))
                                /\ WF_vars(Lock(self))
                                /\ WF_vars(Unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 25 17:50:36 MSK 2019 by a17883227
\* Created Mon Dec 23 02:39:29 MSK 2019 by a17883227
