---------------------------- MODULE PetersonLock ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

Not(v) == IF v = 0 THEN 1 ELSE 0

(* INVARIANTS *)
\*MutualExclusion == ~ (pc[0] = "cs" /\ pc[1] = "cs")   
(* INVARIANTS *)

(** --algorithm PetersonLock
variables flag = [index \in {0, 1} |-> FALSE], victim = 0;

fair process proc \in {0, 1}
begin
start:
while TRUE do
   lraise: flag[self] := TRUE;
   lvictim: victim := self;
   \* блокируем пока условие flag[Not(self)] /\ (victim = self) перестанет выполняться (~ = not)   
   lawait: await ~(flag[Not(self)] /\ (victim = self));
   cs: skip; \* critical section
   ulower: flag[self] := FALSE;
end while;   
end process;

end algorithm; **)
\* BEGIN TRANSLATION
VARIABLES flag, victim, pc

vars == << flag, victim, pc >>

ProcSet == ({0, 1})
MutualExclusion == ~ (pc[0] = "cs" /\ pc[1] = "cs")  
Init == (* Global variables *)
        /\ flag = [index \in {0, 1} |-> FALSE]
        /\ victim = 0
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "lraise"]
               /\ UNCHANGED << flag, victim >>

lraise(self) == /\ pc[self] = "lraise"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "lvictim"]
                /\ UNCHANGED victim

lvictim(self) == /\ pc[self] = "lvictim"
                 /\ victim' = self
                 /\ pc' = [pc EXCEPT ![self] = "lawait"]
                 /\ flag' = flag

lawait(self) == /\ pc[self] = "lawait"
                /\ ~(flag[Not(self)] /\ (victim = self))
                /\ pc' = [pc EXCEPT ![self] = "cs"]
                /\ UNCHANGED << flag, victim >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "ulower"]
            /\ UNCHANGED << flag, victim >>

ulower(self) == /\ pc[self] = "ulower"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "start"]
                /\ UNCHANGED victim

proc(self) == start(self) \/ lraise(self) \/ lvictim(self) \/ lawait(self)
                 \/ cs(self) \/ ulower(self)

Next == (\E self \in {0, 1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0, 1} : WF_vars(proc(self))

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Dec 26 08:59:07 MSK 2019 by a17883227
\* Created Mon Dec 23 02:39:29 MSK 2019 by a17883227
