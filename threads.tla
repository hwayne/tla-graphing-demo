------------------------------ MODULE threads ------------------------------
EXTENDS Integers
CONSTANT NumThreads
Threads == 1..NumThreads
(* --algorithm threads

variables 
  x = 0;

process thread \in Threads
variables tmp = 0;
begin
  Get:
    tmp := x;

  Inc:
    x := tmp + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2cfd730c7e541cfac6a18f77d5288391
VARIABLES x, pc, tmp

vars == << x, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ x = 0
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "Get"]

Get(self) == /\ pc[self] = "Get"
             /\ tmp' = [tmp EXCEPT ![self] = x]
             /\ pc' = [pc EXCEPT ![self] = "Inc"]
             /\ x' = x

Inc(self) == /\ pc[self] = "Inc"
             /\ x' = tmp[self] + 1
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ tmp' = tmp

thread(self) == Get(self) \/ Inc(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3b1540a4627b3d3586cb172c60eb0c0c
====

