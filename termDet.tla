-------------------- MODULE termDet -------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, MaxT
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(* 
--algorithm termDet {
  variables
  chan = [n \in 0..N |-> <<>>];  \* FIFO channels 


  macro send(des, msg) {
      chan[des] := Append(chan[des], msg);
  }

  macro receive(msg) {
      when Len(chan[self]) > 0;
      msg := Head(chan[self]);
      chan[self] := Tail(chan[self]);
  }


  fair process (j \in Procs)
  variables
  T=0;
  m=0;
  active=TRUE;
  \*outc =0;
  outc =[n \in 0..N |-> 0]; 
  inc  =0;
  {
P:    while (T<MaxT){  
        T := T+1;
        \* Write the code for the actions using either or
        either
        {
        await (active=TRUE);
        
        \* send
        with( des \in Procs)
        { 
        
        send(des,m);
\*        outc:=outc+1;

        outc[des] := outc[des]+1;
        
        
        }
        };
        or
        {
\*        recieve
        
        receive(m);
\*        T:= T+1;
        active:=TRUE;
        inc:=inc+1;
        };
        or
        {
\*        to idle
        
        await (active=TRUE);
\*        T:= T+1;
        active:=FALSE;
        send(0,<<self,inc,outc>>);
        
        
        outc := [n \in 0..N |-> 0];
        
        
        };
      }
  }


  fair process (d \in {0}) \* Detector process
  variables
  done=FALSE;
  msg= <<>>;
  notified={};
  \*outS= 0;
  \*inS = 0;
  c=0;
  outS = [n \in 0..N |-> 0];
  inS = [n \in 0..N |-> 0];
  {
D:  while(~done) {
        receive(msg);
        \* Write the code to implement detector logic
        notified:=notified \union {msg[1]};
    \*    inS:=inS+msg[2];
        inS[msg[1]] := msg[2];
        
        
    \*    outS:=outS+msg[3];
    
        c:=0;
     E:    while(c < N) {
             
                c := c+1;
                outS[c] := outS[c] + msg[3][c];
            } ;
        
        
        if ((Cardinality(notified)=N) /\ (\A h \in Procs: inS[h]=outS[h])) {
        
        done:=TRUE;
        }
    }
  }

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4de51e2946e8eae7c21c85098ec46982
VARIABLES chan, pc, T, m, active, outc, inc, done, msg, notified, c, outS, 
          inS

vars == << chan, pc, T, m, active, outc, inc, done, msg, notified, c, outS, 
           inS >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ chan = [n \in 0..N |-> <<>>]
        (* Process j *)
        /\ T = [self \in Procs |-> 0]
        /\ m = [self \in Procs |-> 0]
        /\ active = [self \in Procs |-> TRUE]
        /\ outc = [self \in Procs |-> [n \in 0..N |-> 0]]
        /\ inc = [self \in Procs |-> 0]
        (* Process d *)
        /\ done = [self \in {0} |-> FALSE]
        /\ msg = [self \in {0} |-> <<>>]
        /\ notified = [self \in {0} |-> {}]
        /\ c = [self \in {0} |-> 0]
        /\ outS = [self \in {0} |-> [n \in 0..N |-> 0]]
        /\ inS = [self \in {0} |-> [n \in 0..N |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "P"
                                        [] self \in {0} -> "D"]

P(self) == /\ pc[self] = "P"
           /\ IF T[self]<MaxT
                 THEN /\ T' = [T EXCEPT ![self] = T[self]+1]
                      /\ \/ /\ (active[self]=TRUE)
                            /\ \E des \in Procs:
                                 /\ chan' = [chan EXCEPT ![des] = Append(chan[des], m[self])]
                                 /\ outc' = [outc EXCEPT ![self][des] = outc[self][des]+1]
                            /\ UNCHANGED <<m, active, inc>>
                         \/ /\ Len(chan[self]) > 0
                            /\ m' = [m EXCEPT ![self] = Head(chan[self])]
                            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                            /\ active' = [active EXCEPT ![self] = TRUE]
                            /\ inc' = [inc EXCEPT ![self] = inc[self]+1]
                            /\ outc' = outc
                         \/ /\ (active[self]=TRUE)
                            /\ active' = [active EXCEPT ![self] = FALSE]
                            /\ chan' = [chan EXCEPT ![0] = Append(chan[0], (<<self,inc[self],outc[self]>>))]
                            /\ outc' = [outc EXCEPT ![self] = [n \in 0..N |-> 0]]
                            /\ UNCHANGED <<m, inc>>
                      /\ pc' = [pc EXCEPT ![self] = "P"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, T, m, active, outc, inc >>
           /\ UNCHANGED << done, msg, notified, c, outS, inS >>

j(self) == P(self)

D(self) == /\ pc[self] = "D"
           /\ IF ~done[self]
                 THEN /\ Len(chan[self]) > 0
                      /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                      /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                      /\ notified' = [notified EXCEPT ![self] = notified[self] \union {msg'[self][1]}]
                      /\ inS' = [inS EXCEPT ![self][msg'[self][1]] = msg'[self][2]]
                      /\ c' = [c EXCEPT ![self] = 0]
                      /\ pc' = [pc EXCEPT ![self] = "E"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, msg, notified, c, inS >>
           /\ UNCHANGED << T, m, active, outc, inc, done, outS >>

E(self) == /\ pc[self] = "E"
           /\ IF c[self] < N
                 THEN /\ c' = [c EXCEPT ![self] = c[self]+1]
                      /\ outS' = [outS EXCEPT ![self][c'[self]] = outS[self][c'[self]] + msg[self][3][c'[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "E"]
                      /\ done' = done
                 ELSE /\ IF (Cardinality(notified[self])=N) /\ (\A h \in Procs: inS[self][h]=outS[self][h])
                            THEN /\ done' = [done EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ done' = done
                      /\ pc' = [pc EXCEPT ![self] = "D"]
                      /\ UNCHANGED << c, outS >>
           /\ UNCHANGED << chan, T, m, active, outc, inc, msg, notified, inS >>

d(self) == D(self) \/ E(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: d(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(d(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4be2ca757fef6d2c5e42f9fe77b8b04a

Safety   == done[0] => ((\A s \in Procs: active[s]=FALSE) /\ (\A f \in Procs: chan[f]= <<>>))
Progress == ((\A s \in Procs: active[s]=FALSE) /\ (\A f \in Procs: chan[f]= <<>>)) ~> done[0]
==================================================

\* Include the team member names here 
Aniruddha Karlekar - (50314912 akarleka@buffalo.edu)
Vinay Krishna Sudarshana - (50321417 vinaykri@buffalo.edu)

The termination detection problem involves N processes that can  be in 2 states: active and idle. Each process can perform 3 actions: send, receive and become idle. Only an active process can do the send and become idle action. An idle process however can become active by performing a receive action. We need to determine when the system terminates, i.e. all the processes are idle and the channels are empty.

The problem with using a single integer for inC and outC as explained in the last part of the previous section is that we wrongly conclude that the channels are empty. 

We can solve this problem by making each process maintain 

a) A tuple of N integers to keep track of how many messages are sent to every other process.

b) Like the previous case each process also maintains a 1 integer (inC) to denote how many messages it received in total. 

We implement this by making every process maintain a function outC with domain 1..N and initialize each value to 0.

Whenever a process A chooses to perform a send action to a destination D that is chosen non deterministically. We increment the D’th value of the function outC in the process A.

Whenever a process chooses to perform it’s receive action, the message is read and it’s inC value is incremented. If the process was initially IDLE it becomes ACTIVE upon performing the receive action when it’s channel is non-empty.

Whenever a process(ACTIVE) chooses to do the idle action, it sends to the detector a message with its process id, integer inC and the function outC as a tuple. It also resets all the values of outC to 0. 

In this scenario, the detector has the following information:

a) Total number of messages that were recorded as being sent TO EACH CHANNEL (Vector inS). We implement this by maintaining a function inS with domain 1..N and initialize each value to 0.

b) Total number of messages that were recorded as being received BY EACH CHANNEL. (Vector outS). We implement this by maintaining a function outS with domain 1..N and initialize each value to 0.

c) Set of processes that were notified as idle to the detector. This is implemented as a set notified, that maintains the set of processes that have notified the detector of being idle.

The detector upon performing a receive action will read a message that contains three fields :

a) Process ID i

b) inC of that process - which is the number of messages it read.

c) outC of that process - which is a function with domain 1..N where N is the number of Processes. outC is the number of messages it sent to each process or more accurately the number of messages that it recorded as being sent by putting it into the destination’s channel.

The detector then :

a) Adds process with process ID i to the set notified.

b) Updates the inS of that process i which is the i’th value in it’s function inS, by simply updating the value with the value it received.

c) Updates the outS of that process i which is the i’th value in it’s function outS, by adding the received value to the old value for each entry in the function.

We set the done variable only when each channel notifies the detector of being idle and each channel’s inS is equal to it’s outS. 

Therefore, if we go back to example A in the last paragraph of previous section, i.e if you have two messages - one (let’s call it alpha)  that was sent by process A to B and another message that was sent by process B to A (let’s call it Beta). In the case where message alpha was being recorded as sent, the detector’s outS vector would be [0,1] and beta is being recorded as received the detector’s inS vector would be [1,0]. So we capture enough information here to say the detector will not set the variable DONE and claim termination has reached. So we can say the detector has enough information to overcome the problem discussed in example A.


SAFETY AND PROGRESS PROPERTIES

The safety property that we have considered is :

Safety == done[0] => ((\A s \in Procs: active[s]=FALSE)  /\  (\A f \in Procs: chan[f]= <<>>))

The safety property states that if done is true implies that all the processes are idle (i.e their ACTIVE=FALSE) and channels are empty. (All the channels are empty tuples which means every message that was put in it has been picked up making them empty.)

The progress property that we considered is :

Progress == ((\A s \in Procs: active[s]=FALSE) /\ (\A f \in Procs: chan[f]= <<>>)) ~> done[0]

The progress property states that if at any state if all the processes are idle and all the channels are empty, then at a later state done is set. This means that a state where all the processes are idle and all the channels are empty, leads to a state where done is set to TRUE.
