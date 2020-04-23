------------------------------- MODULE vchan -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Byte \* 0..255, but overridable for modelling purposes. Consider especially 1..max(Len(Sent))+MaxWriteLen

(* The size of the ring buffer in bytes. *)
CONSTANT BufferSize
ASSUME BufferSize \in Nat \ {0}

(* The most data a sender will try to send in one go. *)
CONSTANT MaxWriteLen
ASSUME MaxWriteLen \in Nat \ {0}

(* The most data a receiver will try to read in one go. *)
CONSTANT MaxReadLen
ASSUME MaxReadLen \in Nat \ {0}

(* Endpoint automata *)
Idle == "Idle"
Writing == "Writing"
AfterWriting == "AfterWriting"
Reading == "Reading"
AfterReading == "AfterReading"
Blocked == "Blocked"
Done == "Done"
SenderStates == {Idle, Writing, AfterWriting, Blocked, Done}
ReceiverStates == {Idle, Reading, AfterReading, Blocked, Done}

----------------

Min(x, y) == IF x < y THEN x ELSE y

(* Take(m, i) is the first i elements of message m. *)
Take(m, i) == SubSeq(m, 1, i)

(* Everything except the first i elements of message m. *)
Drop(m, i) == SubSeq(m, i + 1, Len(m))

Clear(f) == f' = FALSE
Set(f) == f' = TRUE

Empty(b) == Len(b) = 0

NotEmpty(b) == Len(b) > 0
----------------

VARIABLES
  (* history variables (for modelling and properties) *)
  Sent,
  Got,
  
  (* The remaining data that has not yet been added to the buffer: *)
  msg,
  
  (* status of the endpoints. *)
  SenderLive,   \* init true, cleared by sender
  ReceiverLive, \* init true, cleared by receiver

  SenderState,   \* {Idle, Writing, AfterWriting, Blocked, Done}
  ReceiverState, \* {Idle, Reading, AfterReading, Blocked, Done}

  (* NotifyWrite is a shared flag that is set by the receiver to indicate that it wants to know when data
     has been written to the buffer. The sender checks it after adding data. If set, the sender
     clears the flag and notifies the receiver using the event channel. This is represented by
     ReceiverIT being set to TRUE. It becomes FALSE when the receiver handles the event. *)
  NotifyWrite,   \* Set by receiver, cleared by sender
  ReceiverIT,    \* Set by sender, cleared by receiver

  (* Buffer represents the data in transit from the sender to the receiver. *)
  Buffer,
  
  (* NotifyRead is a shared flag that indicates that the sender wants to know when some data
     has been read and removed from the buffer (and, therefore, that more space is now available).
     If the receiver sees that this is set after removing data from the buffer,
     it clears the flag and signals the sender via the event channel, represented by SenderIT. *)
  NotifyRead,         \* Set by sender, cleared by receiver
  SenderIT            \* Set by receiver, cleared by sender

----------------------------------------------------------------

MSG(len) == { [ x \in 1..N |-> Len(Sent) + x ] : N \in 1..len }
MESSAGE == MSG(MaxWriteLen)

vars == << Sent, Got, SenderLive, ReceiverLive, SenderState, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

ZeroToFive == 0..5

LimitSent == Len(Sent) < 4

----------------------------------------------------------------

Init == /\ SenderLive = TRUE
        /\ ReceiverLive = TRUE
        /\ ReceiverState = Idle
        /\ SenderState = Idle
        /\ Got = << >>
        /\ Sent = << >>
        /\ msg = << >>
        /\ Buffer = << >>
        /\ NotifyWrite = FALSE
        /\ ReceiverIT = FALSE
        /\ NotifyRead = FALSE
        /\ SenderIT = FALSE

----------------

\* receiver not live: idle R done
SenderIdle1 == /\ SenderLive
               /\ SenderState = Idle
               /\ ~ReceiverLive
               /\ SenderState' = Done
               /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

\* idle R write
SenderIdle2 == /\ SenderLive
               /\ SenderState = Idle
               /\ \E m \in MSG(MaxWriteLen):
                     /\ msg' = m
                     /\ Sent' = Sent \o m
               /\ SenderState' = Writing
               /\ UNCHANGED <<Got, SenderLive, ReceiverLive, ReceiverState, Buffer, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

\* Still free space: Write R AfterWriting
SenderWrite1 ==
    /\ SenderLive
    /\ SenderState = Writing
    /\ \E n \in 1..Len(msg):
        /\ n < MaxWriteLen
        /\ Buffer' = Buffer \o Take(msg, n)
        /\ msg' = Drop(msg, n)
    /\ Len(Buffer') < BufferSize
    /\ SenderState' = AfterWriting
    /\ Set(NotifyRead)
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, SenderIT, NotifyWrite, ReceiverIT >>

\* no free space: Write R Blocked
SenderWrite2 ==
    /\ SenderLive
    /\ ReceiverLive
    /\ SenderState = Writing
    /\ \E n \in 1..Len(msg):
        /\ n < MaxWriteLen
        /\ Buffer' = Buffer \o Take(msg, n)
        /\ msg' = Drop(msg, n)
    /\ Len(Buffer') = BufferSize
    /\ SenderState' = Blocked
    /\ Set(NotifyRead)
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, NotifyWrite, ReceiverIT, SenderIT >>

(*
    Fix deadlock when the Sender write everything, msg is empty and so fall into the Blocked state.
    When the receiver will wake-up and read, it will notify the Sender with SenderIT. But when the
    sender will execute the action UnblockSender, that will put it in the Writing state. THe problem is
    that the msg is empty, so it's impossible to execute SenderWrite1 or SenderWrite2, so it's running into a deadlock.
    To fix this, we add this action to override this problem. It will pass the Sender in Writing State into the AfterWriting state when
    the message is empty.

    NOTE: not sure if it's the best solution
*)
SenderWrite3 ==
    /\ SenderLive
    /\ ReceiverLive
    /\ SenderState = Writing
    /\ Empty(msg)
    /\ Empty(Buffer)
    /\ SenderState' = AfterWriting
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, NotifyWrite, ReceiverIT, SenderIT, NotifyRead, Buffer, msg >>



\* all sent: afterWriting R idle
SenderWriteNext1 ==
    /\ SenderLive
    /\ SenderState = AfterWriting
    /\ Empty(msg)
    /\ IF NotifyWrite
        THEN
            /\ Clear(NotifyWrite)
            /\ Set(ReceiverIT)
        ELSE
            UNCHANGED <<NotifyWrite, ReceiverIT>>
    /\ SenderState' = Idle
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, Buffer, msg, SenderIT, NotifyRead >>

\* not all sent: afterwriting R blocked
SenderWriteNext2 ==
    /\ SenderLive
    /\ SenderState = AfterWriting
    /\ NotEmpty(msg)
    /\ IF NotifyWrite = TRUE
        THEN
            /\ Clear(NotifyWrite)
            /\ Set(ReceiverIT)
        ELSE
            UNCHANGED <<NotifyWrite, ReceiverIT>>
    /\ SenderState' = Blocked
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, Buffer, msg, SenderIT, NotifyRead >>

\* receiver live & IT: blocked R writing
SenderUnblock1 ==
    /\ SenderLive
    /\ SenderState = Blocked
    /\ ReceiverLive
    /\ SenderIT
    /\ SenderState' = Writing
    /\ Clear(SenderIT)
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead >>

\* IT & receiver not live: blocked R done
SenderUnblock2 ==
    /\ SenderLive
    /\ SenderState = Blocked
    /\ ~ReceiverLive
    /\ SenderIT
    /\ SenderState' = Done
    /\ Clear(SenderIT)
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead >>

\* End because the receiver has abort
SenderEnd ==
    /\ SenderLive
    /\ ~ReceiverLive
    /\ SenderLive' = FALSE
    /\ SenderState' = Done
    /\ UNCHANGED << Sent, Got, ReceiverLive, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

----------------

\* buffer empty & sender live: Idle R Blocked
ReceiverIdle1 == /\ ReceiverLive
                 /\ ReceiverState = Idle
                 /\ SenderLive
                 /\ Empty(Buffer)
                 /\ ReceiverState' = Blocked
                 /\ Set(NotifyWrite)
                 /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, SenderState, Buffer, msg, ReceiverIT, NotifyRead, SenderIT >>

\* buffer non empty: Idle R Reading
ReceiverIdle2 ==
    /\ ReceiverLive
    /\ ReceiverState = Idle
    /\ NotEmpty(Buffer)
    /\ ReceiverState' = Reading
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, SenderState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

\* buffer empty & sender not live : Idle R Done
ReceiverIdle3 ==
    /\ ReceiverLive
    /\ ReceiverState = Idle
    /\ Empty(Buffer)
    /\ ~SenderLive
    /\ ReceiverState' = Done
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, SenderState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

\* Reading R AfterReading
ReceiverRead ==
    /\ ReceiverLive
    /\ ReceiverState = Reading
    /\ \E n \in 1..Len(Buffer): \* read arbitrary number of element
        /\ n < MaxReadLen
        /\ Got' = Got \o Take(Buffer, n)
        /\ Buffer' = Drop(Buffer, n)
    /\ ReceiverState' = AfterReading
    /\ Set(NotifyWrite)
    /\ UNCHANGED << Sent, SenderLive, ReceiverLive, SenderState, msg, ReceiverIT, NotifyRead, SenderIT >>


\* AfterReading R Idle
ReceiverReadNext ==
    /\ ReceiverLive
    /\ ReceiverState = AfterReading
    /\ IF NotifyRead
        THEN
            /\ Clear(NotifyRead)
            /\ Set(SenderIT)
        ELSE
            UNCHANGED <<NotifyRead, SenderIT>>
    /\ ReceiverState' = Idle
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, SenderState, Buffer, msg, NotifyWrite, ReceiverIT >>


\* sender it: Blocked R Idle
ReceiverUnblock ==
    /\ ReceiverLive
    /\ ReceiverState = Blocked
    /\ ReceiverIT
    /\ ReceiverState' = Idle
    /\ Clear(ReceiverIT)
    /\ UNCHANGED << Sent, Got, SenderLive, ReceiverLive, SenderState, Buffer, msg, NotifyWrite, NotifyRead, SenderIT >>

ReceiverEnd ==
    /\ ReceiverLive
    /\ ~SenderLive
    /\ Got' = Got \o Take(Buffer, Len(Buffer))
    /\ Buffer' = Drop(Buffer, Len(Buffer))
    /\ ReceiverState' = Done
    /\ UNCHANGED << Sent, SenderLive, ReceiverLive, SenderState, msg, NotifyWrite, ReceiverIT, NotifyRead, SenderIT >>

----------------

(* Asynchronous abort of any endpoint. *)

SenderClose ==
    /\ SenderLive
    /\ SenderState' = Done
    /\ SenderLive' = FALSE
    /\ SenderIT' = TRUE
    /\ UNCHANGED << Sent, Got, ReceiverLive, ReceiverState, Buffer, msg, NotifyWrite, ReceiverIT, NotifyRead >>

ReceiverClose ==
    /\ ReceiverLive
    /\ ReceiverState' = Done
    /\ ReceiverLive' = FALSE
    /\ ReceiverIT' = TRUE
    /\ UNCHANGED << Sent, Got, SenderLive, SenderState, Buffer, msg, NotifyWrite, NotifyRead, SenderIT >>

----------------

(* Spurious interruption *)

----------------

Close == SenderClose \/ ReceiverClose

SenderNext == SenderIdle1 \/ SenderIdle2 \/ SenderWrite1 \/ SenderWrite2 \/ SenderWriteNext1 \/ SenderWriteNext2 \/ SenderUnblock1 \/ SenderUnblock2 \/ SenderEnd \/ SenderWrite3

ReceiverNext == ReceiverIdle1 \/ ReceiverIdle2 \/ ReceiverIdle3 \/ ReceiverRead \/ ReceiverReadNext \/ ReceiverUnblock \/ ReceiverEnd

Next == SenderNext \/ ReceiverNext

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------
TypeOk ==
    /\ Sent \in Seq(Byte)
    /\ Got \in Seq(Byte)
    /\ Buffer \in Seq(Byte)
    /\ SenderLive \in BOOLEAN
    /\ ReceiverLive \in BOOLEAN
    /\ NotifyWrite \in BOOLEAN
    /\ SenderIT \in BOOLEAN
    /\ NotifyRead \in BOOLEAN
    /\ ReceiverIT \in BOOLEAN
    /\ SenderState \in {Idle, Writing, AfterWriting, Blocked, Done}
    /\ ReceiverState \in {Idle, Reading, AfterReading, Blocked, Done}
    /\ msg \in Seq(Byte)

(* Whatever we receive is the same as what was sent (i.e. `Got' is a prefix of `Sent') *)
Integrity == (Take(Sent, Len(Got)) = Got)
  
(* Any data that the write function reports has been sent successfully (i.e.
   data in Sent when it is back at "ready") will eventually be received (if
   the receiver doesn't close the connection). In particular, this says that
   it's OK for the sender to close its end immediately after sending some data. *)
Availability ==
  \A x \in 0..Cardinality(Byte) : x = Len(Sent) /\ SenderState = Idle ~> (Len(Got) >= x)

(* If either side closes the connection, both end up in their Done state *)
ShutdownOK == (~SenderLive \/ ~ReceiverLive) ~> (SenderState = Done /\ ReceiverState = Done)

(* If both ends never close the connection (and Sent is finite), then the receiver eventually gets all the sent bytes. *)
NoLoss == <>(Got = Sent)

================================================================
