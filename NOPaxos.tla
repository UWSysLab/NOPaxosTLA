------------------------------ MODULE NOPaxos ----------------------------------
(*

  Specifies the NOPaxos protocol.

*)


EXTENDS Naturals, FiniteSets, Sequences

--------------------------------------------------------------------------------
(* `^\textbf{\large Constants}^' *)

\* The set of replicas and an ordering of them
CONSTANTS Replicas, ReplicaOrder
ASSUME IsFiniteSet(Replicas) /\ ReplicaOrder \in Seq(Replicas)

\* Message sequencers
CONSTANT NumSequencers \* Normally infinite, assumed finite for model checking
Sequencers == (1..NumSequencers)

\* Set of possible values in a client request and a special null value
CONSTANTS Values, NoOp

\* Replica Statuses
CONSTANTS StNormal, StViewChange, StGapCommit

\* Message Types
CONSTANTS MClientRequest,       \* Sent by client to sequencer
          MMarkedClientRequest, \* Sent by sequencer to replicas
          MRequestReply,        \* Sent by replicas to client
          MSlotLookup,          \* Sent by followes to get the value of a slot
          MSlotLookupRep,       \* Sent by the leader with a value/NoOp
          MGapCommit,           \* Sent by the leader to commit a gap
          MGapCommitRep,        \* Sent by the followers to ACK a gap commit
          MViewChangeReq,       \* Sent when leader/sequencer failure detected
          MViewChange,          \* Sent to ACK view change
          MStartView,           \* Sent by new leader to start view
          MSyncPrepare,         \* Sent by the leader to ensure log durability
          MSyncRep,             \* Sent by followers as ACK
          MSyncCommit           \* Sent by leaders to indicate stable log

(*
  `^\textbf{Message Schemas}^'

ViewIDs == [ leaderNum |-> n \in (1..), sessNum |-> n \in (1..) ]

  ClientRequest
      [ mtype |-> MClientRequest,
        value |-> v \in Values ]

  MarkedClientRequest
      [ mtype      |-> MMarkedClientRequest,
        dest       |-> r \in Replicas,
        value      |-> v \in Values,
        sessNum    |-> s \in Sequencers,
        sessMsgNum |-> n \in (1..) ]

  RequestReply
      [ mtype      |-> MRequestReply,
        sender     |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        request    |-> v \in Values \cup {NoOp},
        logSlotNum |-> n \in (1..) ]

  SlotLookup
      [ mtype      |-> MSlotLookup,
        dest       |-> r \in Replicas,
        sender     |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        sessMsgNum |-> n \in (1..) ]

  GapCommit
      [ mtype      |-> MGapCommit,
        dest       |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        slotNumber |-> n \in (1..) ]

  GapCommitRep
      [ mtype      |-> MGapCommitRep,
        dest       |-> r \in Replicas,
        sender     |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        slotNumber |-> n \in (1..) ]

  ViewChangeReq
      [ mtype  |-> MViewChangeReq,
        dest   |-> r \in Replicas,
        viewID |-> v \in ViewIDs ]

  ViewChange
      [ mtype      |-> MViewChange,
        dest       |-> r \in Replicas,
        sender     |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        lastNormal |-> v \in ViewIDs,
        sessMsgNum |-> n \in (1..),
        log        |-> l \in (1..) \times (Values \cup {NoOp}) ]

  StartView
      [ mtype      |-> MStartView,
        dest       |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        log        |-> l \in (1..) \times (Values \cup {NoOp}),
        sessMsgNum |-> n \in (1..) ]

  SyncPrepare
      [ mtype      |-> MSyncPrepare,
        dest       |-> r \in Replicas,
        sender     |-> r \in Replicas,
        viewID     |-> v \in ViewIDs,
        sessMsgNum |-> n \in (1..),
        log        |-> l \in (1..) \times (Values \cup {NoOp}) ]

  SyncRep
      [ mtype         |-> MSyncRep,
        dest          |-> r \in Replicas,
        sender        |-> r \in Replicas,
        viewID        |-> v \in ViewIDs,
        logSlotNumber |-> n \in (1..) ]

  SyncCommit
      [ mtype         |-> MSyncCommit,
        dest          |-> r \in Replicas,
        sender        |-> r \in Replicas,
        viewID        |-> v \in ViewIDs,
        log           |-> l \in (1..) \times (Values \cup {NoOp}),
        sessMsgNum    |-> n \in (1..) ]

*)

--------------------------------------------------------------------------------
(* `^\textbf{\large Variables}^' *)

\* `^\textbf{Network State}^'
VARIABLE messages \* Set of all messages sent

networkVars      == << messages >>
InitNetworkState == messages = {}

\* `^\textbf{Sequencer State}^'
VARIABLE seqMsgNums

sequencerVars      == << seqMsgNums >>
InitSequencerState == seqMsgNums = [ s \in Sequencers |-> 1 ]

\* `^\textbf{Replica State}^'
VARIABLES vLog,            \* Log of values and gaps
          vSessMsgNum,     \* The number of messages received in the OUM session
          vReplicaStatus,  \* One of StNormal, StViewChange, and StGapCommit
          vViewID,         \* Current viewID replicas recognize
          vLastNormView,   \* Last views in which replicas had status StNormal
          vViewChanges,    \* Used for logging view change votes
          vCurrentGapSlot, \* Used for gap commit at leader
          vGapCommitReps,  \* Used for logging gap commit reps at leader
          vSyncPoint,      \* Synchronization point for replicas
          vTentativeSync,  \* Used by leader to mark current syncing point
          vSyncReps        \* Used for logging sync reps at leader

replicaVars      == << vLog, vViewID, vSessMsgNum, vLastNormView, vViewChanges,
                       vGapCommitReps, vCurrentGapSlot, vReplicaStatus,
                       vSyncPoint, vTentativeSync, vSyncReps >>
InitReplicaState ==
  /\ vLog            = [ r \in Replicas |-> << >> ]
  /\ vViewID         = [ r \in Replicas |->
                           [ sessNum |-> 1, leaderNum |-> 1 ] ]
  /\ vLastNormView   = [ r \in Replicas |->
                           [ sessNum |-> 1, leaderNum |-> 1 ] ]
  /\ vSessMsgNum     = [ r \in Replicas |-> 1 ]
  /\ vViewChanges    = [ r \in Replicas |-> {} ]
  /\ vGapCommitReps  = [ r \in Replicas |-> {} ]
  /\ vCurrentGapSlot = [ r \in Replicas |-> 0 ]
  /\ vReplicaStatus  = [ r \in Replicas |-> StNormal ]
  /\ vSyncPoint      = [ r \in Replicas |-> 0 ]
  /\ vTentativeSync  = [ r \in Replicas |-> 0 ]
  /\ vSyncReps       = [ r \in Replicas |-> {} ]

\* `^\textbf{Set of all vars}^'
vars == << networkVars, sequencerVars, replicaVars >>

\* `^\textbf{Initial state}^'
Init == /\ InitNetworkState
        /\ InitSequencerState
        /\ InitReplicaState

--------------------------------------------------------------------------------
(* `^\textbf{\large Helpers}^' *)

Max(s) == CHOOSE x \in s : \A y \in s : x >= y


\* `^\textbf{View ID Helpers}^'
Leader(viewID) == ReplicaOrder[(viewID.leaderNum % Len(ReplicaOrder)) +
                               (IF viewID.leaderNum >= Len(ReplicaOrder)
                                THEN 1 ELSE 0)]
ViewLe(v1, v2) == /\ v1.sessNum    <= v2.sessNum
                  /\ v1.leaderNum <= v2.leaderNum
ViewLt(v1, v2) == ViewLe(v1, v2) /\ v1 /= v2


\* `^\textbf{Network Helpers}^'
\* Add a message to the network
Send(ms) == messages' = messages \cup ms

\* `^\textbf{Log Manipulation Helpers}^'
(* Combine logs, taking a NoOp for any slot that has a NoOp and a Value
   otherwise. *)
CombineLogs(ls) ==
  LET
    combineSlot(xs) == IF NoOp \in xs THEN
                         NoOp
                       ELSE IF xs = {} THEN
                         NoOp
                       ELSE
                         CHOOSE x \in xs : x /= NoOp
    range == Max({ Len(l) : l \in ls})
  IN
    [i \in (1..range) |->
       combineSlot({l[i] : l \in { k \in ls : i <= Len(k) }})]

\* Insert x into log l at position i (which should be <= Len(l) + 1)
ReplaceItem(l, i, x) ==
  [ j \in 1..Max({Len(l), i}) |-> IF j = i THEN x ELSE l[j] ]

\* Subroutine to send an MGapCommit message
SendGapCommit(r) ==
  LET
    slot == Len(vLog[r]) + 1
  IN
  /\ Leader(vViewID[r]) = r
  /\ vReplicaStatus[r]  = StNormal
  /\ vReplicaStatus'    = [ vReplicaStatus EXCEPT ![r] = StGapCommit ]
  /\ vGapCommitReps'    = [ vGapCommitReps   EXCEPT ![r] = {} ]
  /\ vCurrentGapSlot'   = [ vCurrentGapSlot EXCEPT ![r] = slot ]
  /\ Send({[ mtype      |-> MGapCommit,
             dest       |-> d,
             slotNumber |-> slot,
             viewID     |-> vViewID[r] ] : d \in Replicas})
  /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum,
                  vLastNormView, vViewChanges, vSyncPoint,
                  vTentativeSync, vSyncReps >>

--------------------------------------------------------------------------------
(* `^\textbf{\large Main Spec}^' *)

Quorums == {R \in SUBSET(Replicas) : Cardinality(R) * 2 > Cardinality(Replicas)}

(*
  A request is committed if a quorum sent replies with matching view-id and
  log-slot-num, where one of the replies is from the leader. The following
  predicate is true iff value v is committed in slot i.

  `~TODO: add temporal formula stating Committed implies always Committed
    (this is obvious, though, because nothing gets taken out of messages).~'
*)
Committed(v, i) ==
  \E M \in SUBSET ({m \in messages : /\ m.mtype = MRequestReply
                                     /\ m.logSlotNum = i
                                     /\ m.request = v }) :
    \* Sent from a quorum
    /\ { m.sender : m \in M } \in Quorums
    \* Matching view-id
    /\ \E m1 \in M : \A m2 \in M : m1.viewID = m2.viewID
    \* One from the leader
    /\ \E m \in M : m.sender = Leader(m.viewID)

(*
  We only provide the ordering layer here. This is an easier guarantee to
  provide than saying the execution is equivalent to a linear one. We don't
  currently model execution, and that's a much harder predicate to compute.
*)
Linearizability ==
  LET
    maxLogPosition == Max({1} \cup
      { m.logSlotNum : m \in {m \in messages : m.mtype = MRequestReply } })
  IN ~(\E v1, v2 \in Values \cup { NoOp } :
         /\ v1 /= v2
         /\ \E i \in (1 .. maxLogPosition) :
           /\ Committed(v1, i)
           /\ Committed(v2, i)
      )

SyncSafety == \A r \in Replicas :
              \A i \in 1..vSyncPoint[r] :
              Committed(vLog[r][i], i)

--------------------------------------------------------------------------------
(* `^\textbf{\large Message Handlers and Actions}^' *)

\* `^\textbf{Client action}^'
\* Send a request for value v
ClientSendsRequest(v) == /\ Send({[ mtype |-> MClientRequest,
                                    value |-> v ]})
                         /\ UNCHANGED << sequencerVars, replicaVars >>

\* `^\textbf{Normal Case Handlers}^'
\* Sequencer s receives MClientRequest, m
HandleClientRequest(m, s) ==
  LET
    smn == seqMsgNums[s]
  IN
  /\ Send({[ mtype      |-> MMarkedClientRequest,
             dest       |-> r,
             value      |-> m.value,
             sessNum    |-> s,
             sessMsgNum |-> smn ] : r \in Replicas})
  /\ seqMsgNums' = [ seqMsgNums EXCEPT ![s] = smn + 1 ]
  /\ UNCHANGED replicaVars

\* Replica r receives MMarkedClientRequest, m
HandleMarkedClientRequest(r, m) ==
  /\ vReplicaStatus[r] = StNormal
     \* Normal case
  /\ \/ /\ m.sessNum       = vViewID[r].sessNum
        /\ m.sessMsgNum    = vSessMsgNum[r]
        /\ vLog'           = [ vLog EXCEPT ![r] = Append(vLog[r], m.value) ]
        /\ vSessMsgNum'    = [ vSessMsgNum EXCEPT ![r] = vSessMsgNum[r] + 1 ]
        /\ Send({[ mtype      |-> MRequestReply,
                   request    |-> m.value,
                   viewID     |-> vViewID[r],
                   logSlotNum |-> Len(vLog'[r]),
                   sender     |-> r ]})
        /\ UNCHANGED << sequencerVars,
                        vViewID, vLastNormView, vCurrentGapSlot, vGapCommitReps,
                        vViewChanges, vReplicaStatus, vSyncPoint,
                        vTentativeSync, vSyncReps >>
     \* SESSION-TERMINATED Case
     \/ /\ m.sessNum > vViewID[r].sessNum
        /\ LET
             newViewID == [ sessNum   |-> m.sessNum,
                            leaderNum |-> vViewID[r].leaderNum ]
           IN
           /\ Send({[ mtype  |-> MViewChangeReq,
                      dest   |-> d,
                      viewID |-> newViewID ] : d \in Replicas})
           /\ UNCHANGED << replicaVars, sequencerVars >>
     \* DROP-NOTIFICATION Case
     \/ /\ m.sessNum    = vViewID[r].sessNum
        /\ m.sessMsgNum > vSessMsgNum[r]
           \* If leader, commit a gap
        /\ \/ /\ r = Leader(vViewID[r])
              /\ SendGapCommit(r)
           \* Otherwise, ask the leader
           \/ /\ r /= Leader(vViewID[r])
              /\ Send({[ mtype      |-> MSlotLookup,
                         viewID     |-> vViewID[r],
                         dest       |-> Leader(vViewID[r]),
                         sender     |-> r,
                         sessMsgNum |-> vSessMsgNum[r] ]})
              /\ UNCHANGED << replicaVars, sequencerVars >>

\* `^\textbf{Gap Commit Handlers}^'
\* Replica r receives SlotLookup, m
HandleSlotLookup(r, m) ==
  LET
    logSlotNum == Len(vLog[r]) + 1 - (vSessMsgNum[r] - m.sessMsgNum)
  IN
  /\ m.viewID           = vViewID[r]
  /\ Leader(vViewID[r]) = r
  /\ vReplicaStatus[r] = StNormal
  /\ \/ /\ logSlotNum <= Len(vLog[r])
        /\ Send({[ mtype      |-> MMarkedClientRequest,
                   dest       |-> m.sender,
                   value      |-> vLog[r][logSlotNum],
                   sessNum    |-> vViewID[r].sessNum,
                   sessMsgNum |-> m.sessMsgNum ]})
        /\ UNCHANGED << replicaVars, sequencerVars >>
     \/ /\ logSlotNum = Len(vLog[r]) + 1
        /\ SendGapCommit(r)

\* Replica r receives GapCommit, m
HandleGapCommit(r, m) ==
  /\ m.viewID             = vViewID[r]
  /\ m.slotNumber         <= Len(vLog[r]) + 1
  /\ \/ vReplicaStatus[r] = StNormal
     \/ vReplicaStatus[r] = StGapCommit
  /\ vLog' = [ vLog EXCEPT ![r] = ReplaceItem(vLog[r], m.slotNumber, NoOp) ]
  \* Increment the msgNumber if necessary
  /\ IF m.slotNumber > Len(vLog[r]) THEN
       vSessMsgNum' = [ vSessMsgNum EXCEPT ![r] = vSessMsgNum[r] + 1 ]
     ELSE
       UNCHANGED vSessMsgNum
  /\ Send({[ mtype      |-> MGapCommitRep,
             dest       |-> Leader(vViewID[r]),
             sender     |-> r,
             slotNumber |-> m.slotNumber,
             viewID     |-> vViewID[r] ],
           [ mtype      |-> MRequestReply,
             request    |-> NoOp,
             viewID     |-> vViewID[r],
             logSlotNum |-> m.slotNumber,
             sender     |-> r ]})
  /\ UNCHANGED << sequencerVars, vGapCommitReps, vViewID, vCurrentGapSlot,
                  vReplicaStatus, vLastNormView, vViewChanges,
                  vSyncPoint, vTentativeSync, vSyncReps >>

\* Replica r receives GapCommitRep, m
HandleGapCommitRep(r, m) ==
  /\ vReplicaStatus[r]  = StGapCommit
  /\ m.viewID           = vViewID[r]
  /\ Leader(vViewID[r]) = r
  /\ m.slotNumber       = vCurrentGapSlot[r]
  /\ vGapCommitReps'    =
       [ vGapCommitReps EXCEPT ![r] = vGapCommitReps[r] \cup {m} ]
  \* When there's enough, resume StNormal and process more messages
  /\ LET isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
                             /\ \E n \in M : n.sender = r
         gCRs             == { n \in vGapCommitReps'[r] :
                                 /\ n.mtype      = MGapCommitRep
                                 /\ n.viewID     = vViewID[r]
                                 /\ n.slotNumber = vCurrentGapSlot[r] }
     IN
       IF isViewPromise(gCRs) THEN
         vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StNormal ]
       ELSE
         UNCHANGED vReplicaStatus
  /\ UNCHANGED << sequencerVars, networkVars, vLog, vViewID, vCurrentGapSlot,
                  vSessMsgNum, vLastNormView, vViewChanges, vSyncPoint,
                  vTentativeSync, vSyncReps >>

\* `^\textbf{Failure Cases}^'
\* Replica r starts a Leader change
StartLeaderChange(r) ==
  LET
    newViewID == [ sessNum   |-> vViewID[r].sessNum,
                   leaderNum |-> vViewID[r].leaderNum + 1 ]
  IN
  /\ Send({[ mtype  |-> MViewChangeReq,
             dest   |-> d,
             viewID |-> newViewID ] : d \in Replicas})
  /\ UNCHANGED << replicaVars, sequencerVars >>

\* `^\textbf{View Change Handlers}^'
\* Replica r gets MViewChangeReq, m
HandleViewChangeReq(r, m) ==
  LET
    currentViewID == vViewID[r]
    newSessNum    == Max({currentViewID.sessNum, m.viewID.sessNum})
    newLeaderNum  == Max({currentViewID.leaderNum, m.viewID.leaderNum})
    newViewID     == [ sessNum |-> newSessNum, leaderNum |-> newLeaderNum ]
  IN
  /\ currentViewID   /= newViewID
  /\ vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StViewChange ]
  /\ vViewID'        = [ vViewID EXCEPT ![r] = newViewID ]
  /\ vViewChanges'   = [ vViewChanges EXCEPT ![r] = {} ]
  /\ Send({[ mtype      |-> MViewChange,
             dest       |-> Leader(newViewID),
             sender     |-> r,
             viewID     |-> newViewID,
             lastNormal |-> vLastNormView[r],
             sessMsgNum |-> vSessMsgNum[r],
             log        |-> vLog[r] ]} \cup
           \* Send the MViewChangeReqs in case this is an entirely new view
           {[ mtype  |-> MViewChangeReq,
              dest   |-> d,
              viewID |-> newViewID ] : d \in Replicas})
  /\ UNCHANGED << vCurrentGapSlot, vGapCommitReps, vLog, vSessMsgNum,
                  vLastNormView, sequencerVars, vSyncPoint,
                  vTentativeSync, vSyncReps >>

\* Replica r receives MViewChange, m
HandleViewChange(r, m) ==
  \* Add the message to the log
  /\ vViewID[r]         = m.viewID
  /\ vReplicaStatus[r]  = StViewChange
  /\ Leader(vViewID[r]) = r
  /\ vViewChanges' =
     [ vViewChanges EXCEPT ![r] = vViewChanges[r] \cup {m}]
  \* If there's enough, start the new view
  /\ LET
       isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
                           /\ \E n \in M : n.sender = r
       vCMs             == { n \in vViewChanges'[r] :
                               /\ n.mtype  = MViewChange
                               /\ n.viewID = vViewID[r] }
       \* Create the state for the new view
       normalViews == { n.lastNormal : n \in vCMs }
       lastNormal  == (CHOOSE v \in normalViews : \A v2 \in normalViews :
                         ViewLe(v2, v))
       goodLogs    == { n.log : n \in
                          { o \in vCMs : o.lastNormal = lastNormal } }
       \* If updating seqNum, revert sessMsgNum to 0; otherwise use latest
       newMsgNum   ==
         IF lastNormal.sessNum = vViewID[r].sessNum THEN
            Max({ n.sessMsgNum : n \in
                    { o \in vCMs : o.lastNormal = lastNormal } })
         ELSE
           0
     IN
       IF isViewPromise(vCMs) THEN
         Send({[ mtype      |-> MStartView,
                 dest       |-> d,
                 viewID     |-> vViewID[r],
                 log        |-> CombineLogs(goodLogs),
                 sessMsgNum |-> newMsgNum ] : d \in Replicas })
       ELSE
         UNCHANGED networkVars
  /\ UNCHANGED << vReplicaStatus, vViewID, vLog, vSessMsgNum, vCurrentGapSlot,
                  vGapCommitReps, vLastNormView, sequencerVars, vSyncPoint,
                  vTentativeSync, vSyncReps >>

\* Replica r receives a MStartView, m
HandleStartView(r, m) ==
  (*
    Note how I handle this. There was actually a bug in prose description in the
    paper where the following guard was underspecified.
  *)
  /\ \/ ViewLt(vViewID[r], m.viewID)
     \/ vViewID[r]   = m.viewID /\ vReplicaStatus[r] = StViewChange
  /\ vLog'           = [ vLog EXCEPT ![r] = m.log ]
  /\ vSessMsgNum'    = [ vSessMsgNum EXCEPT ![r] = m.sessMsgNum ]
  /\ vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StNormal ]
  /\ vViewID'        = [ vViewID EXCEPT ![r] = m.viewID ]
  /\ vLastNormView'  = [ vLastNormView EXCEPT ![r] = m.viewID ]
  \* Send replies (in the new view) for all log items
  /\ Send({[ mtype      |-> MRequestReply,
             request    |-> m.log[i],
             viewID     |-> m.viewID,
             logSlotNum |-> i,
             sender     |-> r ] : i \in (1..Len(m.log))})
  /\ UNCHANGED << sequencerVars,
                  vViewChanges, vCurrentGapSlot, vGapCommitReps, vSyncPoint,
                  vTentativeSync, vSyncReps >>

\* `^\textbf{Synchronization handlers}^'
\* Leader replica r starts synchronization
StartSync(r) ==
  /\ Leader(vViewID[r]) = r
  /\ vReplicaStatus[r]  = StNormal
  /\ vSyncReps'         = [ vSyncReps EXCEPT ![r] = {} ]
  /\ vTentativeSync'    = [ vTentativeSync EXCEPT ![r] = Len(vLog[r]) ]
  /\ Send({[ mtype      |-> MSyncPrepare,
             sender     |-> r,
             dest       |-> d,
             viewID     |-> vViewID[r],
             sessMsgNum |-> vSessMsgNum[r],
             log        |-> vLog[r] ] : d \in Replicas })
  /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum, vLastNormView,
                  vCurrentGapSlot, vViewChanges, vReplicaStatus,
                  vGapCommitReps, vSyncPoint >>

\* Replica r receives MSyncPrepare, m
HandleSyncPrepare(r, m) ==
  LET
    newLog    == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
    newMsgNum == vSessMsgNum[r] + (Len(newLog) - Len(vLog[r]))
  IN
  /\ vReplicaStatus[r] = StNormal
  /\ m.viewID          = vViewID[r]
  /\ m.sender          = Leader(vViewID[r])
  /\ vLog'             = [ vLog EXCEPT ![r] = newLog ]
  /\ vSessMsgNum'      = [ vSessMsgNum EXCEPT ![r] = newMsgNum ]
  /\ Send({[ mtype         |-> MSyncRep,
             sender        |-> r,
             dest          |-> m.sender,
             viewID        |-> vViewID[r],
             logSlotNumber |-> Len(m.log) ]} \cup
          {[ mtype      |-> MRequestReply,
             request    |-> vLog'[r][i],
             viewID     |-> vViewID[r],
             logSlotNum |-> i,
             sender     |-> r ] : i \in 1..Len(vLog'[r])})
  /\ UNCHANGED << sequencerVars, vViewID, vLastNormView, vCurrentGapSlot,
                  vViewChanges, vReplicaStatus, vGapCommitReps,
                  vSyncPoint, vTentativeSync, vSyncReps >>

\* Replica r receives MSyncRep, m
HandleSyncRep(r, m) ==
  /\ m.viewID          = vViewID[r]
  /\ vReplicaStatus[r] = StNormal
  /\ vSyncReps'        = [ vSyncReps EXCEPT ![r] = vSyncReps[r] \cup { m } ]
  /\ LET isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
                             /\ \E n \in M : n.sender = r
         sRMs             == { n \in vSyncReps'[r] :
                                 /\ n.mtype         = MSyncRep
                                 /\ n.viewID        = vViewID[r]
                                 /\ n.logSlotNumber = vTentativeSync[r] }
         committedLog     == IF vTentativeSync[r] >= 1 THEN
                               SubSeq(vLog[r], 1, vTentativeSync[r])
                             ELSE
                               << >>
     IN
       IF isViewPromise(sRMs) THEN
         Send({[ mtype         |-> MSyncCommit,
                 sender        |-> r,
                 dest          |-> d,
                 viewID        |-> vViewID[r],
                 log           |-> committedLog,
                 sessMsgNum    |-> vSessMsgNum[r] -
                                   (Len(vLog[r]) - Len(committedLog)) ] :
              d \in Replicas })
       ELSE
         UNCHANGED networkVars
  /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum, vLastNormView,
                  vCurrentGapSlot, vViewChanges, vReplicaStatus,
                  vGapCommitReps, vSyncPoint, vTentativeSync >>

\* Replica r receives MSyncCommit, m
HandleSyncCommit(r, m) ==
  LET
    newLog    == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
    newMsgNum == vSessMsgNum[r] + (Len(newLog) - Len(vLog[r]))
  IN
  /\ vReplicaStatus[r] = StNormal
  /\ m.viewID          = vViewID[r]
  /\ m.sender          = Leader(vViewID[r])
  /\ vLog'             = [ vLog EXCEPT ![r] = newLog ]
  /\ vSessMsgNum'      = [ vSessMsgNum EXCEPT ![r] = newMsgNum ]
  /\ vSyncPoint'       = [ vSyncPoint EXCEPT ![r] = Len(m.log) ]
  /\ UNCHANGED << sequencerVars, networkVars, vViewID, vLastNormView,
                  vCurrentGapSlot, vViewChanges, vReplicaStatus,
                  vGapCommitReps, vTentativeSync, vSyncReps >>
--------------------------------------------------------------------------------
(* `^\textbf{\large Main Transition Function}^' *)

Next == \* Handle Messages
        \/ \E m \in messages :
           \E s \in Sequencers
                             : /\ m.mtype = MClientRequest
                               /\ HandleClientRequest(m, s)
        \/ \E m \in messages : /\ m.mtype = MMarkedClientRequest
                               /\ HandleMarkedClientRequest(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MViewChangeReq
                               /\ HandleViewChangeReq(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MViewChange
                               /\ HandleViewChange(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MStartView
                               /\ HandleStartView(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MSlotLookup
                               /\ HandleSlotLookup(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MGapCommit
                               /\ HandleGapCommit(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MGapCommitRep
                               /\ HandleGapCommitRep(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MSyncPrepare
                               /\ HandleSyncPrepare(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MSyncRep
                               /\ HandleSyncRep(m.dest, m)
        \/ \E m \in messages : /\ m.mtype = MSyncCommit
                               /\ HandleSyncCommit(m.dest, m)
        \* Client Actions
        \/ \E v \in Values : ClientSendsRequest(v)
        \* Start synchronization
        \/ \E r \in Replicas : StartSync(r)
        \* Failure case
        \/ \E r \in Replicas : StartLeaderChange(r)

================================================================================
