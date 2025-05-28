-------------------------- MODULE raft_0240655845 --------------------------


EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server    \* All entities: e.g., {r1, r2, r3, r4}
CONSTANTS Value     \* e.g., {"v1", "v2"}
CONSTANTS Follower, Candidate, Leader, Switch \* States
CONSTANTS Nil


CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse, RecoveryRequest

CONSTANTS MaxClientRequests
CONSTANTS MaxBecomeLeader
CONSTANTS MaxTerm


VARIABLE messages
VARIABLE switchBuffer
VARIABLE unorderedRequests
VARIABLE switchSentRecord
VARIABLE leaderCount
VARIABLE maxc
VARIABLE entryCommitStats
VARIABLE switchIndex
VARIABLE Servers

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

VARIABLE log
VARIABLE commitIndex
logVars == <<log, commitIndex>>

VARIABLE votesResponded
VARIABLE votesGranted
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

VARIABLE nextIndex
VARIABLE matchIndex

leaderVars == <<nextIndex, matchIndex>>

hovercraftVars == <<switchBuffer, switchIndex, unorderedRequests, switchSentRecord>>

vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>


Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ] \* Allow up to 2 copies for some models
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)
Reply(response, request) == messages' = WithoutMessage(request, WithMessage(response, messages))

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y
min(a, b) == IF a < b THEN a ELSE b

ValidMessage(msgs) == { m \in DOMAIN messages : msgs[m] > 0 }

CommittedTermPrefix(i, x) ==
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
      LET maxTermIndex == CHOOSE y \in DOMAIN log[i] :
                              /\ log[i][y].term <= x
                              /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    ELSE << >>

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A k \in 1..Len(seq1) : seq1[k] = seq2[k]

Committed(i) ==
    IF commitIndex[i] = 0
    THEN << >>
    ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Servers: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests )
                /\ (\A m \in DOMAIN messages: messages[m] <= 1) \* Ensure at most 1 copy of message

Symmetry == Permutations(Servers)


InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower] \* All start as Follower, even Switch
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ]
        /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> "", payload |-> ""] ]
        /\ unorderedRequests = [ s \in Server |-> {} ]
        /\ switchSentRecord = [ s \in Server |-> {} ]

MyInit == \* For MySwitchSpec: Starts with a known leader and switch
        LET ServerIds == CHOOSE ids \in [1..4 -> Server] :
                        \A i, j \in 1..4 : i # j => ids[i] # ids[j]
        r1 == ServerIds[1]
        r2 == ServerIds[2]
        r3 == ServerIds[3]
        r4 == ServerIds[4]
        IN
        /\ switchIndex = r1
        /\ Servers = Server \ {r1}
        /\ commitIndex = [s \in Server |-> 0]
        /\ currentTerm = [s \in Server |-> 2]
        /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
        /\ log = [s \in Server |-> <<>>]
        /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
        /\ maxc = 0
        /\ messages = [m \in {} |-> 0]  \* Start with empty messages
        /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
        /\ state = [s \in Server |->
                  CASE s = switchIndex -> Switch
                  [] s = r2 -> Leader
                  [] OTHER  -> Follower]
        /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
        /\ voterLog = [s \in Server |-> IF s = r2 THEN (r3 :> <<>> @@ r4 :> <<>>) ELSE <<>>]
        /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r3, r4} ELSE {}]
        /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r3, r4} ELSE {}]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize here too
        /\ switchSentRecord = [s \in Server |-> {} ]
        /\ unorderedRequests = [s \in Server |-> {} ]
        /\ switchBuffer = [i \in {} |-> [term: Nat, value: STRING, payload: STRING]]


----
\* Define state transitions

Restart(i) ==
    /\ state[i] = Leader
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [k \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [k \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, hovercraftVars, Servers>>

Timeout(i) ==
    /\ state[i] \in {Follower}
    /\ currentTerm[i] < MaxTerm
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET entryIndex == nextIndex[i][j]
           logEntryFromLeader == log[i][entryIndex]  \* This is already metadata [term, value]
           entries == << [term |-> logEntryFromLeader.term, value |-> logEntryFromLeader.value] >>      \* Send this METADATA
           entryKey == <<entryIndex, logEntryFromLeader.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,      \* Contains METADATA only
\*                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, log, commitIndex, maxc, leaderCount, hovercraftVars, Servers>>

BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [k \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, hovercraftVars, Servers>>

SwitchClientRequest(ldr, v) ==
    /\ state[ldr] = Leader
    /\ v \in Value
    /\ maxc < MaxClientRequests
    /\ v \notin DOMAIN switchBuffer
    /\ LET leaderTerm == currentTerm[ldr]
           entry == [term    |-> leaderTerm,
                     value   |-> v,
                     payload |-> v]
           entryExists == \E r \in DOMAIN switchBuffer: entry = switchBuffer[r]
       IN IF ~entryExists THEN
            /\ maxc' = maxc + 1
            /\ switchBuffer' = switchBuffer @@ (v :> entry)
          ELSE UNCHANGED <<maxc, switchBuffer>>
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, leaderCount, entryCommitStats, switchIndex, switchSentRecord, unorderedRequests, Servers>>


SwitchClientRequestReplicate(i, val) ==
    \* Send only to leader the others will have to recover the request when they receive an append entry.
    \* This is only needed to test the recovery mechanism. It should be uncommented when needed
    /\ state[i] = Leader 
    /\ \E r \in DOMAIN switchBuffer: r = val \* Check if v is a valid switch request
    /\ ~(\E entry \in switchSentRecord[i]: entry = <<switchBuffer[val].value, switchBuffer[val].term>>) \* Check that this entry hasn't been sent to server i yet
    /\ switchSentRecord' = [switchSentRecord EXCEPT ![i] = switchSentRecord[i] \cup {<<switchBuffer[val].value, switchBuffer[val].term>>} ]
    /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = unorderedRequests[i] \cup {switchBuffer[val].value} ]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchIndex, switchBuffer, Servers>> 

LeaderIngestHovercRaftRequest(ldr, val) ==
    /\ ldr \in Servers
    /\ state[ldr] = Leader
    /\ \E j \in DOMAIN switchBuffer: val = j      \* The leader must know of this value from the switchBuffer
    /\ \E j \in unorderedRequests[ldr] : val = j   \* Leader must also have it in its own buffer (as per stricter design)
    /\ ~(\E j \in DOMAIN log[ldr] : log[ldr][j] = switchBuffer[val])
    /\ LET entryTerm == switchBuffer[val].term
           entry == switchBuffer[val]
           newLog == Append(log[ldr], entry)
           newEntryIndex == Len(log[ldr]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![ldr] = newLog]
        /\ unorderedRequests' = [unorderedRequests EXCEPT ![ldr] = @ \ {val}]
        /\ entryCommitStats' =
              IF newEntryIndex > 0
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount, maxc, switchBuffer, switchIndex, switchSentRecord, Servers>>


AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET
           Agree(index) == {i} \cup {k \in Servers :
                                         matchIndex[i][k] >= index}
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record 
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, hovercraftVars, Servers>>

    
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ i \in Servers
       /\ j \in Servers
       /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

HandleRequestVoteResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, unorderedRequests>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, unorderedRequests>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
\*                       /\ commitIndex' = [commitIndex EXCEPT ![i] = @ + 1]     
\*                       /\ commitIndex' = [commitIndex EXCEPT ![i] = 
\*                                            IF commitIndex[i] < m.mcommitIndex THEN 
\*                                                Min({m.mcommitIndex, Len(log[i])}) 
\*                                            ELSE 
\*                                                commitIndex[i]]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>
                   \/ \* conflict: remove 1 entry (simplified from original spec - assumes entry length 1)
                      \* since we do not send empty entries, we have to provide a larger set of values to ensure some progress
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1) \* Truncate log
                          IN log' = [log EXCEPT ![i] = newLog]
\*                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
\*                                          log[i][index2]]
\*                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, unorderedRequests>>
                       

                   \/ \* no conflict but server i can't find request in its unorder requests list. Send recovery message to Server j
                       /\ m.mentries /= << >>
                       \* request not found in servers unordered request list
                       /\ ~(\E k \in unorderedRequests[i]: k = m.mentries[1].value)                      
                       /\ LET message == [mtype     |-> RecoveryRequest,
                                          mterm          |-> currentTerm[i],
                                          mentries       |-> m.mentries,
                                          msource         |-> i,
                                          mdest           |-> j]
                          IN Send(message)
                          \* Do not discard the append entries request
                       /\ UNCHANGED <<serverVars, commitIndex, log, unorderedRequests>>
                       
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ \E k \in unorderedRequests[i]: k = m.mentries[1].value
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entryId == CHOOSE id \in DOMAIN switchBuffer: switchBuffer[id].term = m.mentries[1].term /\ switchBuffer[id].value = m.mentries[1].value 
                              entry == switchBuffer[entryId]
                          IN /\ log' = [log EXCEPT ![i] = Append(log[i], entry)] \* Add this entry to log, this includes the payload
                             /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \ {m.mentries[1].value}]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchBuffer, switchIndex, switchSentRecord, Servers>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET \*newMatchIndex == IF matchIndex[i][j] > m.mmatchIndex THEN matchIndex[i][j] ELSE m.mmatchIndex
                 newMatchIndex == m.mmatchIndex
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN
                /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats                     
       \/ /\ \lnot m.msuccess
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, hovercraftVars, Servers>>

\* Server i receives RecoveryRequest message from server j
HandleRecoveryRequest(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ m.mtype = RecoveryRequest
    /\ m.mentries /= << >>
    /\ \E entry \in DOMAIN switchBuffer: entry = m.mentries[1].value \* Check that this entry has been received by switch
    /\ Discard(m) \* Discard the recovery request
    \* Do not send new append entries request since the previous one wasn't deleted
    /\ unorderedRequests' = [unorderedRequests EXCEPT ![j] = unorderedRequests[j] \cup {switchBuffer[m.mentries[1].value].value} ] \* Snoop the value request from switchBuffer

    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchBuffer, switchIndex, switchSentRecord, Servers>>


UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>


Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN /\ i \in Servers
       /\ ( \/ UpdateTerm(i, j, m)
            \/ /\ m.mtype = RequestVoteRequest
               /\ HandleRequestVoteRequest(i, j, m)
            \/ /\ m.mtype = RequestVoteResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleRequestVoteResponse(i, j, m)
            \/ /\ m.mtype = AppendEntriesRequest
               /\ HandleAppendEntriesRequest(i, j, m)
            \/ /\ m.mtype = AppendEntriesResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleAppendEntriesResponse(i, j, m)
            \/ /\ m.mtype = RecoveryRequest
               /\ HandleRecoveryRequest(i, j, m)
          )

Next ==
       \/ \E srv \in Servers : Timeout(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ RequestVote(srv1, srv2)
       \/ \E srv \in Servers : BecomeLeader(srv)
\*       \/ \E ldr \in Servers, v \in Value :
\*           state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)
\*       \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer :
\*           SwitchClientRequestReplicate(switchIndex, raftSrv, v)
       \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :
           state[ldr] = Leader /\ LeaderIngestHovercRaftRequest(ldr, v)
       \/ \E srv \in Servers : AdvanceCommitIndex(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ AppendEntries(srv1, srv2)
       \/ \E m \in {msg \in ValidMessage(messages) :
                msg.mdest \in Servers /\
                msg.mtype \in {RequestVoteRequest, RequestVoteResponse,
                               AppendEntriesRequest, AppendEntriesResponse}} :
           Receive(m)

MySwitchNext == 
       \/ \E v \in Value, ldr \in Servers: state[ldr] = Leader /\ SwitchClientRequest(ldr, v)
           
       \/ \E v \in DOMAIN switchBuffer, s \in Servers: SwitchClientRequestReplicate(s, v) 
       
       \/ \E ldr \in Servers, v \in DOMAIN switchBuffer: state[ldr] = Leader  /\ LeaderIngestHovercRaftRequest(ldr, v)
             
       \/ \E i \in Servers: AdvanceCommitIndex(i)
       
       \/ \E i,j \in Servers: i /= j  /\ AppendEntries(i, j)
       
       \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse, RecoveryRequest}} : Receive(m)
                

Spec == Init /\ [][Next]_vars

MySpec == MyInit /\ [][MySwitchNext]_vars

\* -------------------- Invariants --------------------
AllServersHaveOneUnorderedRequestInv ==
    \E s \in Servers : Cardinality(unorderedRequests[s]) /= Cardinality(Value)

NoRaftServerHasCommittedYet ==
    \A srv \in Servers : commitIndex[srv] = 0

MoreThanOneLeaderInv ==
    \A i,j \in Servers :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

LogMatchingInv ==
    \A i, j \in Servers : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

LeaderCompletenessInv ==
    \A i \in Servers :
        state[i] = Leader =>
        \A j \in Servers : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])

LogInv ==
    \A i, j \in Servers :
        \/ CheckIsPrefix(Committed(i),Committed(j))
        \/ CheckIsPrefix(Committed(j),Committed(i))

THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv)


MaxCInv == (\E i \in Servers : state[i] = Leader) => maxc <= MaxClientRequests

LeaderCountInv == \A i \in Servers : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

MaxTermInv == \A i \in Servers : currentTerm[i] <= MaxTerm

EntryCommitMessageCountInv ==
    LET NumRaftServers == Cardinality(Servers)
        NumFollowers == IF NumRaftServers > 0 THEN NumRaftServers - 1 ELSE 0
        MinFollowersForMajority == IF NumRaftServers > 0 THEN NumRaftServers \div 2 ELSE 0
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers)
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

EntryCommitAckQuorumInv ==
    LET NumRaftServers == Cardinality(Servers)
        MinFollowerAcksForMajority == IF NumRaftServers > 0 THEN NumRaftServers \div 2 ELSE 0
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

LeaderCommitted ==
    \E i \in Servers : commitIndex[i] /= 1

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4
----

\* MV CONSTANT definitions Value
const_174842341360368000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_174842341360369000 == 
{r1, r2, r3, r4}
----

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174842341360370000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_174842341360371000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:14MaxClientRequests
const_174842341360372000 == 
5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174842341360373000 ==
MyConstraint
----

=============================================================================