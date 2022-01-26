------------------------- MODULE TestImpReplication -------------------------


EXTENDS Naturals,Sequences,TLC


CONSTANT UNDEF,Term,Server,Quorums,Seqs,Value,Votes

min(x,y) == IF x < y
            THEN x
            ELSE y
            
max(x,y) == IF x > y
            THEN x
            ELSE y        
            
            
VARIABLES log,
          accepted

replicationVars == <<accepted,log>>            
                             
VARIABLES leaderLog, (* a history variable, log of leaders *)
          leader (* a history variable, leader[t] is the leader of term t *)

leaderVars == <<leaderLog,leader>>                             
                                                          
VARIABLES preVoteSet,
          preVoteTerm,
          voteCnt
preVoteVars == <<preVoteSet,preVoteTerm,voteCnt>>

VARIABLES voteTerm,
          voteSet
voteVars == <<voteTerm,voteSet>>


                             
VARIABLES state,currentTerm,votedFor,updateRec

stateVars == <<state,currentTerm,votedFor,updateRec>>

VARIABLES e1,e2,e3,e4,e5


VARIABLES voteSeq,ackedVoteSeq
eleSeqVars == <<voteSeq,ackedVoteSeq>>

VARIABLE net

VARIABLES nextIndex,
          matchIndex,
          commitIndex
              
indexVars == <<nextIndex,commitIndex,matchIndex>>     


Entries == [term : Term, index : Seqs, value : Value, leaderTerm : Term]

vars == <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
            updateRec,net,eleSeqVars,indexVars,
            e1,e2,e3,e4,e5>>


Send(n,m) == n' = n \cup {m}




CompareImp(l,t,i) ==  \/ Len(l) = 0
                      \/ /\ i # 0
                         /\ Len(l) > 0
                         /\ \/ t > l[Len(l)].term
                            \/ /\ t = l[Len(l)].term
                               /\ i >= Len(l) 


Compare(l1,l2) == \/ Len(l2) = 0
                  \/ /\ Len(l1) # 0
                     /\ Len(l2) # 0
                     /\ \/ l1[Len(l1)].term > l2[Len(l2)].term
                        \/ /\ l1[Len(l1)].term = l2[Len(l2)].term
                           /\ Len(l1) >= Len(l2)

(* s2为s1投票 *)

CompareLog(s1,s2) == Compare(log[s1],log[s2])

PreVote(s) == /\ state[s] = "FOLLOWER"
              /\ state' = [state EXCEPT ![s] = "PRE_CANDIDATE"]
              /\ voteSeq' = [voteSeq EXCEPT ![s] = @ +1]
              /\ currentTerm[s] + 1 \in Term
              /\ voteCnt + 1 \in Votes
              /\ voteCnt' = voteCnt + 1
              /\ preVoteTerm' = preVoteTerm \cup {currentTerm[s]}
              /\ preVoteSet' = [preVoteSet EXCEPT ![s] = 
                                      {a \in Server : 
                                             /\ currentTerm[a] <= currentTerm[s]
                                             /\ CompareLog(s,a)}]
              /\ ~(\E m \in net : /\ m.mtype = "PreVoteRequest"
                                  /\ m.msrc = s
                                  /\ m.mterm = currentTerm[s])
              /\ Send(net,[mtype |-> "PreVoteRequest",
                           mterm |-> currentTerm[s],
                           msrc |-> s,
                           mvoteTerm |-> currentTerm[s]+1,
                           mvoteSeq |-> voteSeq'[s],
                           mlogIndex |-> Len(log[s]),
                           mlogTerm |-> IF Len(log[s]) = 0 THEN 0 ELSE log[s][Len(log[s])].term])
              /\ UNCHANGED <<currentTerm,votedFor,ackedVoteSeq,voteVars,updateRec,
                         e1,e2,e3,e4,e5,replicationVars,leaderVars,indexVars>>


HandlePreVoteUpdateTerm(s) == /\ \E m \in net :
                                  /\ m.mtype = "PreVoteRequest"
                                  /\ m.mvoteSeq > ackedVoteSeq[s][m.msrc]
                                  /\ ackedVoteSeq' = [ackedVoteSeq EXCEPT ![s][m.msrc] = m.mvoteSeq]
                                  /\ m.mterm > currentTerm[s]
                                  /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                  /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                                  /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                                  /\ LET granted == CompareImp(log[s],m.mlogTerm,m.mlogIndex)
                                     IN
                                        Send(net,[mtype |-> "PreVoteResponse",
                                                  mterm |-> currentTerm'[s],
                                                  msrc |-> s,
                                                  mdest |-> m.msrc,
                                                  mvoteSeq |-> m.mvoteSeq,
                                                  mgranted |-> granted])
                              /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                              voteSeq,indexVars,
                                                e1,e2,e3,e4,e5>>

HandlePreVote(s) == /\ \E m \in net :
                       /\ m.mtype = "PreVoteRequest"
                       /\ m.mvoteSeq > ackedVoteSeq[s][m.msrc]
                       /\ ackedVoteSeq' = [ackedVoteSeq EXCEPT ![s][m.msrc] = m.mvoteSeq]
                       /\ m.mterm = currentTerm[s]
                       /\ LET granted ==  CompareImp(log[s],m.mlogTerm,m.mlogIndex)
                          IN
                              Send(net,[mtype |-> "PreVoteResponse",
                                        mterm |-> currentTerm[s],
                                        msrc |-> s,
                                        mdest |-> m.msrc,
                                        mvoteSeq |-> m.mvoteSeq,
                                        mgranted |-> granted])    
                   /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                    voteSeq,indexVars,
                                    e1,e2,e3,e4,e5>>    


HandlePreVoteRefuseLowTerm(s) == /\ \E m \in net :
                                    /\ m.mtype = "PreVoteRequest"
                                    /\ m.mvoteSeq > ackedVoteSeq[s][m.msrc]
                                    /\ ackedVoteSeq' = [ackedVoteSeq EXCEPT ![s][m.msrc] = m.mvoteSeq]
                                    /\ m.mterm < currentTerm[s]
                                    /\ Send(net,[mtype |-> "PreVoteResponse",
                                                 mterm |-> currentTerm[s],
                                                 msrc |-> s,
                                                 mdest |-> m.msrc,
                                                 mvoteSeq |-> m.mvoteSeq,
                                                 mgranted |-> FALSE])
                                 /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                                    voteSeq,indexVars,
                                                    e1,e2,e3,e4,e5>>


           
PreVoteBecomeFollower(s) == /\ \E m \in net :
                               /\ m.mtype = "PreVoteResponse"
                               /\ m.mdest = s
                               /\ m.mterm > currentTerm[s]
                               /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                               /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                               /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                               /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                             /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                               net,eleSeqVars,indexVars,
                                               e1,e2,e3,e4,e5>> 
           
BecomeCandidate(s) == /\ state[s] = "PRE_CANDIDATE"
                      /\ \E Q \in Quorums:
                          \A q \in Q : \E m \in net :
                                    /\ m.mtype = "PreVoteResponse"
                                    /\ m.mterm = currentTerm[s]
                                    /\ m.mvoteSeq = voteSeq[s]
                                    /\ m.mdest = s
                                    /\ m.msrc = q
                                    /\ m.mgranted = TRUE
                      /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
                      /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
                      /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                      /\ voteTerm' = voteTerm \cup {currentTerm'[s]}
                      /\ updateRec' = [updateRec EXCEPT ![currentTerm'[s]] = @ \cup {s}]
                      /\ voteSet' = [voteSet EXCEPT ![s] = {a \in Server :
                                                                /\ currentTerm[a] <= currentTerm'[s]
                                                                /\ CompareLog(s,a)}]
                      /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,
                                               net,eleSeqVars,indexVars,
                                               e1,e2,e3,e4,e5>> 
                     
                     

RequestVote(s) == /\ state[s] = "CANDIDATE"
                  /\ ~ (\E m \in net : /\ m.mtype = "RequestVote"
                                          /\ m.msrc = s
                                          /\ m.mterm = currentTerm[s])
                  /\ Send(net,
                          [mtype |-> "RequestVote",
                           mterm |-> currentTerm[s],
                           mlastIndex |-> Len(log[s]),
                           mlastTerm |-> IF Len(log[s]) = 0 THEN 0 ELSE log[s][Len(log[s])].term,
                           msrc |-> s])
                  /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                     eleSeqVars,indexVars,e1,e2,e3,e4,e5>>                   
                     
                     
MakeVoteFailLowTerm(s) == /\ \E m \in net :
                                 /\ m.mtype = "RequestVote"
                                 /\ m.mterm < currentTerm[s]
                                 /\ ~ (\E mm \in net : /\ mm.mtype = "RequestVoteResponse"
                                                       /\ mm.mterm = currentTerm[s]
                                                       /\ mm.msrc = s
                                                       /\ mm.mdest = m.msrc)
                                 /\ Send(net,
                                           [mtype |-> "RequestVoteResponse",
                                            mterm |-> currentTerm[s],
                                            mgranted |-> FALSE,
                                            msrc |-> s,
                                            mdest |-> m.msrc])
                          /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                           eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 


MakeVoteUpdateTerm(s) == /\ \E m \in net :
                                /\ m.mtype = "RequestVote"
                                /\ m.mterm > currentTerm[s]
                                /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]                     
                                /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                /\ updateRec' = [updateRec EXCEPT ![currentTerm'[s]] = @ \cup {s}]
                                /\ LET granted == CompareImp(log[s],m.mlastTerm,m.mlastIndex)
                                   IN
                                       /\ votedFor' = [votedFor EXCEPT ![s] = IF granted THEN m.msrc
                                                                              ELSE UNDEF]
                                       /\ Send(net,[mtype |-> "RequestVoteResponse",
                                                    mterm |-> currentTerm'[s],
                                                    mgranted |-> granted,
                                                    msrc |-> s,
                                                    mdest |-> m.msrc])
                                       /\ Assert(granted=TRUE,"1")
                        /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                          eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 




MakeVoteFailOldLog(s) == /\ \E m \in net :
                               /\ m.mtype = "RequestVote"
                               /\ m.mterm = currentTerm[s]
                               /\ Len(log[s]) # 0
                               /\ \/ m.mlastIndex = 0
                                  \/ log[s][Len(log[s])].term > m.mlastTerm
                                  \/ /\ log[s][Len(log[s])].term = m.mlastTerm
                                     /\ Len(log[s]) > m.mlastIndex  
                               /\ ~ (\E mm \in net : /\ mm.mtype = "RequestVoteResponse"
                                                     /\ mm.mterm = currentTerm[s]
                                                     /\ mm.msrc = s
                                                     /\ mm.mdest = m.msrc)
                               /\ Send(net,
                                            [mtype |-> "RequestVoteResponse",
                                             mterm |-> currentTerm[s],
                                             mgranted |-> FALSE,
                                             msrc |-> s,
                                             mdest |-> m.msrc])
                        /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                    eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 
                     

MakeVoteFailVotedAnother(s) == /\ \E m \in net :
                                     /\ m.mtype = "RequestVote"
                                     /\ m.mterm = currentTerm[s]
                                     /\ votedFor[s] # UNDEF
                                     /\ votedFor[s] # m.msrc
                                     /\ ~ (\E mm \in net :
                                                        /\ mm.mtype = "RequestVoteResponse"
                                                        /\ mm.mterm = currentTerm[s]
                                                        /\ mm.msrc = s
                                                        /\ mm.mdest = m.msrc)
                                      /\ Send(net,
                                              [mtype |-> "RequestVoteResponse",                        
                                               mterm |-> currentTerm[s],
                                               mgranted |-> FALSE,
                                               msrc |-> s,
                                               mdest |-> m.msrc])
                              /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                           eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 



VoteBecomeFollower(s) == /\ \E m \in net :
                                 /\ m.mtype = "RequestVoteResponse"
                                 /\ m.mdest = s
                                 /\ m.mterm > currentTerm[s]
                                 /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                 /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                                 /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                 /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                        /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                  net,eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 


MakeVote(s) == /\ \E m \in net :
                    /\ m.mtype = "RequestVote"
                    /\ m.mterm = currentTerm[s]
                    /\ votedFor[s] = UNDEF
                    /\ CompareImp(log[s],m.mlastTerm,m.mlastIndex)                    
                   (* /\ \/ Len(log[s]) = 0
                       \/ /\ m.lastIndex # 0
                          /\ Len(log[s]) > 0
                          /\ \/ m.lastTerm > log[s][Len(log[s])].term
                             \/ /\ m.lastTerm = log[s][Len(log[s])].term
                                /\ m.lastIndex >= Len(log[s]) *)
                    /\ votedFor' = [votedFor EXCEPT ![s] = m.msrc]
                    /\ ~(\E mm \in net : /\ mm.mtype = "RequestVoteResponse"
                                         /\ mm.msrc = s
                                         /\ mm.mdest = m.msrc
                                         /\ mm.mterm = currentTerm[s])
                    /\ Send(net,
                                [mtype |-> "RequestVoteResponse",
                                 mterm |-> currentTerm[s],
                                 mgranted |-> TRUE,
                                 msrc |-> s,
                                 mdest |-> m.msrc])                                                                  
               /\ UNCHANGED <<currentTerm,state,updateRec,replicationVars,leaderVars,preVoteVars,voteVars,
                            eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 


Restart(s) == /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
              /\ commitIndex' = [commitIndex EXCEPT ![s] = 0]
              /\ UNCHANGED <<currentTerm,votedFor,updateRec,replicationVars,leaderVars,preVoteVars,
                            voteVars,net,eleSeqVars,matchIndex,nextIndex,e1,e2,e3,e4,e5>> 
 
 

 
 

BecomeLeader(s) == /\ \E Q \in Quorums :
                        \A q \in Q : \E m \in net :
                            /\ m.mtype = "RequestVoteResponse"
                            /\ m.mgranted = TRUE
                            /\ m.msrc = q
                            /\ m.mterm = currentTerm[s]
                            /\ m.mdest = s 
                   /\ state[s] = "CANDIDATE"
                   /\ state' = [state EXCEPT ![s] = "LEADER"]
                   /\ leader' = [leader EXCEPT ![currentTerm[s]] = s]
                   /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[s]] = log[s]]
                   /\ nextIndex' = [nextIndex EXCEPT ![s] = [ss \in Server |-> Len(log[s])+1]]
                   /\ matchIndex' = [matchIndex EXCEPT ![s] = [ss \in Server |-> 0]]
                   /\ UNCHANGED <<currentTerm,votedFor,updateRec,replicationVars,preVoteVars,voteVars,
                                 net,eleSeqVars,commitIndex,e1,e2,e3,e4,e5>> 
 
          
                                      
AppendEntries(s1,s2) == LET ind == nextIndex[s1][s2] 
                              e == IF ind > Len(log[s1]) THEN UNDEF
                                   ELSE
                                   [ term |-> log[s1][ind].term,
                                     index |-> ind,
                                     value |-> log[s1][ind].value,
                                     leaderTerm |-> currentTerm[s1] ]
                        IN            
                         /\ state[s1] = "LEADER"
                         /\ s1 # s2
                         /\ Len(log[s1]) >= ind
                         /\ ~(\E m \in net : /\ m.mtype = "AppendEntries"
                                             /\ m.mterm = currentTerm[s1]
                                             /\ m.msrc= s1
                                             /\ m.mdest = s2
                                             /\ m.mprevIndex = ind - 1
                                             /\ m.mentry =e)                       
                         /\ Send(net,
                                  [ mtype |-> "AppendEntries",
                                    mterm |-> currentTerm[s1],
                                    mprevTerm |-> IF ind = 1 THEN 0 ELSE log[s1][ind-1].term,
                                    mprevIndex |-> ind-1,
                                    mentry |-> e,
                                    mcommitIndex |-> commitIndex[s1],
                                    msrc |-> s1,
                                    mdest |-> s2])
                        /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                         eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 

                                                                      
            
ReplicateFailLowTerm(s1,s2) == /\ \E m \in net :
                                  /\ m.mtype = "AppendEntries"
                                  /\ m.mdest = s2
                                  /\ m.msrc = s1
                                  /\ m.mterm < currentTerm[s2]
                                  /\ Send(net,
                                      [ mtype |-> "AppendEntriesResponse",
                                        mterm |-> currentTerm[s2],
                                        msuccess |-> FALSE,
                                        mindex |-> m.mprevIndex +1, 
                                        msrc |-> s2,
                                        mdest |-> m.msrc])
                              /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                         eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 


ReplicateFailUnmatch(s1,s2) == /\ \E m \in net :
                                   /\ m.mtype = "AppendEntries"
                                   /\ m.mdest = s2
                                   /\ m.msrc = s1
                                   /\ \/ /\ m.mterm = currentTerm[s2]
                                         /\ UNCHANGED <<currentTerm,state,votedFor,updateRec>>
                                      \/ /\ m.mterm > currentTerm[s2]
                                         /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                                         /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
                                         /\ votedFor' = [votedFor EXCEPT ![s2] = UNDEF]
                                         /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s2}]
                                   /\ m.mprevIndex # 0
                                   /\ \/ Len(log[s2]) < m.mprevIndex
                                      \/ /\ Len(log[s2]) >= m.mprevIndex
                                         /\ log[s2][m.mprevIndex].term # m.mprevTerm
                                   /\ Send(net,
                                             [ mtype |-> "AppendEntriesResponse",
                                               mterm |-> currentTerm'[s2],
                                               msuccess |-> FALSE,
                                               mindex |-> m.mprevIndex+1,
                                               msrc |-> s2,
                                               mdest |-> m.msrc])
                              /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                            eleSeqVars,indexVars,e1,e2,e3,e4,e5>> 
                              
                              
ReplicateSameEntry(s1,s2) == /\ \E m \in net :
                                /\ m.mtype = "AppendEntries"
                                /\ m.mdest = s2
                                /\ m.msrc = s1
                                /\ \/ /\ m.mterm = currentTerm[s2]
                                      /\ UNCHANGED <<currentTerm,state,votedFor,updateRec>>
                                   \/ /\ m.mterm > currentTerm[s2]
                                      /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                                      /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
                                      /\ votedFor' = [votedFor EXCEPT ![s2] = UNDEF]
                                      /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s2}]
                                /\ \/ m.mprevIndex = 0
                                   \/ /\ m.mprevIndex # 0
                                      /\ Len(log[s2]) >= m.mprevIndex
                                      /\ log[s2][m.mprevIndex].term = m.mprevTerm
                                /\ Len(log[s2]) >= m.mprevIndex +1
                                /\ log[s2][m.mprevIndex+1].term = m.mentry.term
                                /\ UNCHANGED <<log,accepted>>
                                /\ Send(net,
                                         [ mtype |-> "AppendEntriesResponse",
                                           mterm |-> currentTerm'[s2],
                                           msuccess |-> TRUE,
                                           mindex |-> m.mprevIndex+1,
                                           msrc |-> s2,
                                           mdest |-> m.msrc])
                                /\ commitIndex' = [commitIndex EXCEPT ![s2] = IF m.mcommitIndex > commitIndex[s2]
                                                                              THEN min(m.mcommitIndex,m.mprevIndex+1)
                                                                              ELSE commitIndex[s2]]
                            /\ UNCHANGED <<leaderVars,preVoteVars,voteVars, eleSeqVars,nextIndex,matchIndex,
                                               e1,e2,e3,e4,e5>> 
                           
                           
Replicate(s1,s2) == /\ \E m \in net :
                        /\ m.mtype = "AppendEntries"
                        /\ m.mdest = s2
                        /\ m.msrc = s1
                        /\ \/ /\ m.mterm = currentTerm[s2]
                              /\ UNCHANGED <<currentTerm,state,votedFor,updateRec>>
                           \/ /\ m.mterm > currentTerm[s2]
                              /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                              /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
                              /\ votedFor' = [votedFor EXCEPT ![s2] = UNDEF]
                              /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s2}]
                        /\ \/ m.mprevIndex = 0
                           \/ /\ m.mprevIndex # 0
                              /\ Len(log[s2]) >= m.mprevIndex
                              /\ log[s2][m.mprevIndex].term = m.mprevTerm
                        /\ \/ /\ Len(log[s2]) < m.mprevIndex + 1
                           \/ /\ Len(log[s2]) >= m.mprevIndex + 1
                              /\ log[s2][m.mprevIndex+1].term # m.mentry.term
                        /\ log' = [log EXCEPT ![s2] = Append(SubSeq(log[s2],1,m.mprevIndex),m.mentry)]
                        /\ accepted' = [accepted EXCEPT ![s2] = accepted[s2] \cup {m.mentry}]
                        /\ voteSet' = [a \in Server |-> IF /\ state[a] = "CANDIDATE"
                                                           /\ s2 \in voteSet[a]
                                                           /\ currentTerm'[s2] < currentTerm[a]
                                                           /\ ~ Compare(log[a],log'[s2])
                                                        THEN voteSet[a] \ {s2}
                                                        ELSE voteSet[a]]
                        /\ Send(net,
                                     [ mtype |-> "AppendEntriesResponse",
                                       mterm |-> currentTerm'[s2],
                                       msuccess |-> TRUE,
                                       mindex |-> m.mprevIndex+1,
                                       msrc |-> s2,
                                       mdest |-> m.msrc])
                        /\ commitIndex' = [commitIndex EXCEPT ![s2] = IF m.mcommitIndex > commitIndex[s2]
                                                                               THEN min(m.mcommitIndex,m.mprevIndex+1)
                                                                                ELSE commitIndex[s2]]
                    /\ UNCHANGED <<leaderVars,preVoteVars,voteTerm,
                                    eleSeqVars,nextIndex,matchIndex,e1,e2,e3,e4,e5>> 
                                                                                
                                                                                                                                                                  
NewProposal(s,v) == LET e == [term |-> currentTerm[s],
                              index |-> Len(log[s])+1,
                              value |-> v,
                              leaderTerm |-> currentTerm[s]]
                    IN
                        /\ state[s] = "LEADER"
                    (*    /\ initLeader[s] = TRUE
                                                     序号需要在Nat的范围内               *)
                        (*/\ Len(log[s])+2 \in Seq   *)
                        /\ Len(log[s])+1 \in Seqs               
                        /\ log' = [log EXCEPT ![s] = Append(log[s],e)]
                        /\ accepted' = [accepted EXCEPT ![s] = accepted[s] \cup {e}]
                        /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[s]] = Append(log[s],e)]
                        /\ voteSet' = [a \in Server |-> IF /\ state[a] = "CANDIDATE"
                                                           /\ s \in voteSet[a]
                                                           /\ currentTerm[s] < currentTerm[a]
                                                           /\ ~ Compare(log[a],log'[s])
                                                        THEN (voteSet[a] \ {s})
                                                        ELSE voteSet[a]]
                        /\ UNCHANGED <<stateVars,leader,preVoteVars,voteTerm,
                                      net,eleSeqVars,indexVars,e1,e2,e3,e4,e5>>         



HandleAppendEntriesResponseLowTerm(s) == /\ \E m \in net :
                                            /\ m.mtype = "AppendEntriesResponse"
                                            /\ m.mdest = s
                                            /\ m.mterm > currentTerm[s]
                                            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                            /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                                            /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                            /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                                         /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                               net,eleSeqVars,indexVars,e1,e2,e3,e4,e5>>                 
                     


HandleAppendEntriesResponseFail(s) == /\ \E m \in net :
                                        /\ m.mtype = "AppendEntriesResponse"
                                        /\ m.mdest = s
                                        /\ m.mterm = currentTerm[s]
                                        /\ state[s] = "LEADER"
                                        /\ m.msuccess = FALSE
                                        /\ nextIndex' = [nextIndex EXCEPT ![s][m.msrc] = max(1,nextIndex[s][m.msrc]-1)]
                                      /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                              net,eleSeqVars,commitIndex,matchIndex,e1,e2,e3,e4,e5>> 
                                      
                                      
HandleAppendEntriesResponseSuccess(s) == /\ \E m \in net :
                                            /\ m.mtype = "AppendEntriesResponse"
                                            /\ m.mdest = s
                                            /\ state[s] = "LEADER"
                                            /\ m.mterm = currentTerm[s]
                                            /\ m.msuccess = TRUE
                                            /\ m.mindex > matchIndex[s][m.msrc]
                                            /\ nextIndex' = [nextIndex EXCEPT ![s][m.msrc] = m.mindex + 1]
                                            /\ matchIndex' = [matchIndex EXCEPT ![s][m.msrc] = m.mindex]
                                         /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                               net,eleSeqVars,commitIndex,e1,e2,e3,e4,e5>> 
                          
                                
(*  辅助函数 *)
AdvanceCommitIndex(s) == \E i \in 1..Len(log[s]):
                            /\ state[s] = "LEADER"
                            /\ log[s][i].term = currentTerm[s]
                            /\ \E Q \in Quorums : \A q \in Q : matchIndex[s][q] >= i
                            /\ i > commitIndex[s]
                            /\ commitIndex' = [commitIndex EXCEPT ![s] = i]
                            /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                           net,eleSeqVars,nextIndex,matchIndex,e1,e2,e3,e4,e5>> 




Init == /\ state  = [s \in Server |-> "FOLLOWER"]
        /\ currentTerm = [s \in Server |-> 0]   
        /\ votedFor = [s \in Server |-> UNDEF]
        /\ net = {}        
        /\ voteSeq = [s \in Server |-> 0]
        /\ ackedVoteSeq = [s \in Server |-> [a \in Server |-> 0]] 
        /\ preVoteSet = [s \in Server |-> {}]
        /\ preVoteTerm = {}
        /\ voteCnt = 0
        /\ voteTerm = {}
        /\ voteSet = [s \in Server |-> {}] 
        /\ updateRec = [t \in Term |-> IF t = 0 THEN Server ELSE {}]
        /\ log = [s \in Server |-> <<>> ]
        /\ accepted = [s \in Server |-> {}]  
        /\ leader = [t \in Term |-> UNDEF]
        /\ leaderLog = [t \in Term |-> <<>>] 
        /\ nextIndex = [s \in Server |-> [ss \in Server |-> 0]]
        /\ matchIndex = [s \in Server |-> [ss \in Server |-> 0]]
        /\ commitIndex = [s \in Server |-> 0]
        /\ e1 = 0
        /\ e2 = 0
        /\ e3 = 0
        /\ e4 = 0
        /\ e5 = 0


Next == \/ \E s \in Server : PreVote(s)
        \/ \E s \in Server : HandlePreVoteUpdateTerm(s)
        \/ \E s \in Server : HandlePreVote(s)
        \/ \E s \in Server : HandlePreVoteRefuseLowTerm(s)
        \/ \E s \in Server : PreVoteBecomeFollower(s)
        \/ \E s \in Server : BecomeCandidate(s)
        \/ \E s \in Server : RequestVote(s)
        \/ \E s \in Server : MakeVoteFailLowTerm(s)
        \/ \E s \in Server : MakeVoteUpdateTerm(s)
        \/ \E s \in Server : MakeVoteFailOldLog(s)
        \/ \E s \in Server : MakeVoteFailVotedAnother(s)
        \/ \E s \in Server : VoteBecomeFollower(s)
        \/ \E s \in Server : MakeVote(s)
        (*\/ \E s \in Server : Restart(s) *)
        \/ \E s \in Server : BecomeLeader(s)
        \/ \E s1,s2 \in Server : AppendEntries(s1,s2) 
        \/ \E s1,s2 \in Server : ReplicateFailLowTerm(s1,s2)
        \/ \E s1,s2 \in Server : ReplicateFailUnmatch(s1,s2) 
        \/ \E s1,s2 \in Server : ReplicateSameEntry(s1,s2)
        \/ \E s1,s2 \in Server : Replicate(s1,s2)
        \/ \E s \in Server, v \in Value : NewProposal(s,v)
        \/ \E s \in Server : HandleAppendEntriesResponseLowTerm(s)
        \/ \E s \in Server : HandleAppendEntriesResponseFail(s)
        \/ \E s \in Server : HandleAppendEntriesResponseSuccess(s)
        \/ \E s \in Server : AdvanceCommitIndex(s)
   
                     
Spec == Init /\ [][Next]_vars
                      
(*        
ARaft == INSTANCE TestAbsReplication

Refinement == Spec => ARaft!Spec     
*)        

acceptedAll(s,e) == e \in accepted[s]

acceptedCur(s,e) == /\ acceptedAll(s,e)
                    /\ e.term = e.leaderTerm
                    
committedExp(e) == \E Q \in Quorums :
                        \A s \in Q : acceptedCur(s,e)
                        
                        
committedImp(e) == \E s \in Server: \E i,j \in 1..Len(log[s]) : 
                                                  /\ log[s][i] = e
                                                  /\ j > i
                                                  /\ committedExp(log[s][j])                              
                                                
committed(e) == \/ committedExp(e)
                \/ committedImp(e)


Consistency == \A en1,en2 \in Entries : committed(en1) /\ committed(en2) /\ en1.index = en2.index => 
                en1.value = en2.value



=============================================================================
\* Modification History
\* Last modified Fri Jan 21 02:38:35 CST 2022 by gxs
\* Created Sun Sep 26 17:18:52 CST 2021 by gxs
