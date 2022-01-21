----------------------------- MODULE Replicate -----------------------------



EXTENDS Naturals,Sequences


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


                             
VARIABLES state,currentTerm,updateRec

stateVars == <<state,currentTerm,updateRec>>

VARIABLES e1,e2,e3,e4,e5



VARIABLE net

VARIABLES nextIndex,
          matchIndex,
          commitIndex
              
indexVars == <<nextIndex,commitIndex,matchIndex>>     


Entries == [term : Term, index : Seqs, value : Value, leaderTerm : Term]

vars == <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
            updateRec,net,indexVars,
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


   
AbsPreVote(s) == /\ state[s] = "FOLLOWER"
                 /\ state' = [state EXCEPT ![s] = "PRE_CANDIDATE"]
                 /\ currentTerm[s] + 1 \in Term
                 /\ voteCnt + 1 \in Votes
                 /\ voteCnt' = voteCnt + 1
                 /\ preVoteTerm' = preVoteTerm \cup {currentTerm[s]}
                 /\ preVoteSet' = [preVoteSet EXCEPT ![s] = 
                                        {a \in Server : 
                                                /\ currentTerm[a] <= currentTerm[s]
                                                /\ CompareLog(s,a)}]
                 /\ UNCHANGED <<currentTerm,voteVars,updateRec,
                                    replicationVars,leaderVars,
                                    e1,e2,e3,e4,e5,net,indexVars>>


PreVoteUpdateTerm(s) == /\ \E t \in preVoteTerm:
                             /\ t > currentTerm[s]
                             /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                             /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                             /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                        /\ UNCHANGED <<preVoteVars,voteVars,
                                        replicationVars,leaderVars,
                                    e1,e2,e3,e4,e5,net,indexVars>>



BecomeCandidate(s) == /\ state[s] = "PRE_CANDIDATE"
                      /\ \E Q \in Quorums : 
                          \A q \in Q : /\ q \in preVoteSet[s]
                                       /\ q \in updateRec[currentTerm[s]]
                      /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
                      /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
                      /\ voteTerm' = voteTerm \cup {currentTerm'[s]}
                      /\ updateRec' = [updateRec EXCEPT ![currentTerm'[s]] = @ \cup {s}]
                      /\ voteSet' = [voteSet EXCEPT ![s] = {a \in Server :
                                                                /\ currentTerm[a] <= currentTerm'[s]
                                                                /\ CompareLog(s,a)}]
                      /\ UNCHANGED <<preVoteVars,
                                    replicationVars,leaderVars,
                                    e1,e2,e3,e4,e5,net,indexVars>>


voteUpdateTerm(s) == /\ \E t \in voteTerm :
                         /\ t > currentTerm[s]
                         /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                         /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                         /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                     /\ UNCHANGED <<preVoteVars,voteVars,
                                    replicationVars,leaderVars,
                                    e1,e2,e3,e4,e5,net,indexVars>>


Restart(s) == /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
              /\ commitIndex' = [commitIndex EXCEPT ![s] = 0]
              /\ UNCHANGED <<currentTerm,updateRec,replicationVars,leaderVars,preVoteVars,
                            voteVars,net,matchIndex,nextIndex,e1,e2,e3,e4,e5,matchIndex,
                                    net>> 


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


                                                                  
committedBefore(t) == {e \in Entries :  e.term < t /\ committed(e)}



BecomeLeader(s) ==  /\ state[s] = "CANDIDATE"           
                    /\ \A e \in committedBefore(currentTerm[s]) : 
                                 \E i \in 1..Len(log[s]) : /\ log[s][i].term = e.term
                                                            /\ i = e.index 
                    /\ \E Q \in Quorums : \A a \in Q : /\ a \in voteSet[s]
                                                       /\ a \in updateRec[currentTerm[s]]  
                    /\ leader[currentTerm[s]] = UNDEF
                    /\ state' = [state EXCEPT ![s] = "LEADER"]
                    /\ leader' = [leader EXCEPT ![currentTerm[s]] = s]
                    /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[s]] = log[s]]
                    /\ nextIndex' = [nextIndex EXCEPT ![s] = [ss \in Server |-> Len(log[s])+1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![s] = [ss \in Server |-> 0]]
                    /\ UNCHANGED <<currentTerm,preVoteVars,voteVars,updateRec,
                                replicationVars,e1,e2,e3,e4,e5,net,commitIndex>>  
       
                                      
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
                                         indexVars,e1,e2,e3,e4,e5>> 

                                                                      
            
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
                                         indexVars,e1,e2,e3,e4,e5>> 


ReplicateFailUnmatch(s1,s2) == /\ \E m \in net :
                                   /\ m.mtype = "AppendEntries"
                                   /\ m.mdest = s2
                                   /\ m.msrc = s1
                                   /\ \/ /\ m.mterm = currentTerm[s2]
                                         /\ UNCHANGED <<currentTerm,state,updateRec>>
                                      \/ /\ m.mterm > currentTerm[s2]
                                         /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                                         /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
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
                                            indexVars,e1,e2,e3,e4,e5>> 
                              
                              
ReplicateSameEntry(s1,s2) == /\ \E m \in net :
                                /\ m.mtype = "AppendEntries"
                                /\ m.mdest = s2
                                /\ m.msrc = s1
                                /\ \/ /\ m.mterm = currentTerm[s2]
                                      /\ UNCHANGED <<currentTerm,state,updateRec>>
                                   \/ /\ m.mterm > currentTerm[s2]
                                      /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                                      /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
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
                            /\ UNCHANGED <<leaderVars,preVoteVars,voteVars,nextIndex,matchIndex,
                                               e1,e2,e3,e4,e5>> 
                           
                           
Replicate(s1,s2) == /\ \E m \in net :
                        /\ m.mtype = "AppendEntries"
                        /\ m.mdest = s2
                        /\ m.msrc = s1
                        /\ \/ /\ m.mterm = currentTerm[s2]
                              /\ UNCHANGED <<currentTerm,state,updateRec>>
                           \/ /\ m.mterm > currentTerm[s2]
                              /\ currentTerm' = [currentTerm EXCEPT ![s2] = m.mterm]
                              /\ state' = [state EXCEPT ![s2] = "FOLLOWER"]
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
                                    nextIndex,matchIndex,e1,e2,e3,e4,e5>> 
                                                                                

                                                           
(*  主函数 newProposal  *)                                                                                                                                    
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
                                      net,indexVars,e1,e2,e3,e4,e5>>         



HandleAppendEntriesResponseLowTerm(s) == /\ \E m \in net :
                                            /\ m.mtype = "AppendEntriesResponse"
                                            /\ m.mdest = s
                                            /\ m.mterm > currentTerm[s]
                                            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                            /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                            /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                                         /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                               net,indexVars,e1,e2,e3,e4,e5>>                 
                     


HandleAppendEntriesResponseFail(s) == /\ \E m \in net :
                                        /\ m.mtype = "AppendEntriesResponse"
                                        /\ m.mdest = s
                                        /\ m.mterm = currentTerm[s]
                                        /\ state[s] = "LEADER"
                                        /\ m.msuccess = FALSE
                                        /\ nextIndex' = [nextIndex EXCEPT ![s][m.msrc] = max(1,nextIndex[s][m.msrc]-1)]
                                      /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                              net,commitIndex,matchIndex,e1,e2,e3,e4,e5>> 
                                      
                                      
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
                                               net,commitIndex,e1,e2,e3,e4,e5>> 
                          
                                
(*  辅助函数 *)
AdvanceCommitIndex(s) == \E i \in 1..Len(log[s]):
                            /\ state[s] = "LEADER"
                            /\ log[s][i].term = currentTerm[s]
                            /\ \E Q \in Quorums : \A q \in Q : matchIndex[s][q] >= i
                            /\ i > commitIndex[s]
                            /\ commitIndex' = [commitIndex EXCEPT ![s] = i]
                            /\ UNCHANGED <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
                                           net,nextIndex,matchIndex,e1,e2,e3,e4,e5>> 




Init == /\ state  = [s \in Server |-> "FOLLOWER"]
        /\ currentTerm = [s \in Server |-> 0]   
        /\ net = {}        
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


Next == \/ \E s \in Server : AbsPreVote(s)
        \/ \E s \in Server : PreVoteUpdateTerm(s)
        \/ \E s \in Server : BecomeCandidate(s)
        \/ \E s \in Server : voteUpdateTerm(s) 
        \/ \E s \in Server : BecomeLeader(s)
        (*\/ \E s \in Server : Restart(s) *)
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


Consistency == \A en1,en2 \in Entries : committed(en1) /\ committed(en2) /\ en1.index = en2.index => 
                en1.value = en2.value



=============================================================================
\* Modification History
\* Last modified Sun Oct 10 22:39:11 CST 2021 by gxs
\* Created Fri Oct 08 02:19:01 CST 2021 by gxs
