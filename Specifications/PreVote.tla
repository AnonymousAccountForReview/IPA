------------------------------ MODULE PreVote ------------------------------



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


VARIABLES voteSeq,ackedVoteSeq
eleSeqVars == <<voteSeq,ackedVoteSeq>>

VARIABLE net


Entries == [term : Term, index : Seqs, value : Value, leaderTerm : Term]

vars == <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
            updateRec,net,eleSeqVars,
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

(* s2Ϊs1ͶƱ *)

CompareLog(s1,s2) == Compare(log[s1],log[s2])

PreVote(s) == /\ state[s] = "FOLLOWER"
              /\ state' = [state EXCEPT ![s] = "PRE_CANDIDATE"]
              /\ voteSeq' = [voteSeq EXCEPT ![s] = @ +1]
              /\ voteCnt + 1 \in Votes
              /\ voteCnt' = voteCnt + 1
              /\ currentTerm[s] + 1 \in Term
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
              /\ UNCHANGED <<currentTerm,ackedVoteSeq,voteVars,updateRec,
                         e1,e2,e3,e4,e5,replicationVars,leaderVars>>


HandlePreVoteUpdateTerm(s) == /\ \E m \in net :
                                  /\ m.mtype = "PreVoteRequest"
                                  /\ m.mvoteSeq > ackedVoteSeq[s][m.msrc]
                                  /\ ackedVoteSeq' = [ackedVoteSeq EXCEPT ![s][m.msrc] = m.mvoteSeq]
                                  /\ m.mterm > currentTerm[s]
                                  /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
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
                                              voteSeq,
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
                                    voteSeq,
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
                                                    voteSeq,
                                                    e1,e2,e3,e4,e5>>


           
PreVoteBecomeFollower(s) == /\ \E m \in net :
                               /\ m.mtype = "PreVoteResponse"
                               /\ m.mdest = s
                               /\ m.mterm > currentTerm[s]
                               /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                               /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                               /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                             /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                               net,eleSeqVars,
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
                      /\ voteTerm' = voteTerm \cup {currentTerm'[s]}
                      /\ updateRec' = [updateRec EXCEPT ![currentTerm'[s]] = @ \cup {s}]
                      /\ voteSet' = [voteSet EXCEPT ![s] = {a \in Server :
                                                                /\ currentTerm[a] <= currentTerm'[s]
                                                                /\ CompareLog(s,a)}]
                      /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,
                                               net,eleSeqVars,
                                               e1,e2,e3,e4,e5>> 
                     
                     

voteUpdateTerm(s) == /\ \E t \in voteTerm :
                         /\ t > currentTerm[s]
                         /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                         /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                         /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                     /\ UNCHANGED <<preVoteVars,voteVars,
                                    replicationVars,leaderVars,eleSeqVars,net,
                                    e1,e2,e3,e4,e5>>


Restart(s) == /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
              /\ UNCHANGED <<currentTerm,preVoteVars,voteVars,updateRec,log,
                             replicationVars,leaderVars,e1,e2,e3,e4,e5,net,
                             eleSeqVars,net,eleSeqVars>>



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
                    /\ UNCHANGED <<currentTerm,preVoteVars,voteVars,updateRec,
                                replicationVars,e1,e2,e3,e4,e5,net,eleSeqVars>>  
                                    

NewProposal(s,v) == LET e == [term |-> currentTerm[s],
                              index |-> Len(log[s])+1,
                              value |-> v,
                              leaderTerm |-> currentTerm[s]]
                    IN         
                        /\ state[s] = "LEADER"
                        /\ Len(log[s]) + 1 \in Seqs
                        /\ log' = [log EXCEPT ![s] = Append(log[s],e)]
                        /\ accepted' = [accepted EXCEPT ![s] = accepted[s] \cup {e}]
                        /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[s]] = Append(log[s],e)]
                        /\ voteSet' = [a \in Server |-> IF /\ state[a] = "CANDIDATE"
                                                           /\ s \in voteSet[a]
                                                           /\ currentTerm[s] < currentTerm[a]
                                                           /\ ~ Compare(log[a],log'[s])
                                                        THEN (voteSet[a] \ {s})
                                                        ELSE voteSet[a]]
                        /\ UNCHANGED <<leader,stateVars,preVoteVars,voteTerm,
                                        e1,e2,e3,e4,e5,updateRec,net,eleSeqVars>>

                                  
consistent(l1,l2,i) == /\ Len(l2) >= i
                       /\ \/ \A j \in 1..i : l1[j].term = l2[j].term
                          \/ i = 0
                       
                       
Replicate(s1,s2) ==  LET t == currentTerm[s2] IN
                       /\ t # 0
                       /\ leader[t] = s1 
                       /\ s1 # s2
                       /\ \E j \in 1..Len(leaderLog[t]) : 
                                /\ consistent(leaderLog[t],log[s2],j-1)
                                /\ \/ Len(log[s2]) < j
                                   \/ /\ Len(log[s2]) >= j
                                      /\ leaderLog[t][j].term # log[s2][j].term
                                /\ LET en == [ term |-> leaderLog[t][j].term,
                                               index |-> leaderLog[t][j].index,
                                               value |-> leaderLog[t][j].value,
                                               leaderTerm |-> t] 
                                    IN
                                    /\ accepted' = [accepted EXCEPT ![s2] = accepted[s2] \cup {en}]
                                    /\ log' = [log EXCEPT ![s2] = Append(SubSeq(log[s2],1,j-1),en)]
                       /\ voteSet' = [a \in Server |-> IF /\ state[a] = "CANDIDATE"
                                                          /\ s2 \in voteSet[a]
                                                          /\ currentTerm[s2] < currentTerm[a]
                                                          /\ ~ Compare(log[a],log'[s2])
                                                       THEN voteSet[a] \ {s2}
                                                       ELSE voteSet[a]]
                       /\ UNCHANGED <<leaderVars,stateVars,preVoteVars,voteTerm,
                                        updateRec,e1,e2,e3,e4,e5,net,eleSeqVars>>

ReplicateUpdateTerm(s,t) == /\ leader[t] # UNDEF
                            /\ currentTerm[s] < t
                            /\ \E j \in 1..Len(leaderLog[t]) :
                                 /\ consistent(leaderLog[t],log[s],j-1)
                                 /\ LET en == [ term |-> leaderLog[t][j].term,
                                                index |-> leaderLog[t][j].index,
                                                value |-> leaderLog[t][j].value,
                                                leaderTerm |-> t] 
                                    IN
                                       /\ accepted' = [accepted EXCEPT ![s] = accepted[s] \cup {en}]
                                       /\ log' = [log EXCEPT ![s] = Append(SubSeq(log[s],1,j-1),en)]
                            /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                            /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                            /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                            /\ voteSet' = [a \in Server |-> IF /\ state[a] = "CANDIDATE"
                                                               /\ s \in voteSet[a]
                                                               /\ t < currentTerm[a]
                                                               /\ ~ Compare(log[a],log'[s])
                                                           THEN voteSet[a] \ {s}
                                                           ELSE voteSet[a]]
                            /\ UNCHANGED <<leaderVars,preVoteVars,voteTerm,
                                                    e1,e2,e3,e4,e5,net,eleSeqVars>>
                  



Init == /\ state  = [s \in Server |-> "FOLLOWER"]
        /\ currentTerm = [s \in Server |-> 0]   
        /\ net = {}        
        /\ voteSeq = [s \in Server |-> 0]
        /\ voteCnt = 0
        /\ ackedVoteSeq = [s \in Server |-> [a \in Server |-> 0]] 
        /\ preVoteSet = [s \in Server |-> {}]
        /\ preVoteTerm = {}
        /\ voteTerm = {}
        /\ voteSet = [s \in Server |-> {}] 
        /\ updateRec = [t \in Term |-> IF t = 0 THEN Server ELSE {}]
        /\ log = [s \in Server |-> <<>> ]
        /\ accepted = [s \in Server |-> {}]  
        /\ leader = [t \in Term |-> UNDEF]
        /\ leaderLog = [t \in Term |-> <<>>] 
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
        \/ \E s \in Server : voteUpdateTerm(s) 
     (* \/ \E s \in Server : Restart(s) *)
        \/ \E s \in Server : BecomeLeader(s)
        \/ \E s \in Server, v \in Value : NewProposal(s,v)
        \/ \E s1,s2 \in Server : Replicate(s1,s2)
        \/ \E s \in Server, t \in Term : ReplicateUpdateTerm(s,t)
   
                     
Spec == Init /\ [][Next]_vars
                      
        
(*
ARaft == INSTANCE TestAbsReplication

Refinement == Spec => ARaft!Spec     
        
*)

Consistency == \A en1,en2 \in Entries : committed(en1) /\ committed(en2) /\ en1.index = en2.index => 
                en1.value = en2.value


Inv == \A s \in Server : voteSeq[s] <= currentTerm[s] + 1

=============================================================================
\* Modification History
\* Last modified Wed Oct 13 22:45:46 CST 2021 by gxs
\* Created Fri Sep 24 16:29:58 CST 2021 by gxs
