-------------------------------- MODULE Vote --------------------------------

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


                             
VARIABLES state,currentTerm,votedFor,updateRec

stateVars == <<state,currentTerm,votedFor,updateRec>>

VARIABLES e1,e2,e3,e4,e5



VARIABLE net


Entries == [term : Term, index : Seqs, value : Value, leaderTerm : Term]

vars == <<stateVars,replicationVars,leaderVars,preVoteVars,voteVars,
            updateRec,net,
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
                                    replicationVars,leaderVars,votedFor,
                                    e1,e2,e3,e4,e5,net>>


PreVoteUpdateTerm(s) == /\ \E t \in preVoteTerm:
                             /\ t > currentTerm[s]
                             /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                             /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                             /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                        /\ UNCHANGED <<preVoteVars,voteVars,
                                        replicationVars,leaderVars,votedFor,
                                    e1,e2,e3,e4,e5,net>>



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
                                    replicationVars,leaderVars,votedFor,
                                    e1,e2,e3,e4,e5,net>>

voteUpdateTerm(s) == /\ \E t \in voteTerm :
                         /\ t > currentTerm[s]
                         /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
                         /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                         /\ updateRec' = [updateRec EXCEPT ![t] = @ \cup {s}]
                     /\ UNCHANGED <<preVoteVars,voteVars,
                                    replicationVars,leaderVars,votedFor,
                                    e1,e2,e3,e4,e5,net>>

 

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
                                     e1,e2,e3,e4,e5>>                   
                     
                     
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
                                          e1,e2,e3,e4,e5>> 


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
                        /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                          e1,e2,e3,e4,e5>> 




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
                                    e1,e2,e3,e4,e5>> 
                     

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
                                           e1,e2,e3,e4,e5>> 



VoteBecomeFollower(s) == /\ \E m \in net :
                                 /\ m.mtype = "RequestVoteResponse"
                                 /\ m.mdest = s
                                 /\ m.mterm > currentTerm[s]
                                 /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                                 /\ votedFor' = [votedFor EXCEPT ![s] = UNDEF]
                                 /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                                 /\ updateRec' = [updateRec EXCEPT ![m.mterm] = @ \cup {s}]
                        /\ UNCHANGED <<replicationVars,leaderVars,preVoteVars,voteVars,
                                  net,e1,e2,e3,e4,e5,net>> 


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
                            e1,e2,e3,e4,e5>> 



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
                   /\ UNCHANGED <<currentTerm,votedFor,updateRec,replicationVars,preVoteVars,voteVars,
                                 net,e1,e2,e3,e4,e5,net>> 
 



Restart(s) == /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
              /\ UNCHANGED <<currentTerm,votedFor,updateRec,replicationVars,leaderVars,preVoteVars,
                            voteVars,net,e1,e2,e3,e4,e5,net>> 
 

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
                                        e1,e2,e3,e4,e5,updateRec,votedFor,net>>

                                  
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
                                        updateRec,e1,e2,e3,e4,e5,votedFor,net>>

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
                                                    e1,e2,e3,e4,e5,votedFor,net>>
                  


Init == /\ state  = [s \in Server |-> "FOLLOWER"]
        /\ currentTerm = [s \in Server |-> 0]   
        /\ votedFor = [s \in Server |-> UNDEF]
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
        /\ e1 = 0
        /\ e2 = 0
        /\ e3 = 0
        /\ e4 = 0
        /\ e5 = 0


Next == \/ \E s \in Server : AbsPreVote(s)
        \/ \E s \in Server : PreVoteUpdateTerm(s)
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
        \/ \E s1,s2 \in Server : Replicate(s1,s2)
        \/ \E s \in Server, v \in Value : NewProposal(s,v)
        \/ \E s \in Server, t \in Term : ReplicateUpdateTerm(s,t)

   
                     
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
\* Last modified Mon Nov 15 16:54:39 CST 2021 by gxs
\* Created Fri Oct 08 01:38:14 CST 2021 by gxs
