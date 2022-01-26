Raft is divided into three modules, module _PreVote_ describing Raft's prevote mechanism, module _Vote_ describing Raft's election mechanism and module _Replication_ containing actions describing the transmission of log entries from leader to followers.   There are four specifications:

* **Raft.tla**:  Original specification of Raft 

* **PreVote.tla**:  Specification with module _Vote_ and _Replication_ abstracted
* **Vote.tla**: Specification with module _PreVote_ and _Replication_ abstracted
* **Replication.tla**: Spefication with module _PreVote_ and _Vote_ abstracted



