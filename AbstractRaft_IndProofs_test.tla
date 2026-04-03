---- MODULE AbstractRaft_IndProofs_test ----
EXTENDS AbstractRaft,TLAPS,FiniteSetTheorems

\* Proof Graph Stats
\* ==================
\* seed: None
\* num proof graph nodes: 12
\* num proof obligations: 72

IndGlobal == 
  /\ TypeOK
  /\ H_StateMachineSafety
  /\ H_CommittedEntryIsOnQuorum
  /\ H_LaterLogsHaveEarlierCommitted
  /\ H_LeaderCompleteness
  /\ H_LogEntryImpliesSafeAtTerm
  /\ H_TermsMonotonic
  /\ H_UniformLogEntries
  /\ H_QuorumsSafeAtTerms
  /\ H_PrimaryTermGTELogTerm
  /\ H_LogMatching
  /\ H_PrimaryHasOwnEntries
  /\ H_OnePrimaryPerTerm


\* mean in-degree: 1.75
\* median in-degree: 1
\* max in-degree: 6
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(Server) /\ Cardinality(Server) > 1
ASSUME A1 == Nil \notin Server
ASSUME A2 == (Primary # Server)
ASSUME A3 == Server = Server
ASSUME A4 == Quorums(Server) \subseteq SUBSET Server /\ {} \notin Quorums(Server) /\ Quorums(Server) # {} /\ \A s \in Server : {s} \notin Quorums(Server)
ASSUME A5 == MaxLogLen \in Nat
ASSUME A6 == MaxTerm \in Nat /\ InitTerm \in Nat
ASSUME A7 == Primary # Secondary

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (TypeOK,ClientRequestAction)
  <1>1. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,GetEntriesAction)
  <1>2. TypeOK /\ TypeOK /\ GetEntriesAction => TypeOK' BY DEF TypeOK,GetEntriesAction,GetEntries,TypeOK
  \* (TypeOK,RollbackEntriesAction)
  <1>3. TypeOK /\ TypeOK /\ RollbackEntriesAction => TypeOK' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,TypeOK
  \* (TypeOK,BecomeLeaderAction)
  <1>4. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,CommitEntryAction)
  <1>5. TypeOK /\ TypeOK /\ CommitEntryAction => TypeOK' BY DEF TypeOK,CommitEntryAction,CommitEntry,TypeOK
  \* (TypeOK,UpdateTermsAction)
  <1>6. TypeOK /\ TypeOK /\ UpdateTermsAction => TypeOK' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,TypeOK
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_OnePrimaryPerTerm
THEOREM L_1 == TypeOK /\ H_QuorumsSafeAtTerms /\ H_OnePrimaryPerTerm /\ Next => H_OnePrimaryPerTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_OnePrimaryPerTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ ClientRequestAction => H_OnePrimaryPerTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_OnePrimaryPerTerm /\ GetEntriesAction => H_OnePrimaryPerTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_OnePrimaryPerTerm /\ RollbackEntriesAction => H_OnePrimaryPerTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ H_OnePrimaryPerTerm /\ BecomeLeaderAction => H_OnePrimaryPerTerm'
    <2>. SUFFICES ASSUME TypeOK, H_QuorumsSafeAtTerms, H_OnePrimaryPerTerm, BecomeLeaderAction,
                        NEW s1 \in Server, NEW t1 \in Server,
                        state'[s1] = Primary, state'[t1] = Primary, currentTerm'[s1] = currentTerm'[t1]
         PROVE s1 = t1
      BY DEF H_OnePrimaryPerTerm
    <2>1. PICK leader \in Server, Q \in Quorums(Server) : BecomeLeader(leader, Q)
      BY DEF BecomeLeaderAction
    <2>2. \A v \in Q : currentTerm[v] < currentTerm[leader] + 1
      BY <2>1 DEF BecomeLeader, CanVoteForOplog
    <2>3. state' = [s_1 \in Server |-> IF s_1 = leader THEN Primary ELSE IF s_1 \in Q THEN Secondary ELSE state[s_1]]
      BY <2>1 DEF BecomeLeader
    <2>4. currentTerm' = [s_1 \in Server |-> IF s_1 \in Q THEN currentTerm[leader] + 1 ELSE currentTerm[s_1]]
      BY <2>1 DEF BecomeLeader
    \* Key quorum intersection lemma
    <2>5. \A Q1, Q2 \in Quorums(Server) : Q1 \cap Q2 # {}
      <3>. SUFFICES ASSUME NEW Q1 \in Quorums(Server), NEW Q2 \in Quorums(Server) PROVE Q1 \cap Q2 # {} OBVIOUS
      <3>1. Q1 \subseteq Server /\ Q2 \subseteq Server BY DEF Quorums
      <3>2. IsFiniteSet(Server) BY A0
      <3>3. IsFiniteSet(Q1) /\ IsFiniteSet(Q2) BY <3>1, <3>2, FS_Subset
      <3>4. Cardinality(Q1) * 2 > Cardinality(Server) /\ Cardinality(Q2) * 2 > Cardinality(Server) BY DEF Quorums
      <3>5. Cardinality(Server) \in Nat BY <3>2, FS_CardinalityType
      <3>6. Cardinality(Q1) \in Nat /\ Cardinality(Q2) \in Nat BY <3>3, FS_CardinalityType
      <3>7. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server) BY <3>4, <3>5, <3>6
      <3>. QED BY <3>1, <3>2, <3>7, FS_MajoritiesIntersect
    \* Case: both are the new leader
    <2>6. CASE s1 = leader /\ t1 = leader
      BY <2>6
    \* Case: s1 is new leader, t1 was existing primary
    <2>7. CASE s1 = leader /\ t1 # leader
      <3>1. state'[t1] = Primary /\ t1 # leader
        BY <2>7
      <3>2. t1 \notin Q
        BY <3>1, <2>3
      <3>3. state[t1] = Primary
        BY <3>1, <3>2, <2>3
      <3>4. currentTerm'[t1] = currentTerm[t1]
        BY <3>2, <2>4
      <3>5. leader \in Q
        BY <2>1 DEF BecomeLeader
      <3>6. currentTerm'[s1] = currentTerm[leader] + 1
        BY <2>7, <3>5, <2>4
      <3>7. currentTerm[t1] = currentTerm[leader] + 1
        BY <3>4, <3>6
      \* t1 was a primary, so has a quorum Qt where all terms >= currentTerm[t1]
      <3>8. PICK Qt \in Quorums(Server) : \A n \in Qt : currentTerm[n] >= currentTerm[t1]
        BY <3>3 DEF H_QuorumsSafeAtTerms
      \* Q and Qt intersect
      <3>9. Q \cap Qt # {}
        BY <2>5
      <3>10. PICK w \in Q \cap Qt : TRUE
        BY <3>9
      \* w is in Q so currentTerm[w] < currentTerm[leader]+1
      <3>11. currentTerm[w] < currentTerm[leader] + 1
        BY <3>10, <2>2
      \* w is in Qt so currentTerm[w] >= currentTerm[t1] = currentTerm[leader]+1
      <3>12. currentTerm[w] >= currentTerm[t1]
        BY <3>10, <3>8
      <3>13. currentTerm[w] >= currentTerm[leader] + 1
        BY <3>7, <3>12
      <3>14. FALSE
        BY <3>11, <3>13 DEF TypeOK, Terms
      <3>. QED BY <3>14
    \* Case: t1 is new leader, s1 was existing primary (symmetric)
    <2>8. CASE s1 # leader /\ t1 = leader
      <3>1. s1 \notin Q
        BY <2>8, <2>3
      <3>2. state[s1] = Primary
        BY <2>8, <3>1, <2>3
      <3>3. currentTerm'[s1] = currentTerm[s1]
        BY <3>1, <2>4
      <3>4. leader \in Q
        BY <2>1 DEF BecomeLeader
      <3>5. currentTerm'[t1] = currentTerm[leader] + 1
        BY <2>8, <3>4, <2>4
      <3>6. currentTerm[s1] = currentTerm[leader] + 1
        BY <3>3, <3>5
      <3>7. PICK Qs \in Quorums(Server) : \A n \in Qs : currentTerm[n] >= currentTerm[s1]
        BY <3>2 DEF H_QuorumsSafeAtTerms
      <3>8. Q \cap Qs # {}
        BY <2>5
      <3>9. PICK w \in Q \cap Qs : TRUE
        BY <3>8
      <3>10. currentTerm[w] < currentTerm[leader] + 1
        BY <3>9, <2>2
      <3>11. currentTerm[w] >= currentTerm[s1]
        BY <3>9, <3>7
      <3>12. currentTerm[w] >= currentTerm[leader] + 1
        BY <3>6, <3>11
      <3>13. FALSE
        BY <3>10, <3>12 DEF TypeOK, Terms
      <3>. QED BY <3>13
    \* Case: both were existing primaries (neither is new leader)
    <2>9. CASE s1 # leader /\ t1 # leader
      <3>1. s1 \notin Q /\ state[s1] = Primary
        BY <2>9, <2>3
      <3>2. t1 \notin Q /\ state[t1] = Primary
        BY <2>9, <2>3
      <3>3. currentTerm'[s1] = currentTerm[s1]
        BY <3>1, <2>4
      <3>4. currentTerm'[t1] = currentTerm[t1]
        BY <3>2, <2>4
      <3>5. currentTerm[s1] = currentTerm[t1]
        BY <3>3, <3>4
      <3>. QED BY <3>1, <3>2, <3>5 DEF H_OnePrimaryPerTerm
    <2>. QED BY <2>6, <2>7, <2>8, <2>9
  \* (H_OnePrimaryPerTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_OnePrimaryPerTerm /\ CommitEntryAction => H_OnePrimaryPerTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_OnePrimaryPerTerm
  \* (H_OnePrimaryPerTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_OnePrimaryPerTerm /\ UpdateTermsAction => H_OnePrimaryPerTerm'
    <2>. SUFFICES ASSUME TypeOK, H_OnePrimaryPerTerm,
                        NEW i \in Server, NEW j \in Server, UpdateTerms(i, j),
                        NEW s1 \in Server, NEW t1 \in Server,
                        state'[s1] = Primary, state'[t1] = Primary, currentTerm'[s1] = currentTerm'[t1]
         PROVE s1 = t1
      BY DEF H_OnePrimaryPerTerm, UpdateTermsAction
    <2>1. currentTerm[i] > currentTerm[j]
      BY DEF UpdateTerms, UpdateTermsExpr
    <2>2. currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
      BY DEF UpdateTerms, UpdateTermsExpr
    <2>3. state' = [state EXCEPT ![j] = Secondary]
      BY DEF UpdateTerms, UpdateTermsExpr
    \* Only j's state changes (to Secondary), so any Primary in state' was Primary in state (and is not j)
    <2>4. state[s1] = Primary /\ s1 # j
      BY <2>3 DEF TypeOK
    <2>5. state[t1] = Primary /\ t1 # j
      BY <2>3 DEF TypeOK
    <2>6. currentTerm'[s1] = currentTerm[s1]
      BY <2>2, <2>4 DEF TypeOK
    <2>7. currentTerm'[t1] = currentTerm[t1]
      BY <2>2, <2>5 DEF TypeOK
    <2>8. currentTerm[s1] = currentTerm[t1]
      BY <2>6, <2>7
    <2>. QED BY <2>4, <2>5, <2>8 DEF H_OnePrimaryPerTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_PrimaryHasOwnEntries
THEOREM L_2 == TypeOK /\ H_OnePrimaryPerTerm /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ Next => H_PrimaryHasOwnEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_PrimaryHasOwnEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_OnePrimaryPerTerm /\ H_PrimaryHasOwnEntries /\ ClientRequestAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,H_OnePrimaryPerTerm,ClientRequestAction,ClientRequest,H_PrimaryHasOwnEntries,InLog
  \* (H_PrimaryHasOwnEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryHasOwnEntries /\ GetEntriesAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryHasOwnEntries,InLog,Empty
  \* (H_PrimaryHasOwnEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryHasOwnEntries /\ RollbackEntriesAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryHasOwnEntries,InLog,CanRollback,LastTerm,Empty
  \* (H_PrimaryHasOwnEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryHasOwnEntries /\ BecomeLeaderAction => H_PrimaryHasOwnEntries'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm, H_PrimaryHasOwnEntries, BecomeLeaderAction
         PROVE H_PrimaryHasOwnEntries'
      OBVIOUS
    <2>1. PICK leader \in Server, Q \in Quorums(Server) : BecomeLeader(leader, Q)
      BY DEF BecomeLeaderAction
    <2>2. UNCHANGED <<log, immediatelyCommitted>>
      BY <2>1 DEF BecomeLeader
    <2>3. \A v \in Q : currentTerm[v] < currentTerm[leader] + 1
      BY <2>1 DEF BecomeLeader, CanVoteForOplog
    <2>4. state' = [s_1 \in Server |-> IF s_1 = leader THEN Primary ELSE IF s_1 \in Q THEN Secondary ELSE state[s_1]]
      BY <2>1 DEF BecomeLeader
    <2>5. currentTerm' = [s_1 \in Server |-> IF s_1 \in Q THEN currentTerm[leader] + 1 ELSE currentTerm[s_1]]
      BY <2>1 DEF BecomeLeader
    \* Quorum intersection
    <2>6. \A Q1, Q2 \in Quorums(Server) : Q1 \cap Q2 # {}
      <3>1. IsFiniteSet(Server) BY A0
      <3>2. SUFFICES ASSUME NEW Q1 \in Quorums(Server), NEW Q2 \in Quorums(Server) PROVE Q1 \cap Q2 # {} OBVIOUS
      <3>3. Q1 \subseteq Server /\ Q2 \subseteq Server BY DEF Quorums
      <3>4. IsFiniteSet(Q1) /\ IsFiniteSet(Q2) BY <3>1, <3>3, FS_Subset
      <3>5. Cardinality(Q1) * 2 > Cardinality(Server) /\ Cardinality(Q2) * 2 > Cardinality(Server) BY DEF Quorums
      <3>6. Cardinality(Server) \in Nat BY <3>1, FS_CardinalityType
      <3>7. Cardinality(Q1) \in Nat /\ Cardinality(Q2) \in Nat BY <3>4, FS_CardinalityType
      <3>8. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server) BY <3>5, <3>6, <3>7
      <3>. QED BY <3>1, <3>3, <3>8, FS_MajoritiesIntersect
    \* No server has entries at the new term (currentTerm[leader]+1) in the pre-state
    <2>7. \A s \in Server : \A k \in DOMAIN log[s] : log[s][k] # currentTerm[leader] + 1
      <3>. SUFFICES ASSUME NEW s \in Server, NEW k \in DOMAIN log[s], log[s][k] = currentTerm[leader] + 1 PROVE FALSE OBVIOUS
      <3>1. PICK Qe \in Quorums(Server) : \A n \in Qe : currentTerm[n] >= log[s][k]
        BY DEF H_LogEntryImpliesSafeAtTerm
      <3>2. \A n \in Qe : currentTerm[n] >= currentTerm[leader] + 1
        BY <3>1
      <3>3. Q \cap Qe # {}
        BY <2>6
      <3>4. PICK w \in Q \cap Qe : TRUE BY <3>3
      <3>5. currentTerm[w] < currentTerm[leader] + 1
        BY <3>4, <2>3
      <3>6. currentTerm[w] >= currentTerm[leader] + 1
        BY <3>4, <3>2
      <3>. QED BY <3>5, <3>6 DEF TypeOK, Terms
    \* For any primary i in the post-state: new leader case
    <2>8. \A j \in Server : \A k \in DOMAIN log'[j] : log'[j][k] # currentTerm'[leader]
      <3>1. leader \in Q BY <2>1 DEF BecomeLeader
      <3>2. currentTerm'[leader] = currentTerm[leader] + 1 BY <3>1, <2>5
      <3>. QED BY <3>2, <2>2, <2>7
    \* For any existing primary (not the new leader)
    <2>9. \A i \in Server : i # leader /\ state'[i] = Primary =>
          (\A j \in Server : \A k \in DOMAIN log'[j] : log'[j][k] = currentTerm'[i] =>
            (\E x \in DOMAIN log'[i] : x = k /\ log'[i][x] = log'[j][k]))
      <3>. SUFFICES ASSUME NEW i \in Server, i # leader, state'[i] = Primary
           PROVE \A j \in Server : \A k \in DOMAIN log'[j] : log'[j][k] = currentTerm'[i] =>
                 (\E x \in DOMAIN log'[i] : x = k /\ log'[i][x] = log'[j][k])
        OBVIOUS
      <3>1. i \notin Q /\ state[i] = Primary
        BY <2>4
      <3>2. currentTerm'[i] = currentTerm[i]
        BY <3>1, <2>5
      <3>. QED BY <2>2, <3>1, <3>2 DEF H_PrimaryHasOwnEntries, InLog
    <2>. QED BY <2>4, <2>8, <2>9 DEF H_PrimaryHasOwnEntries, InLog
  \* (H_PrimaryHasOwnEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryHasOwnEntries /\ CommitEntryAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryHasOwnEntries,InLog,ImmediatelyCommitted
  \* (H_PrimaryHasOwnEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryHasOwnEntries /\ UpdateTermsAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_PrimaryHasOwnEntries,InLog
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogMatching
THEOREM L_3 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ Next => H_LogMatching'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogMatching,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ ClientRequestAction => H_LogMatching' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_LogMatching,InLog
  \* (H_LogMatching,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ GetEntriesAction => H_LogMatching' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LogMatching,Empty
  \* (H_LogMatching,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LogMatching /\ RollbackEntriesAction => H_LogMatching' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LogMatching
  \* (H_LogMatching,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogMatching /\ BecomeLeaderAction => H_LogMatching' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogMatching
  \* (H_LogMatching,CommitEntryAction)
  <1>5. TypeOK /\ H_LogMatching /\ CommitEntryAction => H_LogMatching' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_LogMatching
  \* (H_LogMatching,UpdateTermsAction)
  <1>6. TypeOK /\ H_LogMatching /\ UpdateTermsAction => H_LogMatching' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LogMatching
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_PrimaryTermGTELogTerm
THEOREM L_4 == TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ Next => H_PrimaryTermGTELogTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_PrimaryTermGTELogTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ ClientRequestAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_PrimaryTermGTELogTerm,Terms
  \* (H_PrimaryTermGTELogTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryTermGTELogTerm /\ GetEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryTermGTELogTerm,Empty
  \* (H_PrimaryTermGTELogTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryTermGTELogTerm /\ RollbackEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryTermGTELogTerm,CanRollback,LastTerm,Empty
  \* (H_PrimaryTermGTELogTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ BecomeLeaderAction => H_PrimaryTermGTELogTerm'
    <2>. SUFFICES ASSUME TypeOK, H_LogEntryImpliesSafeAtTerm, H_PrimaryTermGTELogTerm, BecomeLeaderAction
         PROVE H_PrimaryTermGTELogTerm'
      OBVIOUS
    <2>1. PICK leader \in Server, Q \in Quorums(Server) : BecomeLeader(leader, Q)
      BY DEF BecomeLeaderAction
    <2>2. UNCHANGED <<log, immediatelyCommitted>>
      BY <2>1 DEF BecomeLeader
    <2>3. \A v \in Q : currentTerm[v] < currentTerm[leader] + 1
      BY <2>1 DEF BecomeLeader, CanVoteForOplog
    <2>4. state' = [s_1 \in Server |-> IF s_1 = leader THEN Primary ELSE IF s_1 \in Q THEN Secondary ELSE state[s_1]]
      BY <2>1 DEF BecomeLeader
    <2>5. currentTerm' = [s_1 \in Server |-> IF s_1 \in Q THEN currentTerm[leader] + 1 ELSE currentTerm[s_1]]
      BY <2>1 DEF BecomeLeader
    \* Quorum intersection
    <2>6. \A Q1, Q2 \in Quorums(Server) : Q1 \cap Q2 # {}
      <3>1. IsFiniteSet(Server) BY A0
      <3>2. SUFFICES ASSUME NEW Q1 \in Quorums(Server), NEW Q2 \in Quorums(Server) PROVE Q1 \cap Q2 # {} OBVIOUS
      <3>3. Q1 \subseteq Server /\ Q2 \subseteq Server BY DEF Quorums
      <3>4. IsFiniteSet(Q1) /\ IsFiniteSet(Q2) BY <3>1, <3>3, FS_Subset
      <3>5. Cardinality(Q1) * 2 > Cardinality(Server) /\ Cardinality(Q2) * 2 > Cardinality(Server) BY DEF Quorums
      <3>6. Cardinality(Server) \in Nat BY <3>1, FS_CardinalityType
      <3>7. Cardinality(Q1) \in Nat /\ Cardinality(Q2) \in Nat BY <3>4, FS_CardinalityType
      <3>8. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server) BY <3>5, <3>6, <3>7
      <3>. QED BY <3>1, <3>3, <3>8, FS_MajoritiesIntersect
    \* For existing primaries (not leader), invariant holds since currentTerm and log unchanged
    <2>7. \A s \in Server : s # leader /\ state'[s] = Primary =>
          (\A idx \in DOMAIN log'[s] : currentTerm'[s] >= log'[s][idx])
      BY <2>2, <2>4, <2>5 DEF H_PrimaryTermGTELogTerm
    \* For the new leader: all log entries have term < newTerm via quorum intersection
    <2>8. \A idx \in DOMAIN log'[leader] : currentTerm'[leader] >= log'[leader][idx]
      <3>1. leader \in Q BY <2>1 DEF BecomeLeader
      <3>2. currentTerm'[leader] = currentTerm[leader] + 1 BY <3>1, <2>5
      <3>3. log'[leader] = log[leader] BY <2>2
      <3>. SUFFICES ASSUME NEW idx \in DOMAIN log[leader]
           PROVE currentTerm[leader] + 1 >= log[leader][idx]
        BY <3>2, <3>3
      <3>4. PICK Qe \in Quorums(Server) : \A n \in Qe : currentTerm[n] >= log[leader][idx]
        BY DEF H_LogEntryImpliesSafeAtTerm
      <3>5. Q \cap Qe # {} BY <2>6
      <3>6. PICK w \in Q \cap Qe : TRUE BY <3>5
      <3>7. currentTerm[w] < currentTerm[leader] + 1 BY <3>6, <2>3
      <3>8. currentTerm[w] >= log[leader][idx] BY <3>6, <3>4
      <3>9. w \in Server BY <3>6, A4 DEF Quorums
      <3>10. currentTerm[w] \in Int BY <3>9 DEF TypeOK, Terms
      <3>11. log[leader][idx] \in Int BY DEF TypeOK, Terms
      <3>12. currentTerm[leader] \in Int BY DEF TypeOK, Terms
      <3>. QED BY <3>7, <3>8, <3>10, <3>11, <3>12
    <2>. QED BY <2>7, <2>8 DEF H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryTermGTELogTerm /\ CommitEntryAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryTermGTELogTerm,ImmediatelyCommitted,InLog
  \* (H_PrimaryTermGTELogTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryTermGTELogTerm /\ UpdateTermsAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_PrimaryTermGTELogTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_QuorumsSafeAtTerms
THEOREM L_5 == TypeOK /\ H_QuorumsSafeAtTerms /\ Next => H_QuorumsSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (H_QuorumsSafeAtTerms,ClientRequestAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ ClientRequestAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,GetEntriesAction)
  <1>2. TypeOK /\ H_QuorumsSafeAtTerms /\ GetEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,GetEntriesAction,GetEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,RollbackEntriesAction)
  <1>3. TypeOK /\ H_QuorumsSafeAtTerms /\ RollbackEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,BecomeLeaderAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ BecomeLeaderAction => H_QuorumsSafeAtTerms'
    <2>. SUFFICES ASSUME TypeOK, H_QuorumsSafeAtTerms, BecomeLeaderAction
         PROVE H_QuorumsSafeAtTerms'
      OBVIOUS
    <2>1. PICK leader \in Server, Q \in Quorums(Server) : BecomeLeader(leader, Q)
      BY DEF BecomeLeaderAction
    <2>2. currentTerm' = [s_1 \in Server |-> IF s_1 \in Q THEN currentTerm[leader] + 1 ELSE currentTerm[s_1]]
      BY <2>1 DEF BecomeLeader
    <2>3. state' = [s_1 \in Server |-> IF s_1 = leader THEN Primary ELSE IF s_1 \in Q THEN Secondary ELSE state[s_1]]
      BY <2>1 DEF BecomeLeader
    <2>4. leader \in Q
      BY <2>1 DEF BecomeLeader
    <2>5. \A v \in Q : currentTerm[v] < currentTerm[leader] + 1
      BY <2>1 DEF BecomeLeader, CanVoteForOplog
    <2>6. \A n \in Q : currentTerm'[n] = currentTerm[leader] + 1
      BY <2>2
    <2>7. Q \subseteq Server
      BY DEF Quorums
    \* Quorum intersection
    <2>8. \A Q1, Q2 \in Quorums(Server) : Q1 \cap Q2 # {}
      <3>1. IsFiniteSet(Server) BY A0
      <3>2. SUFFICES ASSUME NEW Q1 \in Quorums(Server), NEW Q2 \in Quorums(Server) PROVE Q1 \cap Q2 # {} OBVIOUS
      <3>3. Q1 \subseteq Server /\ Q2 \subseteq Server BY DEF Quorums
      <3>4. IsFiniteSet(Q1) /\ IsFiniteSet(Q2) BY <3>1, <3>3, FS_Subset
      <3>5. Cardinality(Q1) * 2 > Cardinality(Server) /\ Cardinality(Q2) * 2 > Cardinality(Server) BY DEF Quorums
      <3>6. Cardinality(Server) \in Nat BY <3>1, FS_CardinalityType
      <3>7. Cardinality(Q1) \in Nat /\ Cardinality(Q2) \in Nat BY <3>4, FS_CardinalityType
      <3>8. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server) BY <3>5, <3>6, <3>7
      <3>. QED BY <3>1, <3>3, <3>8, FS_MajoritiesIntersect
    \* For any existing primary s, currentTerm[leader]+1 >= currentTerm[s]
    <2>9. \A s \in Server : state[s] = Primary => currentTerm[leader] + 1 >= currentTerm[s]
      <3>. SUFFICES ASSUME NEW s \in Server, state[s] = Primary PROVE currentTerm[leader] + 1 >= currentTerm[s] OBVIOUS
      <3>1. PICK Qs \in Quorums(Server) : \A n \in Qs : currentTerm[n] >= currentTerm[s]
        BY DEF H_QuorumsSafeAtTerms
      <3>2. Q \cap Qs # {} BY <2>8
      <3>3. PICK w \in Q \cap Qs : TRUE BY <3>2
      <3>4. currentTerm[w] >= currentTerm[s] BY <3>3, <3>1
      <3>5. currentTerm[w] < currentTerm[leader] + 1 BY <3>3, <2>5
      <3>6. w \in Server BY <3>3, <2>7
      <3>. QED BY <3>4, <3>5, <3>6 DEF TypeOK, Terms
    \* Q witnesses the invariant for all primaries in post-state
    <2>10. \A s \in Server : state'[s] = Primary =>
           \A n \in Q : currentTerm'[n] >= currentTerm'[s]
      <3>. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary PROVE \A n \in Q : currentTerm'[n] >= currentTerm'[s] OBVIOUS
      <3>1. CASE s = leader
        BY <3>1, <2>4, <2>6 DEF TypeOK, Terms
      <3>2. CASE s # leader
        <4>1. s \notin Q /\ state[s] = Primary BY <3>2, <2>3
        <4>2. currentTerm'[s] = currentTerm[s] BY <4>1, <2>2
        <4>3. currentTerm[leader] + 1 >= currentTerm[s] BY <4>1, <2>9
        <4>. QED BY <4>2, <4>3, <2>6 DEF TypeOK, Terms
      <3>. QED BY <3>1, <3>2
    <2>. QED BY <2>10 DEF H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,CommitEntryAction)
  <1>5. TypeOK /\ H_QuorumsSafeAtTerms /\ CommitEntryAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,UpdateTermsAction)
  <1>6. TypeOK /\ H_QuorumsSafeAtTerms /\ UpdateTermsAction => H_QuorumsSafeAtTerms'
    <2>. SUFFICES ASSUME TypeOK, H_QuorumsSafeAtTerms,
                        NEW i \in Server, NEW j \in Server, UpdateTerms(i, j),
                        NEW s \in Server, state'[s] = Primary
         PROVE \E Qw \in Quorums(Server) : \A n \in Qw : currentTerm'[n] >= currentTerm'[s]
      BY DEF H_QuorumsSafeAtTerms, UpdateTermsAction
    <2>1. currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
      BY DEF UpdateTerms, UpdateTermsExpr
    <2>2. state' = [state EXCEPT ![j] = Secondary]
      BY DEF UpdateTerms, UpdateTermsExpr
    <2>3. s # j /\ state[s] = Primary
      BY <2>2 DEF TypeOK
    <2>4. currentTerm'[s] = currentTerm[s]
      BY <2>1, <2>3 DEF TypeOK
    <2>5. PICK Qs \in Quorums(Server) : \A n \in Qs : currentTerm[n] >= currentTerm[s]
      BY <2>3 DEF H_QuorumsSafeAtTerms
    <2>6. Qs \subseteq Server
      BY DEF Quorums
    <2>7. currentTerm[i] >= currentTerm[j]
      BY DEF UpdateTerms, UpdateTermsExpr
    <2>8. ASSUME NEW n \in Qs PROVE currentTerm'[n] >= currentTerm'[s]
      <3>1. n \in Server BY <2>6
      <3>2. CASE n = j
        BY <3>1, <3>2, <2>1, <2>4, <2>5, <2>7, <2>8 DEF TypeOK, Terms
      <3>3. CASE n # j
        BY <3>1, <3>3, <2>1, <2>4, <2>5, <2>8 DEF TypeOK, Terms
      <3>. QED BY <3>2, <3>3
    <2>. QED BY <2>8
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_UniformLogEntries
THEOREM L_6 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ H_UniformLogEntries /\ Next => H_UniformLogEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_UniformLogEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_UniformLogEntries /\ ClientRequestAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_PrimaryHasOwnEntries, H_UniformLogEntries,
                        NEW p \in Server, ClientRequest(p),
                        NEW s \in Server, NEW t \in Server,
                        NEW i \in DOMAIN log'[s],
                        \A j \in DOMAIN log'[s] : j < i => log'[s][j] # log'[s][i],
                        NEW k \in DOMAIN log'[t], log'[t][k] = log'[s][i]
         PROVE ~(k < i)
      BY DEF ClientRequestAction, H_UniformLogEntries
    <2>1. log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p])] BY DEF ClientRequest
    <2>2. state[p] = Primary BY DEF ClientRequest
    <2>3. \A j \in Server : \A idx \in DOMAIN log[j] : log[j][idx] = currentTerm[p] => idx \in DOMAIN log[p] /\ log[p][idx] = currentTerm[p]
      BY <2>2 DEF H_PrimaryHasOwnEntries, InLog
    \* Explicit Append properties
    <2>a. log'[p] = Append(log[p], currentTerm[p])
      BY <2>1 DEF TypeOK
    <2>b. \A srv \in Server : srv # p => log'[srv] = log[srv]
      BY <2>1 DEF TypeOK
    <2>c. DOMAIN log'[p] = 1..(Len(log[p])+1)
      BY <2>a DEF TypeOK
    <2>d. \A idx \in 1..Len(log[p]) : log'[p][idx] = log[p][idx]
      BY <2>a DEF TypeOK
    <2>e. log'[p][Len(log[p])+1] = currentTerm[p]
      BY <2>a DEF TypeOK
    <2>f. DOMAIN log[p] = 1..Len(log[p])
      BY DEF TypeOK
    <2>6. CASE s # p /\ t # p
      BY <2>b, <2>6 DEF H_UniformLogEntries
    <2>7. CASE s = p /\ t # p
      \* Explicit substitution of s=p into SUFFICES assumptions
      <3>a. log'[t][k] = log'[p][i] BY <2>7
      <3>b. \A j \in DOMAIN log'[p] : j < i => log'[p][j] # log'[p][i] BY <2>7
      <3>1. CASE i \in DOMAIN log[p]
        \* Old entry at index i in log[p]
        <4>1. log'[p][i] = log[p][i] BY <2>d, <2>f, <3>1
        <4>2. log'[t][k] = log[t][k] BY <2>b, <2>7
        <4>3. k \in DOMAIN log[t] BY <2>b, <2>7
        <4>4. log[t][k] = log[p][i]
          BY <3>a, <4>1, <4>2
        <4>5. \A j \in DOMAIN log[p] : j < i => log[p][j] # log[p][i]
          <5>. SUFFICES ASSUME NEW j \in DOMAIN log[p], j < i PROVE log[p][j] # log[p][i] OBVIOUS
          <5>1. j \in DOMAIN log'[p] BY <2>f, <2>c DEF TypeOK, Terms
          <5>2. log'[p][j] = log[p][j] BY <2>d, <2>f
          <5>3. log'[p][j] # log'[p][i] BY <3>b, <5>1
          <5>. QED BY <5>2, <5>3, <4>1
        <4>. QED BY <3>1, <4>4, <4>5, <4>3, <2>7 DEF H_UniformLogEntries
      <3>2. CASE i \notin DOMAIN log[p]
        \* New entry: i = Len(log[p])+1, log'[p][i] = currentTerm[p]
        \* Contradiction via uniqueness + H_PrimaryHasOwnEntries
        <4>1. i = Len(log[p]) + 1
          BY <2>c, <2>f, <3>2, <2>7 DEF TypeOK
        <4>2. log'[p][i] = currentTerm[p]
          BY <2>e, <4>1
        <4>3. log'[t][k] = log[t][k] BY <2>b, <2>7
        <4>4. k \in DOMAIN log[t] BY <2>b, <2>7
        <4>5. log[t][k] = currentTerm[p]
          BY <3>a, <4>2, <4>3
        <4>6. k \in DOMAIN log[p] /\ log[p][k] = currentTerm[p]
          BY <4>5, <4>4, <2>3, <2>7
        <4>7. log'[p][k] = log[p][k]
          BY <4>6, <2>d, <2>f
        <4>8. log'[p][k] = currentTerm[p]
          BY <4>7, <4>6
        <4>9. log'[p][k] = log'[p][i]
          BY <4>8, <4>2
        <4>10. k \in DOMAIN log'[p]
          BY <4>6, <2>f, <2>c DEF TypeOK, Terms
        <4>11. k < i => log'[p][k] # log'[p][i]
          BY <4>10, <3>b
        <4>. QED BY <4>9, <4>11
      <3>. QED BY <3>1, <3>2
    <2>8. CASE s # p /\ t = p
      \* Explicit substitution of t=p into SUFFICES assumptions
      <3>a. log'[s] = log[s] BY <2>b, <2>8
      <3>b. log'[p][k] = log'[s][i] BY <2>8
      <3>c. i \in DOMAIN log[s] BY <3>a
      <3>d. \A j \in DOMAIN log[s] : j < i => log[s][j] # log[s][i] BY <3>a, <2>8
      <3>2. CASE k \in DOMAIN log[p]
        \* Old entry in log[p] at k
        <4>1. log'[p][k] = log[p][k] BY <2>d, <2>f, <3>2
        <4>2. log[p][k] = log[s][i] BY <4>1, <3>b, <3>a
        <4>. QED BY <3>c, <4>2, <3>d, <3>2, <2>8 DEF H_UniformLogEntries
      <3>3. CASE k \notin DOMAIN log[p]
        \* k = Len(log[p])+1 (new entry). log'[p][k] = currentTerm[p].
        \* log[s][i] = currentTerm[p]. By H_PrimaryHasOwnEntries: i \in DOMAIN log[p].
        \* So i <= Len(log[p]) < k. ~(k < i).
        <4>1. k = Len(log[p]) + 1
          BY <2>c, <2>f, <3>3, <2>8 DEF TypeOK
        <4>2. log'[p][k] = currentTerm[p] BY <2>e, <4>1
        <4>3a. log'[s][i] = log[s][i] BY <3>a
        <4>3b. log'[s][i] = currentTerm[p] BY <3>b, <4>2
        <4>3. log[s][i] = currentTerm[p]
          BY <4>3a, <4>3b
        <4>4. i \in DOMAIN log[s] BY <3>c
        <4>5. i \in DOMAIN log[p]
          BY <4>3, <4>4, <2>3, <2>8
        <4>6. i \in 1..Len(log[p])
          BY <4>5, <2>f
        <4>. QED BY <4>1, <4>6 DEF TypeOK, Terms
      <3>. QED BY <3>2, <3>3
    <2>9. CASE s = p /\ t = p
      \* Explicit substitution: s=t=p, so log'[p][k] = log'[p][i]
      <3>a. log'[p][k] = log'[p][i] BY <2>9
      <3>b. \A j \in DOMAIN log'[p] : j < i => log'[p][j] # log'[p][i] BY <2>9
      <3>1. CASE i \in DOMAIN log[p] /\ k \in DOMAIN log[p]
        \* Both old entries
        <4>1. log'[p][i] = log[p][i] BY <2>d, <2>f, <3>1
        <4>2. log'[p][k] = log[p][k] BY <2>d, <2>f, <3>1
        <4>3. log[p][k] = log[p][i] BY <4>1, <4>2, <3>a
        <4>4. \A j \in DOMAIN log[p] : j < i => log[p][j] # log[p][i]
          <5>. SUFFICES ASSUME NEW j \in DOMAIN log[p], j < i PROVE log[p][j] # log[p][i] OBVIOUS
          <5>1. j \in DOMAIN log'[p] BY <2>f, <2>c DEF TypeOK, Terms
          <5>2. log'[p][j] = log[p][j] BY <2>d, <2>f
          <5>3. log'[p][j] # log'[p][i] BY <3>b, <5>1
          <5>. QED BY <5>2, <5>3, <4>1
        <4>. QED BY <3>1, <4>3, <4>4 DEF H_UniformLogEntries
      <3>2. CASE i \in DOMAIN log[p] /\ k \notin DOMAIN log[p]
        \* i old, k new. k = Len(log[p])+1 > i, so ~(k < i).
        <4>1. k = Len(log[p]) + 1
          BY <2>c, <2>f, <3>2, <2>9 DEF TypeOK
        <4>2. i \in 1..Len(log[p])
          BY <3>2, <2>f
        <4>. QED BY <4>1, <4>2 DEF TypeOK, Terms
      <3>3. CASE i \notin DOMAIN log[p] /\ k \in DOMAIN log[p]
        \* i new, k old. Contradiction via uniqueness.
        <4>1. log'[p][k] = log[p][k] BY <2>d, <2>f, <3>3
        <4>2. i = Len(log[p]) + 1
          BY <2>c, <2>f, <3>3, <2>9 DEF TypeOK
        <4>3. log'[p][i] = currentTerm[p] BY <2>e, <4>2
        <4>4. log'[p][k] = log'[p][i] BY <3>a
        <4>5. k \in DOMAIN log'[p]
          BY <3>3, <2>f, <2>c DEF TypeOK, Terms
        <4>6. k < i => log'[p][k] # log'[p][i]
          BY <4>5, <3>b
        <4>. QED BY <4>4, <4>6
      <3>4. CASE i \notin DOMAIN log[p] /\ k \notin DOMAIN log[p]
        \* Both new: i = k = Len(log[p])+1, so i = k and ~(k < i).
        <4>1. i = Len(log[p]) + 1
          BY <2>c, <2>f, <3>4, <2>9 DEF TypeOK
        <4>2. k = Len(log[p]) + 1
          BY <2>c, <2>f, <3>4, <2>9 DEF TypeOK
        <4>. QED BY <4>1, <4>2
      <3>. QED BY <3>1, <3>2, <3>3, <3>4
    <2>. QED BY <2>6, <2>7, <2>8, <2>9
  \* (H_UniformLogEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ H_UniformLogEntries /\ GetEntriesAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_LogMatching, H_UniformLogEntries,
                        NEW r \in Server, NEW sender \in Server, GetEntries(r, sender),
                        NEW s \in Server, NEW t \in Server,
                        NEW i \in DOMAIN log'[s],
                        \A j \in DOMAIN log'[s] : j < i => log'[s][j] # log'[s][i],
                        NEW k \in DOMAIN log'[t], log'[t][k] = log'[s][i]
         PROVE ~(k < i)
      BY DEF GetEntriesAction, H_UniformLogEntries
    \* Define newEntry for clarity
    <2>0. LET newEntryIndex == IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1
              newEntry == log[sender][newEntryIndex] IN
           log' = [log EXCEPT ![r] = Append(log[r], newEntry)]
      BY DEF GetEntries, Empty
    <2>1. log' = [log EXCEPT ![r] = Append(log[r], log[sender][IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1])]
      BY DEF GetEntries, Empty
    \* Explicit Append properties for log'[r]
    <2>a. log'[r] = Append(log[r], log[sender][IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1])
      BY <2>1 DEF TypeOK
    <2>b. \A srv \in Server : srv # r => log'[srv] = log[srv]
      BY <2>1 DEF TypeOK
    <2>c. DOMAIN log'[r] = 1..(Len(log[r])+1)
      BY <2>a DEF TypeOK
    <2>d. \A idx \in 1..Len(log[r]) : log'[r][idx] = log[r][idx]
      BY <2>a DEF TypeOK
    <2>e. log'[r][Len(log[r])+1] = log[sender][IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1]
      BY <2>a DEF TypeOK
    <2>f. DOMAIN log[r] = 1..Len(log[r])
      BY DEF TypeOK
    <2>g. Len(log[sender]) > Len(log[r])
      BY DEF GetEntries
    <2>h. ~Empty(log[r]) => log[sender][Len(log[r])] = log[r][Len(log[r])]
      BY DEF GetEntries, Empty
    \* Key: in both Empty and ~Empty cases, newEntryIndex = Len(log[r])+1 when not empty, = 1 when empty.
    \* But Len(log[r])+1 = 1 when Empty(log[r]) (Len=0). So newEntryIndex = Len(log[r])+1 always? No.
    \* When Empty: newEntryIndex=1, Len(log[r])=0, so Len(log[r])+1=1. Same!
    <2>i. (IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1) = Len(log[r]) + 1
      BY DEF TypeOK, Empty, Terms
    <2>5. CASE s # r /\ t # r
      BY <2>b, <2>5 DEF H_UniformLogEntries
    <2>6. CASE s = r /\ t # r
      \* Explicit substitution of s=r
      <3>a. log'[t][k] = log'[r][i] BY <2>6
      <3>b. \A j \in DOMAIN log'[r] : j < i => log'[r][j] # log'[r][i] BY <2>6
      <3>c. log'[t][k] = log[t][k] BY <2>b, <2>6
      <3>d. k \in DOMAIN log[t] BY <2>b, <2>6
      <3>1. CASE i \in DOMAIN log[r]
        \* Old entry, use pre-state invariant
        <4>1. log'[r][i] = log[r][i] BY <2>d, <2>f, <3>1
        <4>2. log[t][k] = log[r][i] BY <3>a, <4>1, <3>c
        <4>3. \A j \in DOMAIN log[r] : j < i => log[r][j] # log[r][i]
          <5>. SUFFICES ASSUME NEW j \in DOMAIN log[r], j < i PROVE log[r][j] # log[r][i] OBVIOUS
          <5>1. j \in DOMAIN log'[r] BY <2>f, <2>c DEF TypeOK, Terms
          <5>2. log'[r][j] = log[r][j] BY <2>d, <2>f
          <5>3. log'[r][j] # log'[r][i] BY <3>b, <5>1
          <5>. QED BY <5>2, <5>3, <4>1
        <4>. QED BY <3>1, <4>2, <4>3, <3>d, <2>6 DEF H_UniformLogEntries
      <3>2. CASE i \notin DOMAIN log[r]
        \* New entry at Len(log[r])+1.
        <4>1. i = Len(log[r]) + 1
          BY <2>c, <2>f, <3>2, <2>6 DEF TypeOK
        <4>2. log'[r][i] = log[sender][Len(log[r]) + 1]
          BY <2>e, <4>1, <2>i
        \* Use H_UniformLogEntries on sender's log.
        \* First establish uniqueness of log[sender][Len(log[r])+1] in sender's log.
        <4>3. Len(log[r]) + 1 \in DOMAIN log[sender]
          BY <2>g DEF TypeOK, Terms
        <4>4. \A j \in DOMAIN log[sender] : j < Len(log[r]) + 1 => log[sender][j] # log[sender][Len(log[r]) + 1]
          \* For j < Len(log[r])+1, j \in DOMAIN log[r]. log[r][j] = log[sender][j] by H_LogMatching.
          \* And log[r][j] = log'[r][j] # log'[r][i] = log[sender][Len(log[r])+1].
          <5>. SUFFICES ASSUME NEW j2 \in DOMAIN log[sender], j2 < Len(log[r]) + 1
               PROVE log[sender][j2] # log[sender][Len(log[r]) + 1]
            OBVIOUS
          <5>1. j2 \in 1..Len(log[r])
            BY DEF TypeOK, Terms
          <5>2. j2 \in DOMAIN log[r]
            BY <5>1, <2>f
          <5>3. log'[r][j2] = log[r][j2]
            BY <2>d, <5>1
          <5>4. j2 \in DOMAIN log'[r]
            BY <5>1, <2>c DEF TypeOK, Terms
          <5>5. log'[r][j2] # log'[r][i]
            BY <3>b, <5>4, <4>1 DEF TypeOK, Terms
          <5>6. log[r][j2] # log[sender][Len(log[r]) + 1]
            BY <5>3, <5>5, <4>2
          \* Now need: log[sender][j2] = log[r][j2] (from H_LogMatching)
          <5>7. CASE Empty(log[r])
            \* Len(log[r])=0, j2 < 1, contradicts j2 >= 1
            BY <5>7, <5>1 DEF Empty, TypeOK, Terms
          <5>8. CASE ~Empty(log[r])
            \* By logOk + H_LogMatching: SubSeq(log[r],1,Len(log[r])) = SubSeq(log[sender],1,Len(log[r]))
            <6>1. log[sender][Len(log[r])] = log[r][Len(log[r])]
              BY <2>h, <5>8
            <6>2. Len(log[r]) \in DOMAIN log[r]
              BY <5>8 DEF Empty, TypeOK
            <6>3. Len(log[r]) \in DOMAIN log[sender]
              BY <2>g DEF TypeOK, Terms
            <6>4a. log[r][Len(log[r])] = log[sender][Len(log[r])]
              BY <6>1
            <6>4b. \E j3 \in DOMAIN log[sender] : Len(log[r]) = j3 /\ log[r][Len(log[r])] = log[sender][j3]
              BY <6>3, <6>4a
            <6>4. SubSeq(log[r], 1, Len(log[r])) = SubSeq(log[sender], 1, Len(log[r]))
              BY <6>4b, <6>2 DEF H_LogMatching
            <6>5. log[sender][j2] = log[r][j2]
              BY <6>4, <5>1, <5>2 DEF TypeOK
            <6>. QED BY <6>5, <5>6
          <5>. QED BY <5>7, <5>8
        <4>5. log[t][k] = log[sender][Len(log[r]) + 1]
          BY <3>a, <4>2, <3>c
        \* Apply H_UniformLogEntries on sender
        <4>. QED BY <4>3, <4>4, <4>5, <3>d, <4>1 DEF H_UniformLogEntries
      <3>. QED BY <3>1, <3>2
    <2>7. CASE s # r /\ t = r
      \* Explicit substitution of t=r
      <3>a. log'[s] = log[s] BY <2>b, <2>7
      <3>b. log'[r][k] = log'[s][i] BY <2>7
      <3>c. i \in DOMAIN log[s] BY <3>a
      <3>d. \A j \in DOMAIN log[s] : j < i => log[s][j] # log[s][i] BY <3>a, <2>7
      <3>1. CASE k \in DOMAIN log[r]
        \* Old entry at k
        <4>1. log'[r][k] = log[r][k] BY <2>d, <2>f, <3>1
        <4>2. log[r][k] = log[s][i] BY <4>1, <3>b, <3>a
        <4>. QED BY <3>c, <4>2, <3>d, <3>1, <2>7 DEF H_UniformLogEntries
      <3>2. CASE k \notin DOMAIN log[r]
        \* New entry at k = Len(log[r])+1
        <4>1. k = Len(log[r]) + 1
          BY <2>c, <2>f, <3>2, <2>7 DEF TypeOK
        <4>2. log'[r][k] = log[sender][Len(log[r]) + 1]
          BY <2>e, <4>1, <2>i
        <4>3a. log'[s][i] = log[s][i] BY <3>a
        <4>3b. log'[s][i] = log[sender][Len(log[r]) + 1]
          BY <3>b, <4>2
        <4>3. log[s][i] = log[sender][Len(log[r]) + 1]
          BY <4>3a, <4>3b
        \* Apply H_UniformLogEntries with s=s, i=i, t=sender to get ~(Len(log[r])+1 < i) i.e. ~(k < i)
        <4>4. Len(log[r]) + 1 \in DOMAIN log[sender]
          BY <2>g DEF TypeOK, Terms
        <4>. QED BY <3>c, <3>d, <4>3, <4>4, <4>1 DEF H_UniformLogEntries
      <3>. QED BY <3>1, <3>2
    <2>8. CASE s = r /\ t = r
      \* Both s and t are r
      <3>a. log'[r][k] = log'[r][i] BY <2>8
      <3>b. \A j \in DOMAIN log'[r] : j < i => log'[r][j] # log'[r][i] BY <2>8
      <3>1. CASE i \in DOMAIN log[r] /\ k \in DOMAIN log[r]
        <4>1. log'[r][i] = log[r][i] BY <2>d, <2>f, <3>1
        <4>2. log'[r][k] = log[r][k] BY <2>d, <2>f, <3>1
        <4>3. log[r][k] = log[r][i] BY <4>1, <4>2, <3>a
        <4>4. \A j \in DOMAIN log[r] : j < i => log[r][j] # log[r][i]
          <5>. SUFFICES ASSUME NEW j \in DOMAIN log[r], j < i PROVE log[r][j] # log[r][i] OBVIOUS
          <5>1. j \in DOMAIN log'[r] BY <2>f, <2>c DEF TypeOK, Terms
          <5>2. log'[r][j] = log[r][j] BY <2>d, <2>f
          <5>3. log'[r][j] # log'[r][i] BY <3>b, <5>1
          <5>. QED BY <5>2, <5>3, <4>1
        <4>. QED BY <3>1, <4>3, <4>4 DEF H_UniformLogEntries
      <3>2. CASE i \in DOMAIN log[r] /\ k \notin DOMAIN log[r]
        <4>1. k = Len(log[r]) + 1 BY <2>c, <2>f, <3>2, <2>8 DEF TypeOK
        <4>2. i \in 1..Len(log[r]) BY <3>2, <2>f
        <4>. QED BY <4>1, <4>2 DEF TypeOK, Terms
      <3>3. CASE i \notin DOMAIN log[r] /\ k \in DOMAIN log[r]
        \* Contradiction via uniqueness
        <4>1. k \in DOMAIN log'[r] BY <3>3, <2>f, <2>c DEF TypeOK, Terms
        <4>2. k < i => log'[r][k] # log'[r][i] BY <4>1, <3>b
        <4>. QED BY <3>a, <4>2
      <3>4. CASE i \notin DOMAIN log[r] /\ k \notin DOMAIN log[r]
        <4>1. i = Len(log[r]) + 1 BY <2>c, <2>f, <3>4, <2>8 DEF TypeOK
        <4>2. k = Len(log[r]) + 1 BY <2>c, <2>f, <3>4, <2>8 DEF TypeOK
        <4>. QED BY <4>1, <4>2
      <3>. QED BY <3>1, <3>2, <3>3, <3>4
    <2>. QED BY <2>5, <2>6, <2>7, <2>8
  \* (H_UniformLogEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_UniformLogEntries /\ RollbackEntriesAction => H_UniformLogEntries'
    <2>. SUFFICES ASSUME TypeOK, H_UniformLogEntries,
                        NEW r \in Server, NEW j \in Server, RollbackEntries(r, j),
                        NEW s \in Server, NEW t \in Server,
                        NEW i \in DOMAIN log'[s],
                        \A jj \in DOMAIN log'[s] : jj < i => log'[s][jj] # log'[s][i],
                        NEW k \in DOMAIN log'[t], log'[t][k] = log'[s][i]
         PROVE ~(k < i)
      BY DEF RollbackEntriesAction, H_UniformLogEntries
    <2>1. log' = [log EXCEPT ![r] = SubSeq(log[r], 1, Len(log[r])-1)]
      BY DEF RollbackEntries
    <2>b. \A srv \in Server : srv # r => log'[srv] = log[srv]
      BY <2>1 DEF TypeOK
    \* SubSeq preserves all entries at their indices
    <2>c. \A idx \in DOMAIN log'[r] : idx \in DOMAIN log[r] /\ log'[r][idx] = log[r][idx]
      BY <2>1 DEF TypeOK
    \* DOMAIN log'[r] \subseteq DOMAIN log[r], and any j < i where i \in DOMAIN log'[r]
    \* is also in DOMAIN log'[r] (since DOMAIN log'[r] = 1..Len(log[r])-1)
    <2>d. \A idx \in DOMAIN log'[r] : \A jj \in DOMAIN log[r] : jj < idx => jj \in DOMAIN log'[r]
      BY <2>1 DEF TypeOK
    <2>3. CASE s # r /\ t # r
      BY <2>b, <2>3 DEF H_UniformLogEntries
    <2>5. CASE s = r /\ t # r
      \* Explicit substitution of s=r
      <3>a. log'[t][k] = log'[r][i] BY <2>5
      <3>b. \A jj \in DOMAIN log'[r] : jj < i => log'[r][jj] # log'[r][i] BY <2>5
      <3>c. log'[t][k] = log[t][k] BY <2>b, <2>5
      <3>d. k \in DOMAIN log[t] BY <2>b, <2>5
      \* log'[r][i] = log[r][i] since i is in the SubSeq prefix
      <3>1. i \in DOMAIN log[r] /\ log'[r][i] = log[r][i] BY <2>c, <2>5
      <3>2. log[t][k] = log[r][i] BY <3>a, <3>1, <3>c
      <3>3. \A jj \in DOMAIN log[r] : jj < i => log[r][jj] # log[r][i]
        <4>. SUFFICES ASSUME NEW jj \in DOMAIN log[r], jj < i PROVE log[r][jj] # log[r][i] OBVIOUS
        <4>0. i \in DOMAIN log'[r] BY <2>5
        <4>1. jj \in DOMAIN log'[r]
          BY <2>d, <4>0
        <4>2. log'[r][jj] = log[r][jj] BY <2>c, <4>1
        <4>3. log'[r][jj] # log'[r][i] BY <3>b, <4>1
        <4>. QED BY <4>2, <4>3, <3>1
      <3>. QED BY <3>1, <3>2, <3>3, <3>d, <2>5 DEF H_UniformLogEntries
    <2>6. CASE s # r /\ t = r
      \* Explicit substitution of t=r
      <3>a. log'[s] = log[s] BY <2>b, <2>6
      <3>b. log'[r][k] = log'[s][i] BY <2>6
      <3>c. i \in DOMAIN log[s] BY <3>a
      <3>d. \A jj \in DOMAIN log[s] : jj < i => log[s][jj] # log[s][i] BY <3>a, <2>6
      \* k \in DOMAIN log'[r] => k \in DOMAIN log[r] and log'[r][k] = log[r][k]
      <3>1. k \in DOMAIN log[r] /\ log'[r][k] = log[r][k] BY <2>c, <2>6
      <3>2. log[r][k] = log[s][i] BY <3>1, <3>b, <3>a
      <3>. QED BY <3>c, <3>2, <3>d, <3>1, <2>6 DEF H_UniformLogEntries
    <2>7. CASE s = r /\ t = r
      <3>a. log'[r][k] = log'[r][i] BY <2>7
      <3>b. \A jj \in DOMAIN log'[r] : jj < i => log'[r][jj] # log'[r][i] BY <2>7
      <3>1. i \in DOMAIN log[r] /\ log'[r][i] = log[r][i] BY <2>c, <2>7
      <3>2. k \in DOMAIN log[r] /\ log'[r][k] = log[r][k] BY <2>c, <2>7
      <3>3. log[r][k] = log[r][i] BY <3>1, <3>2, <3>a
      <3>4. \A jj \in DOMAIN log[r] : jj < i => log[r][jj] # log[r][i]
        <4>. SUFFICES ASSUME NEW jj \in DOMAIN log[r], jj < i PROVE log[r][jj] # log[r][i] OBVIOUS
        <4>1. i \in DOMAIN log'[r] BY <2>7
        <4>2. jj \in DOMAIN log'[r]
          BY <2>d, <4>1
        <4>3. log'[r][jj] = log[r][jj] BY <2>c, <4>2
        <4>4. log'[r][jj] # log'[r][i] BY <3>b, <4>2
        <4>. QED BY <4>3, <4>4, <3>1
      <3>. QED BY <3>1, <3>2, <3>3, <3>4 DEF H_UniformLogEntries
    <2>. QED BY <2>3, <2>5, <2>6, <2>7
  \* (H_UniformLogEntries,BecomeLeaderAction)
  <1>4. TypeOK /\ H_UniformLogEntries /\ BecomeLeaderAction => H_UniformLogEntries' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_UniformLogEntries
  \* (H_UniformLogEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_UniformLogEntries /\ CommitEntryAction => H_UniformLogEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_UniformLogEntries
  \* (H_UniformLogEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_UniformLogEntries /\ UpdateTermsAction => H_UniformLogEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_UniformLogEntries
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_TermsMonotonic
THEOREM L_7 == TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ Next => H_TermsMonotonic'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_TermsMonotonic,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ ClientRequestAction => H_TermsMonotonic'
    <2>. SUFFICES ASSUME TypeOK, H_PrimaryTermGTELogTerm, H_TermsMonotonic,
                        NEW p \in Server, ClientRequest(p),
                        NEW sv \in Server, NEW ii \in DOMAIN log'[sv], NEW jj \in DOMAIN log'[sv],
                        ii <= jj
         PROVE log'[sv][ii] <= log'[sv][jj]
      BY DEF ClientRequestAction, H_TermsMonotonic
    <2>1. log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p])] BY DEF ClientRequest
    <2>a. log'[p] = Append(log[p], currentTerm[p]) BY <2>1 DEF TypeOK
    <2>b. \A idx \in 1..Len(log[p]) : log'[p][idx] = log[p][idx] BY <2>a DEF TypeOK
    <2>c. log'[p][Len(log[p])+1] = currentTerm[p] BY <2>a DEF TypeOK
    <2>d. DOMAIN log[p] = 1..Len(log[p]) BY DEF TypeOK
    <2>e. DOMAIN log'[p] = 1..(Len(log[p])+1) BY <2>a DEF TypeOK
    <2>2. CASE sv # p
      BY <2>1, <2>2 DEF TypeOK, H_TermsMonotonic
    <2>3. CASE sv = p
      <3>1. CASE ii \in DOMAIN log[p] /\ jj \in DOMAIN log[p]
        BY <2>b, <2>d, <3>1, <2>3 DEF H_TermsMonotonic
      <3>2. CASE ii \in DOMAIN log[p] /\ jj \notin DOMAIN log[p]
        \* jj = Len(log[p])+1, log'[p][jj] = currentTerm[p]
        \* log'[p][ii] = log[p][ii] <= currentTerm[p] by H_PrimaryTermGTELogTerm
        <4>1. jj = Len(log[p]) + 1 BY <2>e, <2>d, <3>2, <2>3 DEF TypeOK
        <4>2. log'[p][jj] = currentTerm[p] BY <2>c, <4>1
        <4>3. log'[p][ii] = log[p][ii] BY <2>b, <2>d, <3>2
        <4>4. state[p] = Primary BY DEF ClientRequest
        <4>5. log[p][ii] <= currentTerm[p]
          BY <4>4, <3>2 DEF H_PrimaryTermGTELogTerm
        <4>6. log'[sv][ii] <= log'[sv][jj]
          BY <4>2, <4>3, <4>5, <2>3 DEF TypeOK, Terms
        <4>. QED BY <4>6
      <3>3. CASE ii \notin DOMAIN log[p] /\ jj \notin DOMAIN log[p]
        \* Both equal Len(log[p])+1, so ii = jj
        <4>1. ii = Len(log[p]) + 1 BY <2>e, <2>d, <3>3, <2>3 DEF TypeOK
        <4>2. jj = Len(log[p]) + 1 BY <2>e, <2>d, <3>3, <2>3 DEF TypeOK
        <4>3. ii = jj BY <4>1, <4>2
        <4>4. log'[sv][ii] = log'[sv][jj] BY <4>3
        <4>5. log'[p][ii] = currentTerm[p] BY <2>c, <4>1
        <4>6. currentTerm[p] \in Nat BY DEF TypeOK, Terms
        <4>. QED BY <4>4, <4>5, <4>6, <2>3
      <3>4. CASE ii \notin DOMAIN log[p] /\ jj \in DOMAIN log[p]
        \* ii = Len(log[p])+1 > jj, contradicts ii <= jj
        <4>1. ii = Len(log[p]) + 1 BY <2>e, <2>d, <3>4, <2>3 DEF TypeOK
        <4>2. jj \in 1..Len(log[p]) BY <3>4, <2>d
        <4>. QED BY <4>1, <4>2 DEF TypeOK, Terms
      <3>. QED BY <3>1, <3>2, <3>3, <3>4
    <2>. QED BY <2>2, <2>3
  \* (H_TermsMonotonic,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ GetEntriesAction => H_TermsMonotonic'
    <2>. SUFFICES ASSUME TypeOK, H_TermsMonotonic,
                        NEW r \in Server, NEW sender \in Server, GetEntries(r, sender),
                        NEW sv \in Server, NEW ii \in DOMAIN log'[sv], NEW jj \in DOMAIN log'[sv],
                        ii <= jj
         PROVE log'[sv][ii] <= log'[sv][jj]
      BY DEF GetEntriesAction, H_TermsMonotonic
    <2>1. log' = [log EXCEPT ![r] = Append(log[r], log[sender][IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1])]
      BY DEF GetEntries, Empty
    <2>a. log'[r] = Append(log[r], log[sender][IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1])
      BY <2>1 DEF TypeOK
    <2>b. \A idx \in 1..Len(log[r]) : log'[r][idx] = log[r][idx] BY <2>a DEF TypeOK
    <2>c. DOMAIN log[r] = 1..Len(log[r]) BY DEF TypeOK
    <2>d. DOMAIN log'[r] = 1..(Len(log[r])+1) BY <2>a DEF TypeOK
    <2>e. (IF Empty(log[r]) THEN 1 ELSE Len(log[r]) + 1) = Len(log[r]) + 1
      BY DEF TypeOK, Empty, Terms
    <2>f. log'[r][Len(log[r])+1] = log[sender][Len(log[r]) + 1]
      BY <2>a, <2>e DEF TypeOK
    <2>g. Len(log[sender]) > Len(log[r]) BY DEF GetEntries
    <2>h. ~Empty(log[r]) => log[sender][Len(log[r])] = log[r][Len(log[r])]
      BY DEF GetEntries, Empty
    <2>2. CASE sv # r
      BY <2>1, <2>2 DEF TypeOK, H_TermsMonotonic
    <2>3. CASE sv = r
      <3>1. CASE ii \in DOMAIN log[r] /\ jj \in DOMAIN log[r]
        BY <2>b, <2>c, <3>1, <2>3 DEF H_TermsMonotonic
      <3>2. CASE ii \in DOMAIN log[r] /\ jj \notin DOMAIN log[r]
        \* jj = Len(log[r])+1 = new entry. log'[r][jj] = log[sender][Len(log[r])+1].
        \* Need: log[r][ii] <= log[sender][Len(log[r])+1].
        \* By H_TermsMonotonic on r: log[r][ii] <= log[r][Len(log[r])] (ii <= Len(log[r])).
        \* By logOk + H_TermsMonotonic on sender: log[r][Len(log[r])] = log[sender][Len(log[r])] <= log[sender][Len(log[r])+1].
        <4>1. jj = Len(log[r]) + 1 BY <2>d, <2>c, <3>2, <2>3 DEF TypeOK
        <4>2. log'[r][jj] = log[sender][Len(log[r]) + 1] BY <2>f, <4>1
        <4>3. log'[r][ii] = log[r][ii] BY <2>b, <2>c, <3>2
        <4>4. CASE Empty(log[r])
          \* log[r] is empty, but ii \in DOMAIN log[r] contradicts Empty
          BY <4>4, <3>2 DEF Empty, TypeOK
        <4>5. CASE ~Empty(log[r])
          <5>1. Len(log[r]) \in DOMAIN log[r]
            BY <4>5 DEF Empty, TypeOK
          <5>2. ii \in 1..Len(log[r]) BY <3>2, <2>c
          <5>3. log[r][ii] <= log[r][Len(log[r])]
            BY <5>2, <5>1 DEF H_TermsMonotonic, TypeOK, Terms
          <5>4. log[sender][Len(log[r])] = log[r][Len(log[r])]
            BY <2>h, <4>5
          <5>5. Len(log[r]) >= 1
            BY <4>5 DEF Empty, TypeOK, Terms
          <5>6. Len(log[r]) \in DOMAIN log[sender]
            BY <5>5, <2>g DEF TypeOK, Terms
          <5>7. Len(log[r]) + 1 \in DOMAIN log[sender]
            BY <2>g DEF TypeOK, Terms
          <5>8. log[sender][Len(log[r])] <= log[sender][Len(log[r]) + 1]
            BY <5>6, <5>7 DEF H_TermsMonotonic, TypeOK, Terms
          <5>9. log[r][Len(log[r])] <= log[sender][Len(log[r]) + 1]
            BY <5>4, <5>8 DEF TypeOK, Terms
          <5>10. log[r][ii] \in Nat /\ log[r][Len(log[r])] \in Nat /\ log[sender][Len(log[r]) + 1] \in Nat
            BY <5>2, <5>1, <5>7 DEF TypeOK, Terms
          <5>11. log[r][ii] <= log[sender][Len(log[r]) + 1]
            BY <5>3, <5>9, <5>10
          <5>12. log'[sv][ii] <= log'[sv][jj]
            BY <4>3, <4>2, <5>11, <2>3 DEF TypeOK, Terms
          <5>. QED BY <5>12
        <4>. QED BY <4>4, <4>5
      <3>3. CASE ii \notin DOMAIN log[r] /\ jj \notin DOMAIN log[r]
        <4>1. ii = Len(log[r]) + 1 BY <2>d, <2>c, <3>3, <2>3 DEF TypeOK
        <4>2. jj = Len(log[r]) + 1 BY <2>d, <2>c, <3>3, <2>3 DEF TypeOK
        <4>3. ii = jj BY <4>1, <4>2
        <4>4. log'[sv][ii] = log'[sv][jj] BY <4>3
        <4>5. log'[r][ii] = log[sender][Len(log[r]) + 1] BY <2>f, <4>1
        <4>6. log[sender][Len(log[r]) + 1] \in Nat
          BY <2>g DEF TypeOK, Terms
        <4>. QED BY <4>4, <4>5, <4>6, <2>3
      <3>4. CASE ii \notin DOMAIN log[r] /\ jj \in DOMAIN log[r]
        <4>1. ii = Len(log[r]) + 1 BY <2>d, <2>c, <3>4, <2>3 DEF TypeOK
        <4>2. jj \in 1..Len(log[r]) BY <3>4, <2>c
        <4>. QED BY <4>1, <4>2 DEF TypeOK, Terms
      <3>. QED BY <3>1, <3>2, <3>3, <3>4
    <2>. QED BY <2>2, <2>3
  \* (H_TermsMonotonic,RollbackEntriesAction)
  <1>3. TypeOK /\ H_TermsMonotonic /\ RollbackEntriesAction => H_TermsMonotonic' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_TermsMonotonic
  \* (H_TermsMonotonic,BecomeLeaderAction)
  <1>4. TypeOK /\ H_TermsMonotonic /\ BecomeLeaderAction => H_TermsMonotonic' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_TermsMonotonic
  \* (H_TermsMonotonic,CommitEntryAction)
  <1>5. TypeOK /\ H_TermsMonotonic /\ CommitEntryAction => H_TermsMonotonic' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_TermsMonotonic
  \* (H_TermsMonotonic,UpdateTermsAction)
  <1>6. TypeOK /\ H_TermsMonotonic /\ UpdateTermsAction => H_TermsMonotonic' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_TermsMonotonic
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogEntryImpliesSafeAtTerm
THEOREM L_8 == TypeOK /\ H_QuorumsSafeAtTerms /\ H_LogEntryImpliesSafeAtTerm /\ Next => H_LogEntryImpliesSafeAtTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogEntryImpliesSafeAtTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ H_LogEntryImpliesSafeAtTerm /\ ClientRequestAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,H_QuorumsSafeAtTerms,ClientRequestAction,ClientRequest,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ GetEntriesAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ RollbackEntriesAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ BecomeLeaderAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ CommitEntryAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_LogEntryImpliesSafeAtTerm
  \* (H_LogEntryImpliesSafeAtTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ UpdateTermsAction => H_LogEntryImpliesSafeAtTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LogEntryImpliesSafeAtTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LeaderCompleteness
THEOREM L_9 == TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ Next => H_LeaderCompleteness'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LeaderCompleteness,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ ClientRequestAction => H_LeaderCompleteness' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_LeaderCompleteness
  \* (H_LeaderCompleteness,GetEntriesAction)
  <1>2. TypeOK /\ H_LeaderCompleteness /\ GetEntriesAction => H_LeaderCompleteness' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LeaderCompleteness
  \* (H_LeaderCompleteness,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LeaderCompleteness /\ RollbackEntriesAction => H_LeaderCompleteness' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LeaderCompleteness
  \* (H_LeaderCompleteness,BecomeLeaderAction)
  <1>4. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_CommittedEntryIsOnQuorum /\ H_LaterLogsHaveEarlierCommitted /\ H_LeaderCompleteness /\ BecomeLeaderAction => H_LeaderCompleteness' BY DEF TypeOK,H_TermsMonotonic,H_UniformLogEntries,H_CommittedEntryIsOnQuorum,H_LaterLogsHaveEarlierCommitted,BecomeLeaderAction,BecomeLeader,H_LeaderCompleteness
  \* (H_LeaderCompleteness,CommitEntryAction)
  <1>5. TypeOK /\ H_TermsMonotonic /\ H_QuorumsSafeAtTerms /\ H_LeaderCompleteness /\ CommitEntryAction => H_LeaderCompleteness' BY DEF TypeOK,H_TermsMonotonic,H_QuorumsSafeAtTerms,CommitEntryAction,CommitEntry,H_LeaderCompleteness
  \* (H_LeaderCompleteness,UpdateTermsAction)
  <1>6. TypeOK /\ H_LeaderCompleteness /\ UpdateTermsAction => H_LeaderCompleteness' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LeaderCompleteness
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LaterLogsHaveEarlierCommitted
THEOREM L_10 == TypeOK /\ H_LeaderCompleteness /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ Next => H_LaterLogsHaveEarlierCommitted'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LaterLogsHaveEarlierCommitted,ClientRequestAction)
  <1>1. TypeOK /\ H_LeaderCompleteness /\ H_LaterLogsHaveEarlierCommitted /\ ClientRequestAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_LeaderCompleteness,ClientRequestAction,ClientRequest,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ H_UniformLogEntries /\ H_LaterLogsHaveEarlierCommitted /\ GetEntriesAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_TermsMonotonic,H_UniformLogEntries,GetEntriesAction,GetEntries,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ RollbackEntriesAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ BecomeLeaderAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,CommitEntryAction)
  <1>5. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_LaterLogsHaveEarlierCommitted /\ CommitEntryAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,H_LogEntryImpliesSafeAtTerm,CommitEntryAction,CommitEntry,H_LaterLogsHaveEarlierCommitted
  \* (H_LaterLogsHaveEarlierCommitted,UpdateTermsAction)
  <1>6. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ UpdateTermsAction => H_LaterLogsHaveEarlierCommitted' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_LaterLogsHaveEarlierCommitted
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_CommittedEntryIsOnQuorum
THEOREM L_11 == TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ Next => H_CommittedEntryIsOnQuorum'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_CommittedEntryIsOnQuorum,ClientRequestAction)
  <1>1. TypeOK /\ H_CommittedEntryIsOnQuorum /\ ClientRequestAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,GetEntriesAction)
  <1>2. TypeOK /\ H_CommittedEntryIsOnQuorum /\ GetEntriesAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,GetEntriesAction,GetEntries,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,RollbackEntriesAction)
  <1>3. TypeOK /\ H_LaterLogsHaveEarlierCommitted /\ H_CommittedEntryIsOnQuorum /\ RollbackEntriesAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,H_LaterLogsHaveEarlierCommitted,RollbackEntriesAction,RollbackEntries,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,BecomeLeaderAction)
  <1>4. TypeOK /\ H_CommittedEntryIsOnQuorum /\ BecomeLeaderAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ CommitEntryAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_CommittedEntryIsOnQuorum
  \* (H_CommittedEntryIsOnQuorum,UpdateTermsAction)
  <1>6. TypeOK /\ H_CommittedEntryIsOnQuorum /\ UpdateTermsAction => H_CommittedEntryIsOnQuorum' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_CommittedEntryIsOnQuorum
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** H_StateMachineSafety
THEOREM L_12 == TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ Next => H_StateMachineSafety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_StateMachineSafety,ClientRequestAction)
  <1>1. TypeOK /\ H_StateMachineSafety /\ ClientRequestAction => H_StateMachineSafety' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_StateMachineSafety
  \* (H_StateMachineSafety,GetEntriesAction)
  <1>2. TypeOK /\ H_StateMachineSafety /\ GetEntriesAction => H_StateMachineSafety' BY DEF TypeOK,GetEntriesAction,GetEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,RollbackEntriesAction)
  <1>3. TypeOK /\ H_StateMachineSafety /\ RollbackEntriesAction => H_StateMachineSafety' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_StateMachineSafety
  \* (H_StateMachineSafety,BecomeLeaderAction)
  <1>4. TypeOK /\ H_StateMachineSafety /\ BecomeLeaderAction => H_StateMachineSafety' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_StateMachineSafety
  \* (H_StateMachineSafety,CommitEntryAction)
  <1>5. TypeOK /\ H_CommittedEntryIsOnQuorum /\ H_StateMachineSafety /\ CommitEntryAction => H_StateMachineSafety' BY DEF TypeOK,H_CommittedEntryIsOnQuorum,CommitEntryAction,CommitEntry,H_StateMachineSafety
  \* (H_StateMachineSafety,UpdateTermsAction)
  <1>6. TypeOK /\ H_StateMachineSafety /\ UpdateTermsAction => H_StateMachineSafety' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_StateMachineSafety
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => H_OnePrimaryPerTerm BY DEF Init, H_OnePrimaryPerTerm, IndGlobal
    <1>2. Init => H_PrimaryHasOwnEntries BY DEF Init, H_PrimaryHasOwnEntries, IndGlobal
    <1>3. Init => H_LogMatching BY DEF Init, H_LogMatching, IndGlobal
    <1>4. Init => H_PrimaryTermGTELogTerm BY DEF Init, H_PrimaryTermGTELogTerm, IndGlobal
    <1>5. Init => H_QuorumsSafeAtTerms BY DEF Init, H_QuorumsSafeAtTerms, IndGlobal
    <1>6. Init => H_UniformLogEntries BY DEF Init, H_UniformLogEntries, IndGlobal
    <1>7. Init => H_TermsMonotonic BY DEF Init, H_TermsMonotonic, IndGlobal
    <1>8. Init => H_LogEntryImpliesSafeAtTerm BY DEF Init, H_LogEntryImpliesSafeAtTerm, IndGlobal
    <1>9. Init => H_LeaderCompleteness BY DEF Init, H_LeaderCompleteness, IndGlobal
    <1>10. Init => H_LaterLogsHaveEarlierCommitted BY DEF Init, H_LaterLogsHaveEarlierCommitted, IndGlobal
    <1>11. Init => H_CommittedEntryIsOnQuorum BY DEF Init, H_CommittedEntryIsOnQuorum, IndGlobal
    <1>12. Init => H_StateMachineSafety BY DEF Init, H_StateMachineSafety, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal

====