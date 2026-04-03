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
    \* For any primary i in the post-state, H_PrimaryHasOwnEntries' holds
    <2>8. SUFFICES ASSUME NEW i \in Server, NEW j \in Server, state'[i] = Primary
         PROVE ~(\E k \in DOMAIN log'[j] : log'[j][k] = currentTerm'[i] /\ ~InLog(<<k, log'[j][k]>>, i)')
      BY DEF H_PrimaryHasOwnEntries
    <2>9. CASE i = leader
      \* New leader has term currentTerm[leader]+1, no entries at that term exist
      BY <2>2, <2>5, <2>7, <2>9 DEF InLog
    <2>10. CASE i # leader
      \* Existing primary: state'[i] = state[i] = Primary (i not in Q since members become Secondary)
      <3>1. i \notin Q /\ state[i] = Primary
        BY <2>10, <2>4
      <3>2. currentTerm'[i] = currentTerm[i]
        BY <3>1, <2>5
      <3>. QED BY <2>2, <3>1, <3>2 DEF H_PrimaryHasOwnEntries, InLog
    <2>. QED BY <2>9, <2>10
  \* (H_PrimaryHasOwnEntries,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryHasOwnEntries /\ CommitEntryAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryHasOwnEntries,InLog,ImmediatelyCommitted
  \* (H_PrimaryHasOwnEntries,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryHasOwnEntries /\ UpdateTermsAction => H_PrimaryHasOwnEntries' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,UpdateTermsExpr,H_PrimaryHasOwnEntries,InLog
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_LogMatching
THEOREM L_3 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ Next => H_LogMatching'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_LogMatching,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ ClientRequestAction => H_LogMatching' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_LogMatching
  \* (H_LogMatching,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ GetEntriesAction => H_LogMatching' BY DEF TypeOK,GetEntriesAction,GetEntries,H_LogMatching
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
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_PrimaryTermGTELogTerm,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ ClientRequestAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,GetEntriesAction)
  <1>2. TypeOK /\ H_PrimaryTermGTELogTerm /\ GetEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,GetEntriesAction,GetEntries,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,RollbackEntriesAction)
  <1>3. TypeOK /\ H_PrimaryTermGTELogTerm /\ RollbackEntriesAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,BecomeLeaderAction)
  <1>4. TypeOK /\ H_LogEntryImpliesSafeAtTerm /\ H_PrimaryTermGTELogTerm /\ BecomeLeaderAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,H_LogEntryImpliesSafeAtTerm,BecomeLeaderAction,BecomeLeader,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,CommitEntryAction)
  <1>5. TypeOK /\ H_PrimaryTermGTELogTerm /\ CommitEntryAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_PrimaryTermGTELogTerm
  \* (H_PrimaryTermGTELogTerm,UpdateTermsAction)
  <1>6. TypeOK /\ H_PrimaryTermGTELogTerm /\ UpdateTermsAction => H_PrimaryTermGTELogTerm' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_PrimaryTermGTELogTerm
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_QuorumsSafeAtTerms
THEOREM L_5 == TypeOK /\ H_QuorumsSafeAtTerms /\ Next => H_QuorumsSafeAtTerms'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_QuorumsSafeAtTerms,ClientRequestAction)
  <1>1. TypeOK /\ H_QuorumsSafeAtTerms /\ ClientRequestAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,GetEntriesAction)
  <1>2. TypeOK /\ H_QuorumsSafeAtTerms /\ GetEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,GetEntriesAction,GetEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,RollbackEntriesAction)
  <1>3. TypeOK /\ H_QuorumsSafeAtTerms /\ RollbackEntriesAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,BecomeLeaderAction)
  <1>4. TypeOK /\ H_QuorumsSafeAtTerms /\ BecomeLeaderAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,CommitEntryAction)
  <1>5. TypeOK /\ H_QuorumsSafeAtTerms /\ CommitEntryAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,CommitEntryAction,CommitEntry,H_QuorumsSafeAtTerms
  \* (H_QuorumsSafeAtTerms,UpdateTermsAction)
  <1>6. TypeOK /\ H_QuorumsSafeAtTerms /\ UpdateTermsAction => H_QuorumsSafeAtTerms' BY DEF TypeOK,UpdateTermsAction,UpdateTerms,H_QuorumsSafeAtTerms
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** H_UniformLogEntries
THEOREM L_6 == TypeOK /\ H_PrimaryHasOwnEntries /\ H_LogMatching /\ H_UniformLogEntries /\ Next => H_UniformLogEntries'
  <1>. USE A0,A1,A2,A3,A4,A5,A6
  \* (H_UniformLogEntries,ClientRequestAction)
  <1>1. TypeOK /\ H_PrimaryHasOwnEntries /\ H_UniformLogEntries /\ ClientRequestAction => H_UniformLogEntries' BY DEF TypeOK,H_PrimaryHasOwnEntries,ClientRequestAction,ClientRequest,H_UniformLogEntries
  \* (H_UniformLogEntries,GetEntriesAction)
  <1>2. TypeOK /\ H_LogMatching /\ H_UniformLogEntries /\ GetEntriesAction => H_UniformLogEntries' BY DEF TypeOK,H_LogMatching,GetEntriesAction,GetEntries,H_UniformLogEntries
  \* (H_UniformLogEntries,RollbackEntriesAction)
  <1>3. TypeOK /\ H_UniformLogEntries /\ RollbackEntriesAction => H_UniformLogEntries' BY DEF TypeOK,RollbackEntriesAction,RollbackEntries,H_UniformLogEntries
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
  <1>1. TypeOK /\ H_PrimaryTermGTELogTerm /\ H_TermsMonotonic /\ ClientRequestAction => H_TermsMonotonic' BY DEF TypeOK,H_PrimaryTermGTELogTerm,ClientRequestAction,ClientRequest,H_TermsMonotonic
  \* (H_TermsMonotonic,GetEntriesAction)
  <1>2. TypeOK /\ H_TermsMonotonic /\ GetEntriesAction => H_TermsMonotonic' BY DEF TypeOK,GetEntriesAction,GetEntries,H_TermsMonotonic
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