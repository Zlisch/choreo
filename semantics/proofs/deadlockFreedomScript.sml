open preamble choreoUtilsTheory chorSemTheory chorPropsTheory

val _ = new_theory "deadlockFreedom";

Theorem chor_deadlock_freedom:
  ∀c s.
   no_undefined_vars (s,c) ∧
   no_self_comunication c  ∧
   not_finish c
   ⇒ ∃τ l s' c'. trans (s,c) (τ,l) (s',c')
Proof
  Cases
  \\ rw [] \\ rw []
  (* IfThen *)
  >- (rename1 ‘IfThen v’
     \\ Cases_on `FLOOKUP s' (v,s) = SOME (BoolV T)`
     >- metis_tac [trans_if_true]
     \\ Cases_on `FLOOKUP s' (v,s)`
      >- fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘x = (BoolV F)’
      >- metis_tac [trans_if_false]
      >> metis_tac [not_BoolV, trans_if_exn])
  (* Communication *)
  >- (rename1 ‘Com p1 v1 p2 v2’
     \\ `∃d. FLOOKUP s' (v1,p1) = SOME d`
             by fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘d’ 
     \\ metis_tac [trans_com, trans_com_exn, no_self_comunication_def])
  (* Let *)
  >- (rename1 ‘Let v p e c’
      \\ `EVERY IS_SOME (MAP (FLOOKUP s') (MAP (λv. (v,p)) l))`
          by (last_assum mp_tac \\  rpt (pop_assum (K ALL_TAC))
              \\ rw [no_undefined_vars_def,free_variables_def]
              \\ Induct_on `l` \\ rw [IS_SOME_EXISTS,FLOOKUP_DEF])
      \\ metis_tac [trans_letval])
  (* Selection *)
  >- metis_tac [trans_sel,no_self_comunication_def]
  (* Recursion *)
  \\ metis_tac [trans_fix]
QED

Theorem chor_progress:
Proof

val _ = export_theory ()
