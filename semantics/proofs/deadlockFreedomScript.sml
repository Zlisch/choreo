open preamble choreoUtilsTheory chorSemTheory chorPropsTheory chorTypePropsTheory chorTypeTheory

open typeSNTheory                                

val _ = new_theory "deadlockFreedom";

(*
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
*)

Definition chorEnvsn_def:
  chorEnvsn Γ Δ = (∀ p. envsn (localise Γ p) (localise Δ p))
End

Theorem richerLang_localise_sn:
  chorEnvsn Γ s ∧ typecheck (localise Γ p) e t ⇒
  (∃ cl v. eval_exp cl (localise s p) e = Value v ∧ sn_v t v) ∨
  ∃ cl exn. eval_exp cl (localise s p) e = Exn exn
Proof
  rw[] >>
  drule sn_lemma >> strip_tac >>
  fs[sn_e_def, chorEnvsn_def] >>
  ‘envsn (localise Γ p) (localise s p)’ by metis_tac[] >>
  metis_tac[envsn_g_submap, DRESTRICT_SUBMAP, sn_exec_def]        
QED

Theorem chor_progress:
  ∀c s. chorTypecheckOK Γ Θ c ∧ chorEnvtype Γ s ∧ chorEnvsn Γ s ⇒
        ∃τ l s' c'. trans (s,c) (τ,l) (s',c') ∨ ¬not_finish c
Proof
  Cases >> rw [] >> rw [] >>
  drule chortype_no_self_communication >> 
  drule chortype_no_undefined_vars >> rpt strip_tac >>
  first_x_assum $ drule_all_then $ strip_assume_tac >~
  [‘IfThen v p c1 c2’, ‘(s, IfThen v p c1 c2)’]
  >- (Cases_on `FLOOKUP s (v,p) = SOME (BoolV T)`
     >- metis_tac [trans_if_true]
     \\ Cases_on `FLOOKUP s (v,p)`
      >- fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘x = (BoolV F)’
      >- metis_tac [trans_if_false]
      >> metis_tac [not_BoolV, trans_if_exn]) >~
  [‘Com p1 v1 p2 v2’]
  >- (rename1 ‘Com p1 v1 p2 v2’
     \\ `∃d. FLOOKUP s' (v1,p1) = SOME d`
             by fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
      >> Cases_on ‘d’ 
      \\ metis_tac [trans_com, trans_com_exn, no_self_comunication_def]) >~
  [‘Let v p e c’, ‘(s,Let v p e c)’]
  >- (gvs[chorTypecheckOK_let_thm] >> drule richerLang_localise_sn >> strip_tac >>      
      ‘free_vars e ⊆ FDOM (localise s p)’ by metis_tac[typecheck_env_fv, chortype_localise_fdom, SUBSET_TRANS] >>
      first_x_assum $ drule_all_then $ strip_assume_tac >>
      metis_tac[trans_letval, trans_letexn])
  (* Selection *)
  >- metis_tac [trans_sel,no_self_comunication_def]
  (* Recursion *)
  \\ metis_tac [trans_fix]
QED

val _ = export_theory ()
