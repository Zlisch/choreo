open preamble choreoUtilsTheory chorSemTheory chorPropsTheory chorTypePropsTheory chorTypeTheory chorLangTheory

open typeSNTheory envSemTheory richerLangTheory

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

Theorem chor_progress_lemma:
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

Theorem chor_progress:
  ∀ c. chorTypecheckOK FEMPTY Θ c ⇒
         ∃τ l s' c'. trans (FEMPTY,c) (τ,l) (s',c') ∨ ¬not_finish c
Proof
  rpt strip_tac >> drule_then irule chor_progress_lemma >>
  rw[chorEnvsn_def, chorEnvtype_def, envsn_def, envtype_def, localise_def]
QED

(*
Theorem richerLang_localise_closed_sn:
  typecheck FEMPTY e t ⇒
  (∃ cl v. eval_exp cl FEMPTY e = Value v ∧ sn_v t v) ∨
  ∃ cl exn. eval_exp cl FEMPTY e = Exn exn
Proof
  rw[] >> drule sn_lemma >> fs[sn_e_def, sn_exec_def] >>
  disch_then $ qspecl_then [‘FEMPTY’] assume_tac >> rw[envsn_def]
QED
*)

Theorem envsn_localise_update:
  envsn (localise Γ p) (localise s p) ∧ sn_v ty v ⇒
  ∀ vn p'. envsn (localise (Γ |+ ((vn,p'),ty)) p) (localise (s |+ ((vn,p'),v)) p)
Proof
  rw[envsn_def, localise_flookup] >> Cases_on ‘(s',p) = (vn, p')’ >>
  gvs[FLOOKUP_SIMP] >> metis_tac[]
QED

Theorem chorEnvsn_update:
  chorEnvsn Γ s ∧ sn_v ty v ⇒
  ∀vn p. chorEnvsn (Γ |+ ((vn,p),ty)) (s |+ ((vn,p),v))
Proof
  rw[chorEnvsn_def] >> metis_tac[envsn_localise_update]
QED

Theorem fmap_update_duplicate:
  FLOOKUP f x = SOME v ⇒ f = f |+ (x,v)
Proof
  rw[] >> irule (iffRL fmap_eq_flookup) >>
  metis_tac[FLOOKUP_SIMP]
QED

Theorem chorEnvsn_state_update:
  FLOOKUP Γ (vn,p) = SOME ty ∧ sn_v ty v ∧ chorEnvsn Γ s ⇒
  chorEnvsn Γ (s |+ ((vn,p), v))
Proof
  metis_tac[chorEnvsn_def, chorEnvsn_update, fmap_update_duplicate]
QED

Theorem chorEnvtype_state_update:
  FLOOKUP Γ (vn,p) = SOME ty ∧ value_type v ty ∧ chorEnvtype Γ s ⇒
  chorEnvtype Γ (s |+ ((vn,p), v))
Proof
  metis_tac[chorEnvtype_def, chortype_update, fmap_update_duplicate]
QED

Theorem chor_preservation:
  ∀ c Θ Γ s. not_finish c ∧ chorEnvsn Γ s ∧ chorEnvtype Γ s ∧ chorTypecheckOK Γ Θ c ⇒
             (∃ s' c' τ l Γ'. trans (s,c) (τ,l) (s',c') ⇒
                              chorEnvtype Γ' s' ∧ chorEnvsn Γ' s' ∧ chorTypecheckOK Γ' Θ c')
Proof
  metis_tac[chorEnvtype_def, envtype_def, localise_flookup, valuetype_EQ_strT, trans_com, value_type_StrV, sn_v_strT, chorEnvsn_state_update, chorEnvtype_state_update]
QED

(*
Theorem chor_preservation2:
  ∀ c Θ. not_finish c ∧ chorTypecheckOK FEMPTY Θ c ⇒
         (∃ s' c' τ l Γ. trans (FEMPTY,c) (τ,l) (s',c') ⇒
                         chorTypecheckOK Γ Θ c')
Proof
  Cases >> rw [] >> gvs[chorTypecheckOK_if_thm, chorTypecheckOK_com_thm, chorTypecheckOK_let_thm, chorTypecheckOK_sel_thm, chorTypecheckOK_fix_thm, chorEnvtype_def, envtype_def, localise_flookup, localise_fempty] >~
  [‘(_,Sel p1 b p2 c)’]
  >- (drule_all trans_sel >> disch_then $ qspecl_then [‘s’, ‘b’, ‘c’] assume_tac >>
      metis_tac[]) >~
  [‘(_,Let v p e c)’]
  >- (drule richerLang_localise_closed_sn >> strip_tac >>
      metis_tac[EMPTY_SUBSET, trans_letval, trans_letexn, localise_fempty, FDOM_FEMPTY, typecheck_env_fv, SUBSET_EMPTY, chorTypecheckOK_nil]) >~
  [‘Fix dn c’]
  >> (‘trans (s,Fix dn c) (LFix,[]) (s,dsubst c dn (Fix dn c))’ by simp[trans_fix] >>
      ‘∃ Γ. chorTypecheckOK Γ Θ (dsubst c dn (Fix dn c))’ suffices_by metis_tac[] >>
      Cases_on ‘c’ >> rw[dsubst_def]
      >- simp[chorTypecheckOK_nil]
      >> cheat free_vars_mono
     )     
QED
*)

val _ = export_theory ()
