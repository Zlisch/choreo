open HolKernel Parse boolLib bossLib;

open richerLangTheory envSemTheory optionTheory finite_mapTheory pred_setTheory;

val _ = new_theory "typeSN";


Definition sn_v_def:
  (sn_v intT (IntV n) ⇔ T) ∧
  (sn_v strT (StrV s) ⇔ T) ∧
  (sn_v boolT (BoolV b) ⇔ T) ∧
  (sn_v (fnT t1 t2) (Clos s e E) ⇔
     ∀ v. sn_v t1 v ⇒ (∃ cl v'. eval_exp cl (E|+(s,v)) e = Value v' ∧ sn_v t2 v') ∨
                      (∃ cl exn. eval_exp cl (E|+(s,v)) e = Exn exn)) ∧
  (sn_v (pairT t1 t2) (PairV v1 v2) ⇔ sn_v t1 v1 ∧ sn_v t2 v2) ∧
  (sn_v (sumT t1 t2) (SumLV v) ⇔ sn_v t1 v) ∧
  (sn_v (sumT t1 t2) (SumRV v) ⇔ sn_v t2 v) ∧
  (sn_v _ _ ⇔ F)
Termination
  WF_REL_TAC ‘inv_image (measure type_size) FST’
End

Definition envsn_def:
  envsn G E ⇔
    ∀ s ty. FLOOKUP G s = SOME ty ⇒ (∃ v. FLOOKUP E s = SOME v ∧ sn_v ty v)
End

Definition sn_exec_def:
  sn_exec t E e ⇔ (∃ cl v. eval_exp cl E e = Value v ∧ sn_v t v) ∨
                  ∃ cl exn. eval_exp cl E e = Exn exn
End

Definition sn_e_def:
  sn_e G t e ⇔
    ∀ E. envsn (DRESTRICT G (FDOM E)) E ⇒ sn_exec t E e
End

Theorem envsn_g_domsub_update:
  envsn (G \\ s) E ∧ sn_v ty v ⇒
  envsn (G |+ (s,ty)) (E |+ (s,v))
Proof
  rw[envsn_def] >> Cases_on ‘s = s'’ >> gvs[FLOOKUP_SIMP, DOMSUB_FLOOKUP_NEQ]
QED

(* utils *)
Theorem drestrict_insert_domsub:
  DRESTRICT G (s INSERT A) \\ s = DRESTRICT G (A DIFF {s})
Proof
  rw[DRESTRICT_DOMSUB, DELETE_DEF, INSERT_DIFF]
QED

Theorem envsn_g_submap:
  envsn G E ∧ G' ⊑ G ⇒ envsn G' E
Proof
  rw[envsn_def, SUBMAP_FLOOKUP_EQN]
QED

Theorem envsn_drestrict_submap:
  envsn (DRESTRICT G (FDOM E)) E ∧ E' ⊑ E ⇒
  envsn (DRESTRICT G (FDOM E')) E'
Proof
  rw[envsn_def] >>
  ‘DRESTRICT G (FDOM E') ⊑ DRESTRICT G (FDOM E)’ by rw[SUBMAP_FDOM_SUBSET, DRESTRICT_SUBSET_SUBMAP] >>
  ‘FLOOKUP (DRESTRICT G (FDOM E)) s = SOME ty’ by gvs[SUBMAP_FLOOKUP_EQN] >>
  first_x_assum $ drule_all_then $ strip_assume_tac >>
  ‘s ∈ FDOM E'’ by gvs[FLOOKUP_DEF, IN_INTER, FDOM_DRESTRICT] >>
  metis_tac[FLOOKUP_DEF, SUBMAP_FLOOKUP_EQN]
QED

Theorem sn_lemma:
  (* ∀ G e t. typecheck G e t ∧ free_vars e = FDOM G ⇒ sn_e G t e *)
  ∀ G e t. typecheck G e t ⇒ sn_e G t e
Proof
  Induct_on ‘typecheck’ >> rw[sn_e_def, sn_v_def, eval_exp_def] >> gvs[AllCaseEqs(), PULL_EXISTS, result_bind_eq_value, sn_exec_def] >> rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >~
  [‘Fn s e’, ‘fnT dt rt’]
  >- (rw[eval_exp_def] >> simp[sn_v_def] >> rpt strip_tac >> first_x_assum irule >>
      simp[FLOOKUP_SIMP] >> rw[AllCaseEqs()] >> irule envsn_g_domsub_update >>
     )

                                                                                     
        
  Induct_on ‘typecheck’ >> rw[sn_e_def, envtype_sn_def, sn_v_def, eval_exp_def] >> gvs[AllCaseEqs(), PULL_EXISTS, result_bind_eq_value, sn_exec_def] >> rpt (first_x_assum $ drule_all_then $ strip_assume_tac)
  >- (rw[eval_exp_def])
  >- (rw[eval_exp_def] >> DISJ1_TAC >> qexists ‘(cl+cl'+ cl'')’ >> rpt (dxrule clock_value_increment) >>
      simp[] >> Cases_on ‘v''’ >> gvs[sn_v_def, AllCaseEqs()] >> metis_tac[])

  >~ (rw[eval_exp_def] >> DISJ2_TAC >> qexists ‘cl''’ >> simp[]) >~
  [‘If gd tb eb’, ‘eval_exp gc E gd = Value gv’,
   ‘eval_exp tc E tb = Exn exn’, ‘eval_exp ec E eb = Value ev’]
  >- (Cases_on ‘gv’ >> gvs[sn_v_def] >> rename [‘Value (BoolV bv)’] >>
      Cases_on ‘bv’
      >- (disj2_tac >> qexists ‘gc+tc’ >> rpt (dxrule clock_value_increment) >> rpt (dxrule clock_exn_increment) >> rw[eval_exp_def])
      >> (disj1_tac >> qexists ‘gc+ec’ >> rpt (dxrule clock_value_increment) >> rw[eval_exp_def])) >~
  [‘BinOp bop e1 e2’, ‘eval_exp c1 E e1 = Value v1’, ‘eval_exp c2 E e2 = Value v2’]
  >- ( Cases_on ‘eval_bop bop v1 v2’
       >- (disj1_tac >> rw[eval_exp_def] >> qexists ‘c1+c2’ >> rpt (dxrule clock_value_increment) >> rw[])) >~
  [‘Fn s e’, ‘fnT dt rt’]
  >- (rw[eval_exp_def] >> simp[sn_v_def] >> rpt strip_tac >> first_x_assum irule >>
      simp[FLOOKUP_SIMP] >> rw[AllCaseEqs()]
      >- (rename [‘FLOOKUP G s2 = SOME ty’] >>
      ‘s2 ∈ FDOM G’ by metis_tac[flookup_thm] >>
      ‘s2 ∈ free_vars e’ by ASM_SET_TAC [] >>
      metis_tac[])
      >> ASM_SET_TAC [])
QED

(*
Theorem sn_v_value_type:
  ∀ ty v. sn_v ty v ⇒ value_type v ty
Proof
  (* recInduct sn_v_ind >> simp[sn_v_def] >> rw[] >>
  irule value_type_FnV >> *)
  cheat
QED

Theorem envtype_sn_envtype:
  envtype_sn G E ⇒ envtype G E
Proof
  metis_tac[envtype_sn_def, envtype_def, sn_v_value_type]
QED
*)

        
val _ = export_theory();

