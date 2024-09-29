open HolKernel Parse boolLib bossLib chorSemTheory chorLangTheory richerLangTheory valueTheory envSemTheory chorPropsTheory chorTypeTheory finite_mapTheory pred_setTheory

val _ = new_theory "chorTypeProps";

Theorem chortype_localise_fdom:
  ∀ p. chorEnvtype Γ Δ ⇒ FDOM (localise Γ p) ⊆ FDOM (localise Δ p)
Proof
  rw[chorEnvtype_def, envtype_fdom]
QED

Theorem chortype_fdom_subset:
  chorEnvtype Γ Δ ⇒ FDOM Γ ⊆ FDOM Δ
Proof
  rw[chortype_localise_fdom, localise_fdom_subset]
QED

Theorem chortype_update:
  chorEnvtype Γ Δ ∧ value_type v ty ⇒
  ∀ vn p. chorEnvtype (Γ |+ ((vn,p), ty)) (Δ |+ ((vn,p), v))
Proof
  rw[chorEnvtype_def] >>
  ‘envtype (localise Γ p' |+ (vn, ty)) (localise Δ p' |+ (vn, v))’ by metis_tac[envtype_update] >> Cases_on ‘p' = p’
  >- gvs[localise_update_eqn]
  >> metis_tac[localise_update_neq]
QED

Theorem type_has_exp:
  ∀ G ty. ∃ e. typecheck G e ty
Proof
  Induct_on ‘ty’ >> rw[] >~
  [‘pairT t1 t2’]
  >- (irule_at Any typecheck_Binop >> metis_tac[boptype_rules])
  >> metis_tac[typecheck_rules, uoptype_rules]
QED

Theorem type_has_value:
  ∀ ty. ∃ v. value_type v ty
Proof
  Induct >~
  [‘fnT aty bty’]
  >- (irule_at Any value_type_FnV >>
      ‘∃ e. typecheck (FEMPTY |+ (s,aty)) e bty’ by metis_tac[type_has_exp] >>
      first_assum $ irule_at Any >> simp[])
  >> metis_tac[value_type_rules]
QED

Theorem chortype_no_undefined_vars:
  ∀ Γ Θ Δ. chorTypecheckOK Γ Θ c ∧ chorEnvtype Γ Δ ⇒
  no_undefined_vars (Δ, c)
Proof
  Induct_on ‘chorTypecheckOK’ >> rw[no_undefined_vars_def, free_variables_def, Once chorTypecheckOK_cases, FLOOKUP_DEF]
  >- metis_tac[chortype_fdom_subset, SUBSET_DEF]
  >- ASM_SET_TAC []
  >- metis_tac[chortype_fdom_subset, SUBSET_DEF]
  >- metis_tac[typecheck_no_undefined_vars, subset_fdom_localise_state, chortype_localise_fdom, SUBSET_TRANS]
  >> (‘∃ val. value_type val ety’ by simp[type_has_value] >>
      drule_all chortype_update >> disch_then $ qspecl_then [‘v’, ‘p’] assume_tac >>
      first_x_assum drule >> simp[] >> SET_TAC [])
QED

Theorem chortype_no_self_communication:
  ∀ Γ Θ. chorTypecheckOK Γ Θ c ⇒ no_self_comunication c
Proof
  Induct_on ‘chorTypecheckOK’ >> rw[no_self_comunication_def]
QED

Theorem chorTypecheckOK_let_thm:
  chorTypecheckOK Γ Θ (Let v p e c) ⇔
    ∃ ety. typecheck (localise Γ p) e ety ∧
           chorTypecheckOK Γ Θ c ∧
           FLOOKUP Γ (v,p) = SOME ety
Proof
  simp[Once chorTypecheckOK_cases] >> metis_tac[]
QED

Theorem chorTypecheckOK_if_thm:
  chorTypecheckOK Γ Θ (IfThen v p c1 c2) ⇔
    FLOOKUP Γ (v,p) = SOME boolT ∧ chorTypecheckOK Γ Θ c1 ∧
    chorTypecheckOK Γ Θ c2
Proof
  simp[Once chorTypecheckOK_cases]
QED

Theorem chorTypecheckOK_com_thm:
  chorTypecheckOK Γ Θ (Com p1 v1 p2 v2 c) ⇔
    FLOOKUP Γ (v1,p1) = SOME strT ∧ FLOOKUP Γ (v2,p2) = SOME strT ∧
    {p1; p2} ⊆ Θ ∧ p1 ≠ p2 ∧ chorTypecheckOK Γ Θ c
Proof
  simp[Once chorTypecheckOK_cases] >> metis_tac[]
QED

Theorem chorTypecheckOK_sel_thm:
  chorTypecheckOK Γ Θ (Sel p1 b p2 c) ⇔
    {p1; p2} ⊆ Θ ∧ p1 ≠ p2 ∧ chorTypecheckOK Γ Θ c
Proof
  simp[Once chorTypecheckOK_cases] >> metis_tac[]
QED

Theorem chorTypecheckOK_fix_thm:
  chorTypecheckOK Γ Θ (Fix dn c) ⇔
    chorTypecheckOK Γ (Θ ∪ {dn}) c
Proof
  simp[Once chorTypecheckOK_cases]
QED

(* todo: chorTypecheckOK_no_typeerror *)

val _ = export_theory();

