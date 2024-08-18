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

val _ = export_theory();

