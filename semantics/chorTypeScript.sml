open HolKernel Parse boolLib bossLib richerLangTheory envSemTheory finite_mapTheory

open chorLangTheory

val _ = new_theory "chorType";


Inductive chorTypecheckOK:
[~nil:] ∀ Γ Θ. chorTypecheckOK Γ Θ Nil
[~com:] ∀ Γ Θ p1 v1 p2 v2 c ty. FLOOKUP Γ (v1,p1) = SOME strT ∧
                                FLOOKUP Γ (v2,p2) = SOME strT ∧
                                ({p1;p2} ⊆ Θ) ∧
                                chorTypecheckOK Γ Θ c ⇒
                                chorTypecheckOK Γ Θ (Com p1 v1 p2 v2 c)
[~sel:] ∀ Γ Θ p1 p2 b c ty. ({p1;p2} ⊆ Θ) ∧ chorTypecheckOK Γ Θ c ⇒
                            chorTypecheckOK Γ Θ (Sel p1 b p2 c)
[~if:] ∀ Γ Θ v p c1 c2 ty. FLOOKUP Γ (v,p) = SOME boolT ∧
                           chorTypecheckOK Γ Θ c1 ∧ chorTypecheckOK Γ Θ c2 ⇒
                           chorTypecheckOK Γ Θ (IfThen v p c1 c2)
[~let:] ∀ Γ Θ v p e c ety. typecheck (localise Γ p) e ety ∧
                           chorTypecheckOK (Γ |+ ((v,p), ety)) Θ c ⇒
                           chorTypecheckOK Γ Θ (Let v p e c)
[~fix:] ∀ Γ Θ c. chorTypecheckOK Γ (Θ ∪ {dn}) c ⇒ chorTypecheckOK Γ Θ (Fix dn c)
End

Definition chorEnvtype_def:
  chorEnvtype Γ Δ = ∀ str p ty. FLOOKUP Γ (str,p) = SOME ty ⇒
                                ∃ v. FLOOKUP Δ (str,p) = SOME v ∧ value_type v ty
End

val _ = export_theory();

