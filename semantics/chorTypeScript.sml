open HolKernel Parse boolLib bossLib richerLangTheory envSemTheory finite_mapTheory

open chorLangTheory

val _ = new_theory "chorType";


Datatype:
  type = typeL | unitT
End

Inductive chorTypecheck:
[~nil:] ∀ Γ Θ. chorTypecheck Γ Θ Nil unitT
[~com:] ∀ Γ Θ p1 v1 p2 v2 c ty. FLOOKUP Γ (v1,p1) = SOME strT ∧ ({p1,p2} ⊆ Θ) ∧
                                chorTypecheck Γ Θ c ty ⇒
                                chorTypecheck Γ Θ (Com p1 v1 p2 v2 c) ty
[~sel:] ∀ Γ Θ p1 p2 b c ty. ({p1,p2} ⊆ Θ) ∧ chorTypecheck Γ Θ c ty ⇒
                            chorTypecheck Γ Θ (Sel p1 b p2 c) ty
[~if:] ∀ Γ Θ v p c1 c2 ty. FLOOKUP Γ (v,p) = SOME boolT ∧
                           chorTypecheck Γ Θ c1 ty ∧ chorTypecheck Γ Θ c2 ty ⇒
                           chorTypecheck Γ Θ (IfThen v p c1 c2) ty
[~let:] ∀ Γ Θ v p e c ety ty. typecheck (localise Γ p) e ety ∧
                              chorTypecheck (Γ |+ ((v,p), ety)) Θ c ty ⇒
                              chorTypecheck Γ Θ (Let v p e c) ty
End

val _ = export_theory();

