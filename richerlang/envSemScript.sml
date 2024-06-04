open HolKernel Parse boolLib bossLib richerLangTheory finite_mapTheory valueTheory;

val _ = new_theory "envSem";

Definition eval_exp_def:
  (eval_exp c E (Var str) =
   case FLOOKUP E str of
     NONE => TypeError
   | SOME v => return v) ∧
  eval_exp c E (StrLit str) = return (StrV str) ∧
  eval_exp c E (IntLit n) = return (IntV n) ∧
  eval_exp c E (BoolLit b) = return (BoolV b) ∧
  eval_exp c E (BinOp bop e1 e2) =
  do
    v1 <- eval_exp c E e1;
    v2 <- eval_exp c E e2;
    eval_bop bop v1 v2;
  od ∧
  eval_exp c E (Uop uop e) =
  do
    v <- eval_exp c E e;
    eval_uop uop v;
  od ∧
  eval_exp c E (If e1 e2 e3) = 
  do
    v <- eval_exp c E e1;
    b <- getB v;
    if b then eval_exp c E e2 else eval_exp c E e3;
  od ∧
  eval_exp c E (Let s e1 e2) =
  do
    v1 <- eval_exp c E e1;
    eval_exp c (E |+ (s, v1)) e2;
  od ∧
  eval_exp c E (Fn s e) = return (Clos s e E)
  ∧
  eval_exp c E (App e1 e2) = (if c>0 then
                               do
                                 v1 <- eval_exp c E e1;
                                 v2 <- eval_exp c E e2;
                                 case v1 of
                                   (Clos s e E1) => eval_exp (c-1) (E1 |+ (s,v2)) e
                                 | _ => TypeError
                               od
                              else Timeout) ∧
  eval_exp c E (Case e s1 e1 s2 e2) = 
  do
    v <- eval_exp c E e;
    case v of 
      (SumLV v0) => eval_exp c (E|+(s1, v0)) e1
    | (SumRV v0) => eval_exp c (E|+(s2, v0)) e2
    | _ => TypeError
  od
Termination
  WF_REL_TAC ‘inv_image ((<) LEX (measure exp_size)) (λ(c, E, e). (c, e)) ’
End

Definition diverges_def:
  diverges E exp = ∀ c. eval_exp c E exp = Timeout
End

Theorem result_bind_eq_value:
  result_bind m f = Value v ⇔
    ∃ u. m = Value u ∧ f u = Value v
Proof
  Cases_on ‘m’>>simp[]
QED

Theorem result_bind_eq_exn:
  result_bind m f = Exn exn ⇔ m = Exn exn ∨
                              ∃ v. m = Value v ∧ f v = Exn exn
Proof
  Cases_on ‘m’>>simp[]
QED

Theorem result_bind_eq_typeerr:
  result_bind m f = TypeError ⇔ m = TypeError ∨
                              ∃ v. m = Value v ∧ f v = TypeError
Proof
  Cases_on ‘m’>>simp[]
QED


(* why >~[‘typecheck G (Case e arg1 e1 arg2 e2)’] doesn't work ... *)
Theorem type_soundness:
  ∀ c E e G ty. envtype G E ∧ typecheck G e ty ⇒
                (∃ v. eval_exp c E e = Value v ∧
                      value_type v ty) ∨
                (∃ exn. eval_exp c E e = Exn exn) ∨
                eval_exp c E e = Timeout
Proof
  recInduct eval_exp_ind >> rw[eval_exp_def] >> gvs[valuetype_EQ_boolT, AllCaseEqs(), result_bind_eq_value, PULL_EXISTS] >~
  [‘FLOOKUP’]
  >- ( (* var *) gvs[envtype_def]) >~
  [‘G |+ (s, ty1)’]
  >- ( (* let *) simp[PULL_EXISTS] >> first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac [envtype_lemma]) >~
  [‘G |+ (s, ty1)’]
  >- ( (* fn *) irule value_type_FnV >> metis_tac [envtype_def]) >~
  [‘uoptype uop ity oty’, ‘typecheck G arg ity’]
  >- ( (* uop *) first_x_assum $ drule_all_then $ strip_assume_tac >> simp[] >> metis_tac[uop_type_soundness]) >~
  [‘boptype bop ity1 ity2 oty’, ‘typecheck G arg1 ity1’, ‘typecheck G arg2 ity2’]
  >- ( (* bop *) rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[] >> metis_tac[bop_type_soundness])
  >- ( (* if *) rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> gvs[valuetype_EQ_boolT, AllCaseEqs()] >> metis_tac[]) >~
  [‘typecheck G e1 (fnT ity oty)’, ‘typecheck G e2 ity’]
  >- ( (* app *) rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> gvs[valuetype_EQ_fnT] >> first_x_assum $ drule_at (Pat ‘typecheck _ _ _’) >> metis_tac[envtype_lemma])
  >> ( (* case *) first_x_assum $ drule_all_then $ strip_assume_tac
      >- (drule $ iffLR valuetype_EQ_sumT >> rw[]
          >- (‘envtype (G |+ (s1, t1)) (E |+ (s1, v0))’ by simp[envtype_lemma] >>
              first_x_assum $ drule_all_then $ strip_assume_tac >> simp[])
          >> ‘envtype (G |+ (s2, t2)) (E |+ (s2, v0))’ by simp[envtype_lemma] >>
          first_x_assum $ drule_all_then $ strip_assume_tac >> simp[])
      >> simp[])
QED

Theorem clock_value_increment:
  ∀ cl0 E e v. eval_exp cl0 E e = Value v ⇒
               (∀ cl1. cl1 ≥ cl0 ⇒ eval_exp cl1 E e = Value v)
Proof
  recInduct eval_exp_ind >> rw[eval_exp_def] >> gvs[AllCaseEqs(), result_bind_eq_value, PULL_EXISTS]
QED

Theorem clock_exn_increment:
  ∀ cl0 E e exn. eval_exp cl0 E e = Exn exn ⇒
                 (∀ cl1. cl1 ≥ cl0 ⇒ eval_exp cl1 E e = Exn exn)
Proof
  recInduct eval_exp_ind >> rw[eval_exp_def] >> gvs[AllCaseEqs(), result_bind_eq_exn, PULL_EXISTS] >~
  [‘eval_exp (c-1) _ _ = Exn exn’]
  >- (‘eval_exp cl1 E e1 = Value (Clos s e E1)’ by metis_tac[clock_value_increment] >> simp[] >>
      ‘eval_exp cl1 E e2 = Value v2’ by metis_tac[clock_value_increment] >> simp[])
  >> metis_tac [clock_value_increment]
QED

Theorem clock_typeerr_increment:
  ∀ cl0 E e. eval_exp cl0 E e = TypeError ⇒
             (∀ cl1. cl1 ≥ cl0 ⇒ eval_exp cl1 E e = TypeError)
Proof
  recInduct eval_exp_ind >> rw[eval_exp_def] >> gvs[AllCaseEqs(), result_bind_eq_typeerr, PULL_EXISTS] >~
  [‘eval_exp c E e1 = Value (Clos s e E1)’, ‘eval_exp c E e2 = Value v2’, ‘eval_exp (c − 1) (E1 |+ (s,v2)) e = TypeError’]
  >- (‘eval_exp cl1 E e1 = Value (Clos s e E1)’ by metis_tac[clock_value_increment] >> simp[] >>
      ‘eval_exp cl1 E e2 = Value v2’ by metis_tac[clock_value_increment] >> simp[])
  >> metis_tac [clock_value_increment]
QED

Theorem clock_increment:
  ∀ cl0 E e r. eval_exp cl0 E e = r ∧ r ≠ Timeout ⇒               
               (∀ cl1. cl1 ≥ cl0 ⇒ eval_exp cl1 E e = r)
Proof
  Cases_on ‘r’ >> simp[] >> metis_tac[clock_value_increment, clock_exn_increment, clock_typeerr_increment]
QED

(*
Theorem clock_decrement:
Proof
*)


val _ = export_theory();

