open HolKernel Parse boolLib bossLib richerLangTheory finite_mapTheory valueTheory pred_setTheory optionTheory;

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
  eval_exp c E (Fn s e) = return (Clos s e (DRESTRICT E (free_vars e) \\ s))
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

(* for chorLang *)
Definition localise_def:
  localise s p = s f_o (λvn. (vn, p))
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

Theorem envtype_submap:
  envtype G E ∧ G' ⊑ G ⇒ envtype G' E
Proof
  metis_tac[envtype_def, SUBMAP_FLOOKUP_EQN]
QED

Theorem FLOOKUP_supermap:
  FLOOKUP E1 s = SOME v ∧ s ∈ FDOM E2 ∧ E2 ⊑ E1 ⇒
          FLOOKUP E2 s = SOME v
Proof
  rw[FLOOKUP_DEF, SUBMAP_DEF]
QED

Theorem envtype_DRESTRICT:
  (*
  envtype G E ⇒ envtype (DRESTRICT G (FDOM (DRESTRICT E (free_vars e)))) (DRESTRICT E (free_vars e))
  *)
  envtype G E ⇒ envtype (DRESTRICT G (FDOM (DRESTRICT E (free_vars e))) \\ s) (DRESTRICT E (free_vars e) \\ s)
Proof
  rw[envtype_def] >>
  ‘FLOOKUP G str = SOME ty’ by metis_tac[SUBMAP_DOMSUB, SUBMAP_DRESTRICT, SUBMAP_FLOOKUP_EQN] >>
  first_x_assum $ drule_all_then $ strip_assume_tac >>
  ‘str ∈ FDOM (DRESTRICT G (FDOM (DRESTRICT E (free_vars e))) \\ s)’ by simp[TO_FLOOKUP] >>
  ‘str ∈ (FDOM (DRESTRICT E (free_vars e)))’ by metis_tac[FDOM_DOMSUB, IN_DELETE, DRESTRICT_DEF, IN_INTER] >>
  ‘str ≠ s’ by metis_tac[FDOM_DOMSUB, IN_DELETE] >>
  ‘str ∈ (FDOM (DRESTRICT E (free_vars e) \\ s))’ by simp[FDOM_DOMSUB, IN_DELETE] >>
  ‘(DRESTRICT E (free_vars e) \\ s) ⊑ E’ by metis_tac[SUBMAP_DOMSUB, SUBMAP_TRANS, SUBMAP_DRESTRICT] >>
  metis_tac[FLOOKUP_supermap]
QED

Theorem typecheck_drestrict:
  typecheck G e ty ∧ free_vars e ⊆ A ⇒
  typecheck (DRESTRICT G A) e ty
Proof
  (*
  Induct_on ‘typecheck’ >> rw[]
  >- simp[FLOOKUP_SIMP]
  >- (‘{s} ⊆ A’ by simp[SUBSET_DEF] >> metis_tac[UNION_SUBSET, UNION_DIFF_EQ])
  >- ()
  >> metis_tac[]
  *)
  cheat
QED

Theorem typecheck_update_sub_fv:
  envtype G E ∧ typecheck (G |+ (s,ty1)) e ty ⇒
          typecheck (DRESTRICT G (FDOM (DRESTRICT E (free_vars e))) \\ s |+ (s,ty1)) e ty
Proof
  (*
  Induct_on ‘typecheck’ >> rw[]
  >- (gvs[FLOOKUP_SIMP, AllCaseEqs(), FDOM_DRESTRICT, envtype_def] >>
      metis_tac[flookup_thm])
  *)
  cheat
QED

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
  >- ( (* fn *) irule value_type_FnV >> 
       metis_tac[envtype_DRESTRICT, envtype_def, typecheck_update_sub_fv]) >~
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

Theorem localise_update_eqn:
  localise s p |+ (vn, v) = localise (s |+ ((vn, p), v)) p
Proof
  cheat
QED

Theorem submap_domsub2:
  s ⊑ z ⇒ s \\ x ⊑ z \\ x
Proof
  cheat
QED

Theorem submap_localise:
  s ⊑ z ⇒ localise s p ⊑ localise z p
Proof
  cheat
QED

Theorem envtype_fdom:
  envtype G E ⇒ FDOM G ⊆ FDOM E
Proof
  rw[envtype_def, SUBSET_DEF, TO_FLOOKUP] >> metis_tac[option_CLAUSES]
QED

Theorem envtype_update:
  envtype G E ∧ value_type v t ⇒
  envtype (G|+(s,t)) (E|+(s,v))
Proof
  rw[envtype_def] >> rw[FLOOKUP_UPDATE] >> gvs[FLOOKUP_UPDATE]
QED

(* For Fn case in eval_bigger_state *)
Theorem eval_no_undefined_vars:
  envtype G E ∧ typecheck G e ty ⇒
  free_vars e ⊆ FDOM E
Proof
  metis_tac[typecheck_vars, envtype_fdom, SUBSET_TRANS]
QED

Theorem delete_inter_eq:
  A ∩ (B DELETE s) = (A DELETE s) ∩ B
Proof
  irule $ iffRL $ SET_EQ_SUBSET >> rw[SUBSET_DEF]
QED

Theorem drestrict_domsub_map:
  DRESTRICT f s \\ k = DRESTRICT (f \\ k) s
Proof
  rw[DRESTRICT_DOMSUB] >> irule $ iffRL $ DRESTRICT_EQ_DRESTRICT >>
  rw[DELETE_INTER, SET_EQ_SUBSET, SUBSET_DEF, SUBMAP_DEF, DRESTRICT_DEF, DOMSUB_FAPPLY_NEQ]
QED

Theorem subset_absortion:
  A ⊆ B ∧ B ⊆ C ⇒
  A ∩ B = A ∩ C
Proof
  metis_tac[SUBSET_DEF, SUBSET_TRANS, SUBSET_INTER_ABSORPTION]
QED

Theorem eval_value_type:
  envtype G E ∧ typecheck G e ty ∧ eval_exp cl E e = Value v ⇒
  value_type v ty
Proof
  rw[] >> drule type_soundness >>
  disch_then (qspec_then ‘cl’ strip_assume_tac) >>
  first_x_assum $ drule_then $ strip_assume_tac >> gvs[]
QED

(* value_type sumv should be ⇔ ? *)
Theorem eval_sumv_types:
  envtype G E ∧ typecheck G e (sumT t1 t2) ⇒
  (eval_exp cl E e = Value (SumRV v) ⇒ value_type v t2) ∧
  (eval_exp cl E e = Value (SumLV v) ⇒ value_type v t1)
Proof
  (*
  rw[] >> 
  >- (drule eval_value_type >> strip_tac >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >>
      metis_tac[value_type_SumRV, value_type_SumLV])
  *)
  cheat
QED

(* based on type soundness *)
Theorem eval_bigger_state_type:
  ∀ cl s p ev z G ty. eval_exp cl (localise s p) e = Value ev ∧ s ⊑ z ∧
                      envtype G (localise s p) ∧ typecheck G e ty ⇒
                      eval_exp cl (localise z p) e = Value ev
Proof
  Induct_on ‘e’ >~
  [‘Fn _ _’]
  >- (rpt strip_tac >>
      ‘(free_vars e DIFF {s}) ⊆ FDOM (localise s' p)’ by metis_tac[eval_no_undefined_vars, free_vars] >> rw[eval_exp_def] >>
      ‘DRESTRICT (localise s' p) (free_vars e) \\ s = DRESTRICT (localise z p) (free_vars e) \\ s’ by (rw[drestrict_domsub_map] >> irule $ iffRL $ DRESTRICT_EQ_DRESTRICT_SAME >>
  ‘localise s' p ⊑ localise z p’ by simp[submap_localise] >> rw [] >>
  metis_tac[DOMSUB_FAPPLY_NEQ, SUBMAP_DEF, delete_inter_eq, DELETE_DEF, SUBMAP_FDOM_SUBSET, subset_absortion]) >>
      gvs[eval_exp_def])
  >> rw[eval_exp_def] >> gvs[AllCaseEqs(), result_bind_eq_value, PULL_EXISTS]
  >- metis_tac[submap_localise, FLOOKUP_SUBMAP] >~ 
  [‘Value (SumRV v)’]
  >- (‘(s' |+ ((s,p),v)) ⊑ (z |+ ((s,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >>
      gvs[localise_update_eqn] >>
      ‘envtype (G |+ (s,t2)) (localise (s' |+ ((s,p),v)) p)’ by metis_tac[eval_sumv_types, localise_update_eqn, envtype_update] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[]) >~
  [‘Value (SumLV v)’]
  >- (‘(s' |+ ((s0,p),v)) ⊑ (z |+ ((s0,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >>
      gvs[localise_update_eqn] >>
      ‘envtype (G |+ (s0,t1)) (localise (s' |+ ((s0,p),v)) p)’ by metis_tac[eval_sumv_types, localise_update_eqn, envtype_update] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[]) >~
  [‘eval_exp cl (localise s p |+ (vn, v)) body’]
  >- (‘(s |+ ((vn,p),v)) ⊑ (z |+ ((vn,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >> gvs[localise_update_eqn] >>
      ‘envtype (G|+(vn,ety)) (localise (s |+ ((vn,p),v)) p)’ by metis_tac[eval_value_type, localise_update_eqn, envtype_update] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[])
  >> (rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[])
QED

Theorem eval_fn_submap_lemma:
  eval_exp cl (localise s' p) (Fn s e) = Value ev ∧
  free_vars (Fn s e) ⊆ FDOM (localise s' p) ∧
  s' ⊑ z ⇒
  DRESTRICT (localise s' p) (free_vars e) \\ s = DRESTRICT (localise z p) (free_vars e) \\ s
Proof
  rw[drestrict_domsub_map] >>
  irule $ iffRL $ DRESTRICT_EQ_DRESTRICT_SAME >>
  ‘localise s' p ⊑ localise z p’ by simp[submap_localise] >> rw [] >>
  metis_tac[DOMSUB_FAPPLY_NEQ, SUBMAP_DEF, delete_inter_eq, DELETE_DEF, SUBMAP_FDOM_SUBSET, subset_absortion]
QED

Theorem subset_update:
  A ⊆ B ⇒ A ∪ C ⊆ B ∪ C
Proof
  rw[SUBSET_DEF, UNION_DEF]
QED

Theorem subset_diff_update:
  A DIFF B ⊆ C ⇒ A ⊆ C ∪ B
Proof
  metis_tac[subset_update, UNION_DIFF_EQ, SUBSET_UNION, SUBSET_TRANS]
QED

Theorem eval_bigger_state_fv:
  ∀ cl s p ev z. eval_exp cl (localise s p) e = Value ev ∧
                 free_vars e ⊆ FDOM (localise s p) ∧ s ⊑ z ⇒
                 eval_exp cl (localise z p) e = Value ev
Proof
  Induct_on ‘e’ >~
  [‘Fn _ _’]
  >- (rpt strip_tac >> rw[eval_exp_def] >> 
      ‘DRESTRICT (localise s' p) (free_vars e) \\ s = DRESTRICT (localise z p) (free_vars e) \\ s’ by metis_tac[eval_fn_submap_lemma] >>
      gvs[eval_exp_def])
  >> rw[eval_exp_def] >> gvs[AllCaseEqs(), result_bind_eq_value, PULL_EXISTS]
  >- metis_tac[submap_localise, FLOOKUP_SUBMAP] >~ 
  [‘Value (SumRV v)’]
  >- (‘(s' |+ ((s,p),v)) ⊑ (z |+ ((s,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >> gvs[localise_update_eqn] >>
      ‘free_vars e'' ⊆ FDOM (localise (s' |+ ((s,p),v)) p)’ by metis_tac[localise_update_eqn, FDOM_FUPDATE, INSERT_SING_UNION, subset_diff_update, UNION_COMM] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[]) >~
  [‘Value (SumLV v)’]
  >- (‘(s' |+ ((s0,p),v)) ⊑ (z |+ ((s0,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >> gvs[localise_update_eqn] >>
      ‘free_vars e' ⊆ FDOM (localise (s' |+ ((s0,p),v)) p)’ by metis_tac[localise_update_eqn, FDOM_FUPDATE, INSERT_SING_UNION, subset_diff_update, UNION_COMM] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[]) >~
  [‘eval_exp cl (localise s p |+ (vn, v)) body’]
  >- (‘(s |+ ((vn,p),v)) ⊑ (z |+ ((vn,p),v))’ by metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE] >> gvs[localise_update_eqn] >>
      ‘free_vars body ⊆ FDOM (localise (s |+ ((vn,p),v)) p)’ by metis_tac[localise_update_eqn, FDOM_FUPDATE, INSERT_SING_UNION, subset_diff_update, UNION_COMM] >>
      rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[])
  >> (rpt (first_x_assum $ drule_all_then $ strip_assume_tac) >> simp[])
QED

Theorem eval_bigger_state_exn:
  eval_exp cl (localise s p) e = Exn exn ∧ s ⊑ z ⇒
  eval_exp cl (localise z p) e = Exn exn
Proof
  cheat
QED

val _ = export_theory();

