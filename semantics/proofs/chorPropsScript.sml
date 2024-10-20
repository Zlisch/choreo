open preamble choreoUtilsTheory chorSemTheory chorLangTheory richerLangTheory valueTheory envSemTheory finite_mapTheory optionTheory;

val _ = new_theory "chorProps";



(* valid_action ensures a transition tag `alpha` and an asyncronous
   transition tag `h` are related as described in the asyncronous
   transitions rules (trans_com_async and trans_sel_async).

   For this relation to hold `h` must:

   * Be one of LSel or LCom

   * Have its sender be a free process in `alpha`

   * Don't have as a receiver a free process in `alpha`
*)
Definition valid_action_def:
  valid_action alpha h = ((∃p1 b p2 .
                           h = LSel p1 b p2
                           ∧ p1 ∈ freeprocs alpha
                           ∧ p2 ∉ freeprocs alpha) ∨
                          (∃p1 v1 p2 v2.
                            h = LCom p1 v1 p2 v2
                            ∧ p1 ∈ freeprocs alpha
                            ∧ p2 ∉ freeprocs alpha))
End

(* Two list in a lcong relationship have the same length *)
Theorem lcong_length:
  ∀l l'. l τ≅ l' ⇒ LENGTH l = LENGTH l'
Proof
  ho_match_mp_tac lcong_strongind
  \\ rw []
QED

(* An empty list can't be in an lcong relationship with a non empty list *)
Theorem not_nil_lcong_cons:
  ∀h l. ¬ ([] τ≅ h :: l)
Proof
  rw [] >> CCONTR_TAC  >> rw []
  \\ IMP_RES_TAC lcong_length
  \\ fs [LENGTH]
QED

(* `lrm l e` removes the first appearance of element `e` in `l` *)
Definition lrm_def:
  lrm [] e      = []
∧ lrm (x::ls) e = (if x = e
                 then ls
                 else x :: lrm ls e)
End

(* If an element `e` is not in `l` then `lrm e l` is redundant *)
Theorem mem_lrm_id:
  ¬ MEM e l ⇒ lrm l e = l
Proof
  Induct_on `l` >> rw [lrm_def,MEM]
QED

(* `lrm` conditionaly distributes over the first argument (`l`) of an
   append if the element you are trying to remove is in `l`
*)
Theorem lrm_mem_append:
  ∀l e r. MEM e l ⇒ lrm (l ++ r) e = lrm l e ++ r
Proof
  induct_on `l` >> rw [MEM,lrm_def]
QED

(* `lrm` conditionaly distributes over the second argument (`r`) of an
   append if the element (`e`) you are trying to remove is not in the
   first argument (`l`). Note that this does not imply that `e` is in
   `r`
*)
Theorem lrm_not_mem_append:
  ∀l e r. ¬ MEM e l ⇒ lrm (l ++ r) e = l ++ lrm r e
Proof
  induct_on `l` >> rw [MEM,lrm_def]
QED

(* Applying `lrm` at both sides of an lcong preserves the relation *)
Theorem lcong_lrm:
  ∀e l l'. l τ≅ l' ⇒ lrm l e τ≅ lrm l' e
Proof
  GEN_TAC
  \\ ho_match_mp_tac lcong_strongind
  \\ rw [lcong_rules]
  \\ IMP_RES_TAC lcong_trans
  \\ Cases_on `MEM e (h ++ [t1; t2])`
  >- (`MEM e (h ++ [t2; t1])` by fs [MEM_PERM,PERM_APPEND_IFF,PERM_SWAP_AT_FRONT]
     \\ rw [lrm_mem_append]
     \\ Cases_on `MEM e h`
     \\ rw [lrm_mem_append,lcong_rules,lrm_not_mem_append]
     \\ rw [lrm_def,lcong_rules])
  >- (`¬MEM e (h ++ [t2; t1])` by fs [MEM_PERM,PERM_APPEND_IFF,PERM_SWAP_AT_FRONT]
     \\ rw [lrm_not_mem_append,lcong_rules])
QED

(* [] can only be related in `lcong` with  (itself) [] *)
Theorem lcong_nil_simp:
  ∀l. (l τ≅ [] ⇔ l = []) ∧ ([] τ≅ l ⇔ l = [])
Proof
  Cases_on `l`
  >- rw [lcong_rules]
  >- (fs [] >> metis_tac [not_nil_lcong_cons,lcong_refl])
QED

(* Prepending and element (`h`) preserves `lcong` *)
Theorem lcong_cons:
  ∀h l l'. lcong l l' ⇒ lcong (h :: l) (h :: l')
Proof
  GEN_TAC
  \\ ho_match_mp_tac lcong_strongind
  \\ rw [lcong_rules]
  \\ metis_tac [lcong_rules,GSYM APPEND |> CONJUNCT2]
QED

(* Removing the identical heads preserves `lcong` *)
Theorem cons_lcong:
  ∀h l l'. h :: l τ≅ h :: l' ⇒ l τ≅ l'
Proof
  rw []
  \\ IMP_RES_TAC lcong_lrm
  \\ pop_assum (ASSUME_TAC o Q.SPEC `h`)
  \\ fs [lrm_def]
QED

(* A slightly more specific case of `lcong_lrm` *)
Theorem lcong_cons_simp:
  ∀h l h' l'. h ≠ h' ∧ h :: l τ≅ h' :: l'
   ⇒ l τ≅ h' :: lrm l' h
Proof
  rw []
  \\ IMP_RES_TAC lcong_lrm
  \\ pop_assum (ASSUME_TAC o Q.SPEC `h`)
  \\ rfs [lrm_def]
QED

(* Any valid transition ensures the relationship between the
   transition tag `t` and the head of the asyncronous transitions list
   `h` is a valid_action
*)
Theorem trans_valid_action:
   ∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ valid_action t h
Proof
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ valid_action t h`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules,valid_action_def]
QED

(* Any valid trasition with a non-empty list of asyncronous trasitions
   implies there exist a transition with the same transition tag
   and the tail of the asyncronous transition list
*)
Theorem trans_async_some_trans:
   ∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')
Proof
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules]
  \\ metis_tac []
QED

(* valid_actions over a list of actions *)
Definition valid_actions_def:
  valid_actions alpha l = EVERY (valid_action alpha) l
End

(* Any valid transition ensures that both transition tag `t` and
   asyncronous transitions list `l` satisfies valid_actions
*)
Theorem trans_valid_actions:
   ∀s c s' c' t l.
    trans (s,c) (t,l) (s',c')
    ⇒ valid_actions t l
Proof
  Induct_on `l` >> rw []
  >- rw [valid_actions_def]
  \\ IMP_RES_TAC trans_valid_action
  \\ IMP_RES_TAC trans_async_some_trans
  \\ `valid_actions t l` by metis_tac []
  \\ fs [valid_actions_def]
QED

(* In a list of valid actions (`h`) there are no LTau actions *)
Theorem valid_actions_not_ltau:
  ∀t h p v. valid_actions t h ⇒ ¬ MEM (LTau p v) h
Proof
  rw []
  \\ CCONTR_TAC
  \\ fs [valid_actions_def,EVERY_MEM]
  \\ RES_TAC
  \\ fs [valid_action_def]
QED

(* In a list of valid actions (`h`) there are no LFix actions *)
Theorem valid_actions_not_lfix:
  ∀t h p v. valid_actions t h ⇒ ¬ MEM LFix h
Proof
  rw []
  \\ CCONTR_TAC
  \\ fs [valid_actions_def,EVERY_MEM]
  \\ RES_TAC
  \\ fs [valid_action_def]
QED

(* Give a state and a transition tag, one can generate the resulting state *)
Definition state_from_tag_def:
  state_from_tag s (LCom p1 v1 p2 v2) = (s |+ ((v2,p2),s ' (v1,p1)))
  ∧ state_from_tag s (LLet v p e r)  =
    (case r of
       Value ev => (s |+ ((v,p), ev))
     | _ => s)
∧ state_from_tag s _ = s
End

(* The resulting state of any transition can be described using `state_from_tag` *)
(* need to address com_exn so prob error label? *)
Theorem trans_state:
  ∀s c α τ s' c'. trans (s,c) (α,τ) (s',c') ⇒ s' = state_from_tag s α
Proof
  ho_match_mp_tac trans_pairind
  \\ rw [state_from_tag_def]
  \\ fs [FLOOKUP_DEF]
QED

(* Making the state bigger does not affect the behaviour of the choreography *)
Theorem trans_submap:
  ∀s c α τ s' c' z.
   trans (s,c) (α,τ) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans (z,c) (α,τ) (z',c') ∧ s' ⊑ z'
Proof
  let
val local_metis =
metis_tac [trans_rules,FLOOKUP_SUBMAP,SUBMAP_mono_FUPDATE
           , SUBMAP_DOMSUB,GSYM SUBMAP_DOMSUB_gen
           , SUBMAP_TRANS]
  in
    `∀s c α τ s' c'.
  trans (s,c) (α,τ) (s',c')
  ⇒ ∀z. s ⊑ z
        ⇒ ∃z'. trans (z,c) (α,τ) (z',c') ∧ s' ⊑ z'`
               suffices_by metis_tac []
\\ ho_match_mp_tac trans_pairind
\\ rw []  >~
[‘Let v p e c’, ‘Value ev’]
>- metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE, trans_letval, eval_bigger_state_fv, submap_localise, SUBMAP_FDOM_SUBSET, SUBSET_TRANS, localise_fdom] >~
[‘Let v p e c’, ‘Exn exn’]
>- metis_tac[submap_domsub2, SUBMAP_mono_FUPDATE, trans_letexn, eval_bigger_state_exn, submap_localise, SUBMAP_FDOM_SUBSET, SUBSET_TRANS, localise_fdom] >~
[‘IfThen _ _ _ _’, ‘l τ≅ l'’]
>- ( (* if_swap *) res_tac
     \\ `z' = z''` by metis_tac [trans_state]
     \\ rveq \\ qexists_tac `z'` \\ local_metis) >~
[‘Com _ _ _ _ _’, ‘written alpha ≠ SOME (v1,p1)’, ‘trans (s,c) (alpha,l) (s',c')’]
>- ( (* com_async *) metis_tac[trans_com_async]) >~
[‘LFix’, ‘IfThen _ _ _ _’]
>- (res_tac
  \\ `z = z'` by (drule trans_state \\ rw [state_from_tag_def])
    \\ rveq \\ qexists_tac `z` \\ local_metis)  >~
[‘LFix’, ‘IfThen _ _ _ _’]
>- (res_tac
  \\ `z = z'` by (drule trans_state \\ rw [state_from_tag_def])
    \\ rveq \\ qexists_tac `z` \\ local_metis)
>> local_metis
   end
QED

(* RTC version of `trans_submap` *)
Theorem trans_s_submap_gen:
  ∀s c α τ s' c' z.
   trans_s (s,c) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans_s (z,c) (z',c') ∧ s' ⊑ z'
Proof
  `∀x y. trans_s x y
    ⇒ ∀s c s' c' z. x = (s,c) ∧ y = (s',c') ∧ s ⊑ z
       ⇒ ∃z'. trans_s (z,c) (z',c') ∧ s' ⊑ z'`
  suffices_by metis_tac []
  \\ rewrite_tac [trans_s_def]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw []
  >- (qexists_tac `z` \\ rw [])
  \\ PairCases_on `x'` \\ Cases_on `s`
  \\ drule trans_submap
  \\ disch_then drule  \\ rw []
  \\ pop_assum drule   \\ rw []
  \\ qexists_tac `z''` \\ rw []
  \\ ho_match_mp_tac RTC_TRANS
  \\ metis_tac []
QED

(* Slightly more mp-friendly version of `trans_s_submap_gen` *)
Theorem trans_s_submap:
  ∀s c α τ s' c' z.
   trans_s (s,c) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans_s (z,c) (z',c')
Proof
  metis_tac [trans_s_submap_gen]
QED

Definition free_variables_def:
  (free_variables (Nil) = {}) /\
  (free_variables (Call _) = {}) /\
  (free_variables (IfThen v p c1 c2) = {(v,p)} ∪ (free_variables c1 ∪ free_variables c2)) /\
  (free_variables (Com p1 v1 p2 v2 c) = {(v1,p1)} ∪ (free_variables c DELETE (v2,p2))) /\
  (free_variables (Let v p e c) = {(s, p) | s ∈ free_vars e} ∪ (free_variables c DELETE (v,p))) /\
  (free_variables (Sel p b q c) = free_variables c) /\
  (free_variables (Fix x c) = free_variables c)
End

Definition defined_vars_def:
  defined_vars (s,c) = FDOM s
End

Definition no_undefined_vars_def:
  no_undefined_vars (s,c) = (free_variables c ⊆ FDOM s)
End

Theorem defined_vars_mono:
  ∀sc alpha sc'. trans sc alpha sc' ⇒ defined_vars sc ⊆ defined_vars sc'
Proof
  ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[defined_vars_def,SUBSET_OF_INSERT]
QED


(* dsubst resulting free variables are bounded by the original free variables of c and c' *)
Theorem dsubst_subset_free_variables:
  ∀c c' dn.
    free_variables (dsubst c dn c') ⊆ free_variables c ∪ free_variables c'
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [free_variables_def,dsubst_def]
  \\ fs [free_variables_def,dsubst_def]
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []
QED

(* dsubst can only add more free variables *)
Theorem free_variables_subset_dsubst:
  ∀c c' dn.
    free_variables c ⊆ free_variables (dsubst c dn c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [free_variables_def,dsubst_def]
  \\ fs [SUBSET_DEF]
QED

(* free_variables are the same if we are trying to substitute the same program *)
Theorem free_variables_dsubst_eq:
  ∀c dn. free_variables (dsubst c dn c) = free_variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [free_variables_subset_dsubst,
                dsubst_subset_free_variables,
                UNION_IDEMPOT]
QED

(* free_variables are the same if we are trying to substitute the same program *)
Theorem free_variables_dsubst_eq_Fix:
  ∀c x y. free_variables (dsubst c x (Fix y c)) = free_variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [free_variables_subset_dsubst,
                dsubst_subset_free_variables,
                free_variables_def,
                UNION_IDEMPOT]
QED

Theorem free_vars_mono:
  ∀sc alpha sc'. trans sc alpha sc'
    ⇒ (free_variables(SND sc') DIFF defined_vars sc' ⊆ free_variables(SND sc) DIFF defined_vars sc)
Proof
  ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> fs[free_variables_def,defined_vars_def,DIFF_INSERT,
        free_variables_dsubst_eq_Fix] >> rw[]
  >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> rpt strip_tac
  >> fs[] >> metis_tac[]
QED

(* Transitions preserve ‘no_undefined_vars’ since they can not remove
   variables from the state
 *)
Theorem no_undefined_vars_trans_pres:
  ∀sc alpha sc'. no_undefined_vars sc ∧ trans sc alpha sc' ⇒ no_undefined_vars sc'
Proof
  rpt gen_tac >> disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  >> qpat_x_assum `no_undefined_vars _` mp_tac
  >> qpat_x_assum `trans _ _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> imp_res_tac free_vars_mono
  >> fs[no_undefined_vars_def,free_variables_def,DELETE_SUBSET_INSERT,defined_vars_def,SUBSET_OF_INSERT,
        free_variables_dsubst_eq_Fix]
  >> fs[SUBSET_DEF,INSERT_DEF,DIFF_DEF]
  >> metis_tac[]
QED

(* Transitions preserve ‘no_undefined_vars’ since they can not remove
   variables from the state
*)
Theorem no_undefined_vars_trans_s_pres:
  ∀sc alpha sc'. no_undefined_vars sc ∧ trans_s sc sc' ⇒ no_undefined_vars sc'
Proof
  rpt gen_tac \\ disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS)
  \\ rpt (pop_assum mp_tac) \\ simp[trans_s_def]
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`sc'`])
  \\ ho_match_mp_tac RTC_INDUCT \\ rw[]
  \\ metis_tac [no_undefined_vars_trans_pres]
QED

(* A tag does not remove variables from the state, hence preserving
   ‘no_undefined_vars_def’
*)
Theorem no_undefined_vars_from_tags:
  ∀c s α.
   no_undefined_vars (s,c) ⇒ no_undefined_vars (state_from_tag s α, c)
Proof
  rw [no_undefined_vars_def,free_variables_def]
  \\ Cases_on `α` >~
  [‘LLet s vn e r’]
  >- (rw[state_from_tag_def] >> Cases_on ‘r’ >>
      simp[] >> ho_match_mp_tac SUBSET_TRANS >> metis_tac[SUBSET_OF_INSERT])
  \\ fs [state_from_tag_def]
  \\ ho_match_mp_tac SUBSET_TRANS
  \\ metis_tac [SUBSET_OF_INSERT]
QED

(* If there are no undefined variables no lookup into
   the state should fail (give NONE)
*)
Theorem no_undefined_FLOOKUP:
  (∀p v s c q x. no_undefined_vars (s,Com p v q x c)
                 ⇒ ∃x. FLOOKUP s (v,p) = SOME x)
  ∧ (∀p v s c c1 c2. no_undefined_vars (s,IfThen v p c1 c2)
                     ⇒ ∃x. FLOOKUP s (v,p) = SOME x)
  ∧ (∀p s c v e. no_undefined_vars (s,Let v p e c)
                 ⇒ (∀ vn. vn ∈ free_vars e ⇒ IS_SOME (FLOOKUP s (vn,p))))
Proof
  rw [no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] >>
  ‘(vn,p) ∈ {(s,p) | s ∈ free_vars e}’ by simp[] >>
  ‘(vn,p) ∈ FDOM s’ by metis_tac[SUBSET_THM] >> metis_tac[FDOM_FLOOKUP, IS_SOME_DEF]
QED

(* MP-friendly version of no_undefined_FLOOKUP *)
val t_list = no_undefined_FLOOKUP |> CONJUNCTS

Theorem no_undefined_FLOOKUP_if  = el 2 t_list
Theorem no_undefined_FLOOKUP_com = el 1 t_list
Theorem no_undefined_FLOOKUP_let = el 3 t_list

(* Ensure no self communication of a choreography *)
Definition no_self_comunication_def:
  no_self_comunication (Com p _ q _ c)   = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (Sel p _ q c)     = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (IfThen _ _ c c') = (no_self_comunication c ∧
                                            no_self_comunication c')
∧ no_self_comunication (Let _ _ _ c)     = no_self_comunication c
∧ no_self_comunication (Fix _ c)         = no_self_comunication c
∧ no_self_comunication _                 = T
End

Theorem no_self_comunication_dsubst:
  ∀c c' dn.
    no_self_comunication c ∧ no_self_comunication c'
    ⇒ no_self_comunication (dsubst c dn c')
Proof
  rw [] \\ Induct_on ‘c’
  \\ rw [no_self_comunication_def,dsubst_def]
  \\ fs [no_self_comunication_def,dsubst_def]
QED

(* Transitions preserve ‘no_self_comunication’ since they change
   the shape of the choreography aside from consuming its operations
*)
Theorem no_self_comunication_trans_pres:
  ∀s c τ l s' c'.
   no_self_comunication c ∧ trans (s,c) (τ,l) (s',c')
   ⇒ no_self_comunication c'
Proof
  rpt gen_tac \\ disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  \\ qpat_x_assum `no_self_comunication _` mp_tac
  \\ qpat_x_assum `trans _ _ _` mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘s’,‘c’,‘τ’,‘l’,‘s'’,‘c'’])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [no_self_comunication_def,
         no_self_comunication_dsubst]
QED

Definition is_bad_label_def[simp]:
  is_bad_label (LLet _ _ _ Timeout) = T ∧
  is_bad_label _ = F
End


(* Check if a tag matches the head of a choreography *)
Definition chor_match_def:
  chor_match  (LCom p v q x)  (Com p' v' q' x' c)  = ((p,v,q,x)  = (p',v',q',x'))
∧ chor_match  (LComExn p v q x)  (Com p' v' q' x' c)  = ((p,v,q,x)  = (p',v',q',x'))
∧ chor_match  (LSel p b q)    (Sel p' b' q' c)     = ((p,b,q)  = (p',b',q'))
∧ chor_match  (LLet v p e r)  (Let v' p' e' c)     = ((v,p,e) = (v',p',e'))
∧ chor_match  (LTau p v)      (IfThen v' p' c1 c2) = ((p,v)     = (p',v'))
∧ chor_match   LFix           (Fix _ _)            = T
∧ chor_match   _              _                    = F
End

(* Generates the corresponding tag that would consume
   the front of the choreography
*)
Definition chor_tag_def:
  chor_tag s (Com p v q x _)  = (case FLOOKUP s (v,p) of
                                   SOME (StrV d) => LCom p v q x
                                 | _ => LComExn p v q x)
∧ chor_tag _ (Sel p b q _)    = LSel p b q
∧ chor_tag s (Let v p e _)    =
  (case some r. ∃ cl. eval_exp cl (localise s p) e = r ∧ r ≠ Timeout of
     NONE => LLet v p e Timeout
   | SOME r => LLet v p e r)
∧ chor_tag _ (IfThen v p _ _) = LTau p v
∧ chor_tag _ (Fix _ _)        = LFix
End


(* Drops the head of the choreography updating the state in the process.
   Its equivalent to one synchronous step in the semantics.
*)
Definition chor_tl_def:
  chor_tl s Nil             = (s,Nil)
∧ chor_tl s (Call v)        = (s,Call v)
∧ chor_tl s (Fix dn c)      = (s,dsubst c dn (Fix dn c))
∧ chor_tl s (Com p v q x c) = (case FLOOKUP s (v,p) of
                                 SOME (StrV d) => (s|+((x,q), StrV d), c)
                               | _ => (s,Nil))
∧ chor_tl s (Sel p b q c)   = (s,c)
∧ chor_tl s (Let v p e c) =
  (case some ev. ∃ cl. eval_exp cl (localise s p) e = Value ev of
     NONE => (s, Nil)
   | SOME ev => (s |+ ((v,p), ev),c))
∧ chor_tl s (IfThen v p c1 c2) =
    (if FLOOKUP s (v,p) = SOME (BoolV T) then (s,c1)
     else if FLOOKUP s (v,p) = SOME (BoolV F) then (s,c2)
     else (s, Nil))
End

(* Advances the choreography until the given tag
   matches removing everything in its path
   (state is still updated)
*)
Definition syncTrm_def:
  syncTrm (k:num) (s,Nil) τ              = NONE
∧ syncTrm  k      (s,Call v) τ           = NONE
∧ syncTrm  k      (s,IfThen v p c1 c2) τ =
  (if (k = 0) then NONE
   else if chor_match τ (IfThen v p c1 c2)
   then SOME (chor_tl s (IfThen v p c1 c2))
   else if FLOOKUP s (v,p) = SOME (BoolV T)
   then syncTrm (k-1) (s,c1) τ
   else if FLOOKUP s (v,p) = SOME (BoolV F)
   then syncTrm (k-1)(s,c2) τ
   else NONE)
∧ syncTrm k (s, Com p1 v1 p2 v2 c) τ =
  (if k = 0 then NONE
   else if chor_match τ (Com p1 v1 p2 v2 c)
   then SOME (chor_tl s (Com p1 v1 p2 v2 c))
   else case some str. FLOOKUP s (v1,p1) = SOME (StrV str) of
          NONE => NONE
        | SOME str => syncTrm (k-1) (s|+((v2,p2), (StrV str)), c) τ)
∧ syncTrm k (s, Let v p e c) τ =
  (if (k = 0) ∨ is_bad_label τ then NONE
   else if chor_match τ (Let v p e c)
   then (case some r. ∃ cl. eval_exp cl (localise s p) e = r ∧ r ≠ Timeout of
           SOME (Value ev) => SOME (s |+ ((v,p), ev),c)
         | SOME (Exn _) => SOME (s, Nil)
         | _ => NONE)
   else syncTrm (k-1) (chor_tl s (Let v p e c)) τ)
∧ syncTrm k (s,c) τ =
  (if k = 0 then NONE
   else if chor_match τ c
   then SOME (chor_tl s c)
   else syncTrm (k-1) (chor_tl s c) τ)
End

(* Alternative induction principle *)
Theorem syncTrm_pairind =
  syncTrm_ind
  |> Q.SPEC ‘λk (s,c) τ. P k s c τ’
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN ‘P’

Definition not_finish_def[simp]:
  not_finish c = (c ≠ Nil ∧ ∀x. c ≠ Call x)
End

Theorem not_BoolV:
  x ≠ BoolV T ∧ x ≠ BoolV F ⇒ ¬is_BoolV x
Proof
  Cases_on ‘x’ >> simp[]
QED

(* lemma for let_val case in chor_tag_trans *)
Theorem no_undefined_vars_fv_localise_let:
  no_undefined_vars (s,Let v p e c) ⇒
  free_vars e ⊆ FDOM (localise s p)
Proof
  rw[no_undefined_vars_def, free_variables_def, subset_fdom_localise_state]
QED

(* A choreography can always advance synchronously consuming
   the operation at the front
 *)
Theorem chor_tag_trans:
  ∀s c k p.
   no_undefined_vars (s,c)
   ∧ not_finish c
   ∧ no_self_comunication c
   ∧ syncTrm k (s,c) (chor_tag s c) = SOME p
   ⇒ trans (s,c) (chor_tag s c,[]) p
Proof
  rw [] \\ Cases_on ‘c’
  \\ fs [ chor_tag_def,syncTrm_def,chor_match_def
        , chor_tl_def,no_self_comunication_def]
  \\ rveq >~
  [‘IfThen v p c1 c2’]
  >- (IF_CASES_TAC
      >- fs [trans_if_true]
      \\ drule no_undefined_FLOOKUP_if \\ rw [] \\ fs []
      >- fs [trans_if_false]
      >> irule trans_if_exn >> metis_tac[is_BoolV_def, not_BoolV]) >~
  [‘Com p1 v1 p2 v2 c’]
  >- (Cases_on ‘FLOOKUP s (v1,p1)’ >> gvs[]
      >- (drule no_undefined_FLOOKUP_com >> simp[]) >~
      [‘FLOOKUP _ _ = SOME v’]
      >> Cases_on ‘v’ >> gvs[] >>~-
                            ([‘LComExn’], irule trans_com_exn >> simp[])
      >> gvs[chor_match_def] >> irule trans_com >> simp[]) >~
  [‘Let v p e c’]
  >- (CASE_TAC
      >- gvs[chor_match_def]
      >> (qpat_x_assum ‘(some) _ = SOME _’ mp_tac >>
          DEEP_INTRO_TAC some_intro >> simp[] >> strip_tac >>
          gvs[chor_match_def] >>
          Cases_on ‘eval_exp cl (localise s p) e’ >> gvs[] >>
          metis_tac[trans_letval, no_undefined_vars_fv_localise_let, trans_letexn]))
  >> fs [trans_sel,trans_fix]
QED

(* ‘syncTrm’ preserves does not remove any variable from the state *)
Theorem no_undefined_syncTrm:
  ∀k s c τ p.
    no_undefined_vars (s,c) ∧ syncTrm k (s,c) τ = SOME p
    ⇒ no_undefined_vars p
Proof
  ho_match_mp_tac syncTrm_pairind >>
  rw [syncTrm_def,chor_tl_def,
      no_undefined_vars_def,
      free_variables_def,
      free_variables_dsubst_eq_Fix,
      DELETE_SUBSET_INSERT] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >~
  [‘chor_match _ (Let v p e c)’]
  >- rw[AllCaseEqs(), no_undefined_vars_def, free_variables_def] >~
  [‘~chor_match _ (Let v p e c)’]
  >- (Cases_on ‘some ev. ∃cl. eval_exp cl (localise s p) e = Value ev’ >>
      gvs[no_undefined_vars_def, syncTrm_def]) >~
  [‘chor_match l (Com p1 s1 p2 s2 c)’, ‘FLOOKUP s’]
  >> Cases_on ‘FLOOKUP s (s1,p1)’ >> simp[no_undefined_vars_def, free_variables_def] >~
  [‘FLOOKUP _ _ = SOME v’] >> Cases_on ‘v’ >> simp[no_undefined_vars_def, free_variables_def]
QED

(* ‘syncTrm’ does not add self communicating operation into the choreography *)
Theorem no_self_comunication_syncTrm:
  ∀k s c τ q r. no_self_comunication c ∧ syncTrm k (s,c) τ = SOME (q,r) ⇒ no_self_comunication r
Proof
  ho_match_mp_tac syncTrm_pairind
  \\ rw [syncTrm_def,chor_tl_def,
         free_variables_dsubst_eq_Fix,
         no_self_comunication_dsubst,
         no_self_comunication_def]
  \\ rw [no_self_comunication_def] >~
  [‘~chor_match l (Com p1 s1 p2 s2 c)’]
  >- ( gvs[AllCaseEqs()]) >~
  [‘chor_match l (Com p1 s1 p2 s2 c)’]
  >- ( gvs[AllCaseEqs(), no_self_comunication_def]) >~
  [‘chor_match l (Let _ _ _ _)’]
  >-  ( gvs[AllCaseEqs(), no_self_comunication_def]) >~
  [‘~chor_match _ (Let e1 p e2 c)’]
  >> (Cases_on ‘some ev. ∃cl. eval_exp cl (localise s p) e2 = Value ev’ >>
      gvs[no_self_comunication_def])
QED

(* Basic RTC rules (reflexivity) *)
Theorem trans_sync_refl:
  ∀p. trans_sync p p
Proof
  rw [trans_sync_def,RTC_RULES]
QED

(* Basic RTC rules (single step) *)
Theorem trans_sync_step:
  ∀p p' τ q. trans p (τ,[]) p' ∧ trans_sync p' q ⇒ trans_sync p q
Proof
  rw [trans_sync_def] \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘p'’ \\ rw []
  \\ asm_exists_tac \\ fs []
QED

(* Basic RTC rules (transitivity) *)
Theorem trans_sync_trans:
  ∀p p' q. trans_sync p p' ∧ trans_sync p' q ⇒ trans_sync p q
Proof
  metis_tac [trans_sync_def,RTC_RTC]
QED

(* Basic RTC rules (id) *)
Theorem trans_sync_one:
  ∀p τ q. trans p (τ,[]) q ⇒ trans_sync p q
Proof
  rw [trans_sync_def] \\ ho_match_mp_tac RTC_SINGLE
  \\ asm_exists_tac \\ fs []
QED

(* One can synchronously consume as much of a choreography
   as needed to perform any tag operation. If the tag
   does not match anything in the choreography we just
   consume the whole thing.
*)
Theorem Trm_trans:
  ∀s c τ k p.
   no_undefined_vars (s,c) ∧
   no_self_comunication c ∧
   syncTrm k (s,c) τ = SOME p
   ⇒ trans_sync (s,c) p
Proof
  rw []
  \\ drule chor_tag_trans \\ rw []
  \\ rpt (first_x_assum mp_tac)
  \\ MAP_EVERY Q.SPEC_TAC [(‘p’,‘p’),(‘τ’,‘τ’),(‘c’,‘c’),(‘s’,‘s’),(‘k’,‘k’)]
  \\ ho_match_mp_tac syncTrm_pairind
  \\ rw [ no_self_comunication_def
        , no_self_comunication_dsubst
        , free_variables_dsubst_eq_Fix
        , no_undefined_vars_def
        , syncTrm_def
        , chor_match_def
        , chor_tl_def
        , free_variables_def
        , trans_sync_one
        , trans_sync_refl
        , chor_tag_def]
  (* if *) >~
  [‘chor_match l (IfThen v p c1 c2)’, ‘FLOOKUP s (v,p) ≠ SOME (BoolV F)’, ‘FLOOKUP s (v,p) ≠ SOME (BoolV T)’]
  >- (gvs[] >> irule trans_sync_one >> first_assum (irule_at Any) >> first_assum (irule_at Any)) >~
  [‘¬chor_match l (IfThen v p c1 c2)’, ‘FLOOKUP s (v,p) = SOME (BoolV T)’, ‘FLOOKUP s (v,p) = SOME (BoolV F)’]
  >- (gvs[] >> irule trans_sync_one >> first_assum (irule_at Any) >> first_assum (irule_at Any)) >>~-
  ([‘IfThen v p c1 c2’], first_x_assum $ drule_all_then $ strip_assume_tac >>
                         ho_match_mp_tac trans_sync_step \\ asm_exists_tac \\ fs [] >> rw[trans_sync_refl] >>
                         first_x_assum irule \\ rw [] >>
                         TRY (irule chor_tag_trans) >>
                         fs [no_undefined_vars_def,DELETE_SUBSET_INSERT] >>
                         rw [no_self_comunication_dsubst, no_self_comunication_def, free_variables_dsubst_eq_Fix] >>
                         asm_exists_tac \\ fs [])
  (* com *) >~
  [‘chor_match τ (Com p1 v1 p2 v2 c)’]
  >- (Cases_on ‘τ’ >~
      [‘chor_match (LCom p1 v1 p2 v2) _’]
      >- (Cases_on ‘FLOOKUP s (v1',p1')’
          >- (gvs[chor_match_def] >>
              first_x_assum $ drule_all_then $ strip_assume_tac >>
              irule trans_sync_one >> metis_tac[])
          >> (Cases_on ‘x’ >> gvs[chor_match_def] >>
              first_x_assum $ drule_all_then $ strip_assume_tac >>
              irule trans_sync_one >> metis_tac[])) >~
      [‘chor_match (LComExn p1 v1 p2 v2) _’]
      >- (Cases_on ‘FLOOKUP s (v1',p1')’
          >- (gvs[chor_match_def] >>
              first_x_assum $ drule_all_then $ strip_assume_tac >>
              irule trans_sync_one >> metis_tac[])
          >> (Cases_on ‘x’ >> gvs[chor_match_def] >>
              first_x_assum $ drule_all_then $ strip_assume_tac >>
              irule trans_sync_one >> metis_tac[]))
      >> gvs[chor_match_def]) >~
  [‘¬chor_match τ (Com p1 v1 p2 v2 c)’]
  >- (gvs[AllCaseEqs(), PULL_EXISTS, some_def, chor_match_def] >>
      first_x_assum $ drule_all_then $ strip_assume_tac >>
      ho_match_mp_tac trans_sync_step \\ asm_exists_tac \\ fs [] >>
      first_x_assum irule \\ rw [] >>
      TRY (irule chor_tag_trans) >>
      fs [no_undefined_vars_def,DELETE_SUBSET_INSERT] >>
      rw [no_self_comunication_dsubst, no_self_comunication_def, free_variables_dsubst_eq_Fix] >>
      asm_exists_tac \\ fs [])
  (* Let *) >~
  [‘chor_match l (Let v p e c)’]
  >- (qmatch_asmsub_abbrev_tac ‘¬is_bad_label (option_CASE B _ _)’ >>
      qmatch_asmsub_abbrev_tac ‘syncTrm _ (option_CASE A _ _) _’ >>
      Cases_on ‘A’ >> gvs[] >> Cases_on ‘B’ >> gvs[] >>
      pop_assum mp_tac >> pop_assum mp_tac >>
      rpt (DEEP_INTRO_TAC some_intro >> simp[] >> strip_tac)
      >- (Cases_on ‘x’ >> gvs[chor_match_def] >> irule trans_sync_one >> metis_tac[])
      >> (Cases_on ‘x'’ >> gvs[chor_match_def] >> irule trans_sync_one >> metis_tac[]))
  >- (qmatch_asmsub_abbrev_tac ‘¬is_bad_label (option_CASE B _ _)’ >>
      qmatch_asmsub_abbrev_tac ‘syncTrm _ (option_CASE A _ _) _’ >>
      Cases_on ‘A’ >> gvs[] >> Cases_on ‘B’ >> gvs[] >>
      pop_assum mp_tac >> pop_assum mp_tac >>
      rpt (DEEP_INTRO_TAC some_intro >> simp[] >> strip_tac)
      >- gvs[syncTrm_def]
      >- (Cases_on ‘x’ >> gvs[chor_match_def, syncTrm_def])
      >- (Cases_on ‘x'’ >> gvs[chor_match_def] >> ho_match_mp_tac trans_sync_step
          >- (‘trans_sync (s |+ ((k',p),x),c) p'’ suffices_by metis_tac[clock_eval_exp_unique] >>
              first_assum (irule_at Any) >>
              ‘free_variables c ⊆ FDOM (s |+ ((k',p),x))’ by metis_tac[DELETE_DEF, FDOM_FUPDATE, INSERT_SING_UNION, subset_diff_update, UNION_COMM] >>
              ‘free_variables c ⊆ (k',p) INSERT FDOM s’ by gvs[FDOM_FUPDATE] >> simp[] >>
              Cases_on ‘(c ≠ Nil ∧ ∀x. c ≠ Call x)’ >> simp[] >>
              ‘no_undefined_vars (s |+ ((k',p),x),c)’ by simp[no_undefined_vars_def] >>
              drule chor_tag_trans >> strip_tac >> metis_tac[not_finish_def])
          >> metis_tac[clock_eval_exp_typeerr_false, clock_eval_exp_exn_false]))
  >> (first_x_assum (qspec_then ‘k’ assume_tac) \\ rfs []
  \\ TRY (ho_match_mp_tac trans_sync_one \\ asm_exists_tac \\ fs [])
  \\ ho_match_mp_tac trans_sync_step \\ asm_exists_tac \\ fs []
  \\ first_x_assum irule \\ rw []
  \\ TRY (irule chor_tag_trans)
  \\ fs [no_undefined_vars_def,DELETE_SUBSET_INSERT]
  \\ rw [no_self_comunication_dsubst
         , no_self_comunication_def
         , free_variables_dsubst_eq_Fix]
  \\ asm_exists_tac \\ fs [])
QED

Theorem dprocsOf_empty:
  ∀c. dprocsOf [] c = procsOf c
Proof
  ‘∀c dvars. EVERY ($= []) (MAP SND dvars) ⇒ dprocsOf dvars c = procsOf c’
    by(Induct >>
       rw[dprocsOf_def,procsOf_def] >>
       TOP_CASE_TAC >> fs[EVERY_MEM] >>
       imp_res_tac ALOOKUP_MEM >>
       fs[MEM_MAP,PULL_EXISTS] >>
       res_tac >> fs[]) >>
  first_x_assum match_mp_tac >> simp[]
QED

Theorem procsOf_dprocsOf_SUBSET:
  ∀dvars c.
    set(procsOf c) ⊆ set(dprocsOf dvars c)
Proof
  simp[SUBSET_DEF] >>
  Induct_on ‘c’ >>
  rw[procsOf_def,dprocsOf_def,set_nub'] >>
  fs[]
QED

Theorem procsOf_dprocsOf_MEM:
  ∀proc dvars c.
    MEM proc (procsOf c) ⇒ MEM proc (dprocsOf dvars c)
Proof
  metis_tac[procsOf_dprocsOf_SUBSET,SUBSET_DEF]
QED

Theorem dprocsOf_MEM_IMP:
  ∀proc dvars c.
    MEM proc (dprocsOf dvars c) ⇒
    MEM proc (procsOf c) ∨
    ∃dn procs.
      MEM dn (dvarsOf c) ∧
      ALOOKUP dvars dn = SOME procs ∧
      MEM proc procs
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(PURE_FULL_CASE_TAC >> fs[]) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ ALOOKUP dvars dn = ALOOKUP dvars' dn) ⇒
    dprocsOf dvars c = dprocsOf dvars' c
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(PURE_FULL_CASE_TAC >> fs[]) >>
  TRY(AP_TERM_TAC >>
      first_x_assum match_mp_tac >>
      rw[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ':
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ the [] (ALOOKUP dvars dn) = the [] (ALOOKUP dvars' dn)) ⇒
    dprocsOf dvars c = dprocsOf dvars' c
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def]) >> NO_TAC) >>
  TRY(AP_TERM_TAC >>
      first_x_assum match_mp_tac >>
      rw[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ_set:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ set(the [] (ALOOKUP dvars dn)) = set(the [] (ALOOKUP dvars' dn))) ⇒
    set(dprocsOf dvars c) = set(dprocsOf dvars' c)
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,set_nub',MEM_FILTER,PULL_EXISTS] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(last_x_assum match_mp_tac >> rw[] >> NO_TAC) >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def]) >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ_set_opt:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ OPTREL (λx y. set x = set y) (ALOOKUP dvars dn) (ALOOKUP dvars' dn)) ⇒
    set(dprocsOf dvars c) = set(dprocsOf dvars' c)
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,set_nub',MEM_FILTER,PULL_EXISTS] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(last_x_assum match_mp_tac >> rw[] >> NO_TAC) >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def]) >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_init_dup:
  dprocsOf ((dn,dvs)::(dn,dvs')::dvars) c = dprocsOf ((dn,dvs)::dvars) c
Proof
  match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]
QED

Theorem dprocsOf_init_swap:
  dn ≠ dn' ⇒
  dprocsOf ((dn',dvs')::(dn,dvs)::dvars) c = dprocsOf ((dn,dvs)::(dn',dvs')::dvars) c
Proof
  strip_tac >> match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]
QED

Theorem nub'_nil:
  nub' l = [] ⇔ l = []
Proof
  Cases_on ‘l’ >> rw[nub'_def]
QED

Theorem dprocsOf_dvarsOf_empty:
  ∀dvars c.
  dvarsOf c = [] ⇒
  dprocsOf dvars c = dprocsOf [] c
Proof
  rpt strip_tac >>
  match_mp_tac dprocsOf_ALOOKUP_EQ' >>
  rw[]
QED

Theorem dprocsOf_dvarsOf_empty_cons:
  ∀dvars dv c.
  dvarsOf(Fix dn c) = [] ⇒
  dprocsOf ((dn,[])::dvars) c = dprocsOf [] c
Proof
  rpt strip_tac >>
  match_mp_tac dprocsOf_ALOOKUP_EQ' >>
  rw[] >> fs[dvarsOf_def,FILTER_EQ_NIL,EVERY_MEM,MEM_nub',libTheory.the_def] >>
  res_tac >> fs[]
QED

Triviality ALOOKUP_FILTER':
  ALOOKUP (FILTER (λkv. P (FST kv)) ls) x =
  if P x then ALOOKUP ls x else NONE
Proof
  Induct_on ‘ls’ >- rw[] >>
  Cases >> rw[] >> rw[] >>
  metis_tac[]
QED

Theorem dprocsOf_nil:
  dprocsOf ((dn,[])::dvars) c = dprocsOf (FILTER ($<> dn o FST) dvars) c
Proof
  match_mp_tac dprocsOf_ALOOKUP_EQ' >> rw[ALOOKUP_FILTER',o_DEF,libTheory.the_def]
QED

(* TODO: move to choreoUtils *)
Theorem nub'_FILTER:
  ∀P l. nub'(FILTER P l) = FILTER P (nub' l)
Proof
  Induct_on ‘l’ >> rw[nub'_def,FILTER_FILTER] >>
  simp[CONJ_SYM] >>
  rw[FILTER_EQ,EQ_IMP_THM]
QED

Theorem nub'_idem:
  ∀l. nub'(nub' l) = nub' l
Proof
  Induct >>
  rw[nub'_def,nub'_FILTER,FILTER_FILTER]
QED

Theorem nub'_dvarsOf:
  ∀c. nub'(dvarsOf c) = dvarsOf c
Proof
  Induct >> rw[dvarsOf_def,nub'_idem,nub'_FILTER] >> rw[nub'_def]
QED

Theorem dprocsOf_MEM_eq:
  MEM proc (dprocsOf dvars c) ⇔
  MEM proc (procsOf c) ∨
  ∃dn procs.
    MEM dn (dvarsOf c) ∧ ALOOKUP dvars dn = SOME procs ∧
    MEM proc procs
Proof
  rw[EQ_IMP_THM]
  >- (imp_res_tac dprocsOf_MEM_IMP >> fs[] >> metis_tac[])
  >- (drule_then MATCH_ACCEPT_TAC procsOf_dprocsOf_MEM)
  >- (rpt(pop_assum mp_tac) >>
      qid_spec_tac ‘dvars’ >>
      Induct_on ‘c’ >>
      rw[dvarsOf_def,dprocsOf_def,MEM_nub'] >>
      res_tac >> fs[] >>
      fs[MEM_FILTER,MEM_nub'])
QED

Theorem set_procsOf_dsubst_eq:
  ∀c dn c'.
    set (procsOf (dsubst c dn c')) =
    set (procsOf c) ∪
    (if MEM dn (dvarsOf c) then set (procsOf c') else {})
Proof
  Induct_on ‘c’ >> rw[procsOf_def,chorLangTheory.dsubst_def,set_nub',dvarsOf_def] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF] >>
  fs[MEM_FILTER,MEM_nub']
QED

Theorem dsubst_vacuous:
  ∀dn c c'.
  ~MEM dn (dvarsOf c) ⇒ dsubst c dn c' = c
Proof
  rpt strip_tac >> Induct_on ‘c’ >> rw[dvarsOf_def,chorLangTheory.dsubst_def,MEM_nub',MEM_FILTER]
QED

Theorem set_dvarsOf_dsubst_eq:
  ∀c dn c'.
    dvarsOf c' = [] ⇒
    set (dvarsOf (dsubst c dn c')) = (set (dvarsOf c) DIFF {dn})
Proof
  rpt strip_tac >>
  Induct_on ‘c’ >> rw[dvarsOf_def,chorLangTheory.dsubst_def,set_nub',dvarsOf_def] >>
  gs[] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_FILTER,MEM_nub'] >> fs[]
QED

Definition variables_def:
  (variables (chorLang$Nil) = {}) /\
  (variables (Call x) = {}) /\
  (variables (Fix x c) = variables c) /\
  (variables (IfThen v p c1 c2) = {(v,p)} ∪ (variables c1 ∪ variables c2)) /\
  (variables (Com p1 v1 p2 v2 c) = {(v1,p1);(v2,p2)} ∪ (variables c)) /\
  (variables (Let v p e c) = {(s, p) | s ∈ free_vars e} ∪ {(v,p)} ∪ variables c) /\
  (variables (Sel p b q c) = variables c)
End

Theorem dsubst_subset_variables:
  ∀c c' dn.
    variables (dsubst c dn c') ⊆ variables c ∪ variables c'
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [variables_def,dsubst_def]
  \\ fs [variables_def,dsubst_def]
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []
QED

Theorem variables_subset_dsubst:
  ∀c c' dn.
    variables c ⊆ variables (dsubst c dn c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [variables_def,dsubst_def]
  \\ fs [SUBSET_DEF]
QED

Theorem variables_dsubst_eq:
  ∀c dn. variables (dsubst c dn c) = variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [variables_subset_dsubst,
                dsubst_subset_variables,
                UNION_IDEMPOT]
QED

Theorem variables_dsubst_eq_Fix:
  ∀c x y. variables (dsubst c x (Fix y c)) = variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [variables_subset_dsubst,
                dsubst_subset_variables,
                variables_def,
                UNION_IDEMPOT]
QED

Theorem trans_variables_mono:
  ∀s c a l s' c'.
  trans (s,c) (a,l) (s',c') ⇒
  variables c' ⊆ variables c
Proof
  ho_match_mp_tac trans_pairind >>
  rw[variables_def,variables_dsubst_eq_Fix] >>
  fs[SUBSET_DEF]
QED

Theorem trans_s_variables_mono:
  ∀s c s' c'.
  trans_s (s,c) (s',c') ⇒
  variables c' ⊆ variables c
Proof
  rpt strip_tac >>
  ‘(∀sc sc'. (λp q. ∃s. chorSem$trans p s q) sc sc' ⇒ combin$C pred_set$SUBSET ((λ(s,c). variables c) sc) ((λ(s,c). variables c) sc'))’
    by(Cases >> Cases >> rw[] >> rename1 ‘trans _ a _’ >> Cases_on ‘a’ >> metis_tac[trans_variables_mono]) >>
  dxrule RTC_lifts_reflexive_transitive_relations >>
  disch_then(qspecl_then [‘(s,c)’,‘(s',c')’] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  fs[trans_s_def] >>
  fs[reflexive_def,transitive_def] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem free_variables_variables:
  free_variables c ⊆ variables c
Proof
  Induct_on ‘c’ >> rw[free_variables_def,variables_def] >> fs[SUBSET_DEF] >> rw[] >> res_tac
QED

val _ = export_theory ()
