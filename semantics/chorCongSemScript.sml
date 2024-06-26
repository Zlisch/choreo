open preamble chorLangTheory envSemTheory

(* Semantics with build-in congruence *)
val _ = new_theory "chorCongSem";

val _ = Datatype`
  label = LTau proc (varN option)
        | LCom proc varN proc varN
        | LSel proc bool proc
`;

val freeprocs_def = Define`
  freeprocs (LTau p v)          = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
`;

val sender_def = Define`
  sender (LTau p v)          = NONE
∧ sender (LCom p1 v1 p2 v2) = SOME p1
∧ sender (LSel p1 b p2)     = SOME p1
`;

val receiver_def = Define`
  receiver (LTau p v)          = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
`;

val written_def = Define`
  written (LTau p NONE)       = NONE
∧ written (LTau p (SOME v))  = SOME(v,p)
∧ written (LCom p1 v1 p2 v2) = SOME(v2,p2)
∧ written (LSel p1 b p2)     = NONE
`;


val (scong_rules, scong_ind, scong_cases) = Hol_reln `
(* Basic pre-congruence rules *)

  (* Symmetric *)
  (∀c. scong c c)

  (* Transitive *)
∧ (∀c1 c2 c3.
     scong c1 c2
     ∧ scong c2 c3
     ⇒ scong c1 c3)

(* Swapping rules *)

(* Swapping communications and selections is only posible if the
   processes involved in each operations are different (all of them)
*)

∧ (∀p1 p2 p3 p4 v1 v2 v3 v4 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Com p1 v1 p2 v2 (Com p3 v3 p4 v4 c))
            (Com p3 v3 p4 v4 (Com p1 v1 p2 v2 c)))

∧ (∀p1 p2 p3 p4 v1 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Sel p1 v1 p2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Sel p1 v1 p2 c)))

(* L to R *)
∧ (∀p1 p2 p3 p4 v1 v2 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Com p1 v1 p2 v2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Com p1 v1 p2 v2 c)))

(* R to L *)
∧ (∀p1 p2 p3 p4 v1 v2 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Sel p3 v3 p4 (Com p1 v1 p2 v2 c))
            (Com p1 v1 p2 v2 (Sel p3 v3 p4 c)))


(* Let swaps need to make sure no pair of process and variable is
   shared betwen operations (this includes the arguments to the let
   function)
*)
∧ (∀v v' p p' e e' c.
    p ≠ p'
    ⇒ scong (Let v p e (Let v' p' e' c))
           (Let v' p' e' (Let v p e c)))

(* L to R *)
∧ (∀p1 p2 p3 v1 v2 v3 e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ scong (Com p1 v1 p2 v2 (Let v3 p3 e c))
            (Let v3 p3 e (Com p1 v1 p2 v2 c)))
∧ (∀p1 p2 p3 b v e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ scong (Sel p1 b p2 (Let v p3 e c))
            (Let v p3 e (Sel p1 b p2 c)))

(* R to L *)
∧ (∀p1 p2 p3 v1 v2 v3 e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ scong (Let v3 p3 e (Com p1 v1 p2 v2 c))
            (Com p1 v1 p2 v2 (Let v3 p3 e c)))
∧ (∀p1 p2 p3 b v e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ scong (Let v p3 e (Sel p1 b p2 c))
            (Sel p1 b p2 (Let v p3 e c)))

(* If Rules *)
∧ (∀p q e1 e2 c1 c2 c1' c2'.
    p ≠ q
    ⇒ scong (IfThen e1 p (IfThen e2 q c1 c2)  (IfThen e2 q c1' c2'))
            (IfThen e2 q (IfThen e1 p c1 c1') (IfThen e1 p c2  c2')))

(* L to R *)
∧ (∀p1 p2 p v1 v2 c1 c2 e.
    p ∉ {p1;p2}
    ⇒ scong (Com p1 v1 p2 v2 (IfThen e p c1 c2))
            (IfThen e p (Com p1 v1 p2 v2 c1) (Com p1 v1 p2 v2 c2)))
∧ (∀p1 p2 b c1 c2 p e.
    p ∉ {p1;p2}
    ⇒ scong (Sel p1 b p2 (IfThen e p c1 c2))
            (IfThen e p (Sel p1 b p2 c1) (Sel p1 b p2 c2)))
∧ (∀p1 p2 v e ep c1 c2.
    p1 ≠ p2
    ⇒ scong (Let v p1 ep (IfThen e p2 c1 c2))
            (IfThen e p2 (Let v p1 ep c1) (Let v p1 ep c2)))

(* R to L *)
∧ (∀p1 p2 p v1 v2 c1 c2 e.
    p ∉ {p1;p2}
    ⇒ scong (IfThen e p (Com p1 v1 p2 v2 c1) (Com p1 v1 p2 v2 c2))
            (Com p1 v1 p2 v2 (IfThen e p c1 c2)))
∧ (∀p1 p2 b c1 c2 p e.
    p ∉ {p1;p2}
    ⇒ scong (IfThen e p (Sel p1 b p2 c1) (Sel p1 b p2 c2))
            (Sel p1 b p2 (IfThen e p c1 c2)))
∧ (∀p1 p2 v e ep c1 c2.
    p1 ≠ p2
    ⇒ scong (IfThen e p2 (Let v p1 ep c1) (Let v p1 ep c2))
            (Let v p1 ep (IfThen e p2 c1 c2)))

  (* Structural rules *)
∧ (∀p e c1 c1' c2 c2'.
    scong c1 c1'
    ∧ scong c2 c2'
    ⇒ scong (IfThen e p c1 c2) (IfThen e p c1' c2'))
∧ (∀p v e c c'.
    scong c c'
    ⇒ scong (Let v p e c) (Let v p e c'))
∧ (∀p1 v1 p2 v2 c c'.
    scong c c'
    ⇒ scong (Com p1 v1 p2 v2 c) (Com p1 v1 p2 v2 c'))
∧ (∀p1 b p2 c c'.
    scong c c'
    ⇒ scong (Sel p1 b p2 c) (Sel p1 b p2 c'))

  (* Recursion *)
∧ (∀x c. scong (Fix x c) (dsubst c x (Fix x c)))
`;

val _ = Parse.add_infix("≲",425,Parse.NONASSOC);
val _ = Parse.overload_on("≲",``scong``);

val _ = zip ["scong_refl", "scong_trans"
            , "scong_com_swap", "scong_sel_swap"
            , "scong_com_sel_swap","scong_sel_com_swap"
            , "scong_let_swap"
            , "scong_com_let_swap" , "scong_sel_let_swap"
            , "scong_let_com_swap" , "scong_let_sel_swap"
            , "scong_if_swap"
            , "scong_com_if_swap" , "scong_sel_if_swap", "scong_let_if_swap"
            , "scong_if_com_swap" , "scong_if_sel_swap", "scong_if_let_swap"
            , "scong_if", "scong_let", "scong_com", "scong_sel"
            , "scong_fix"]
            (CONJUNCTS scong_rules) |> map save_thm;

Inductive transCong:
  (* Communication *)
[~com:]  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ transCong (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2) (s |+ ((v2,p2),d),c))

  (* Selection *)
[~sel:] (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ transCong (s,Sel p1 b p2 c) (LSel p1 b p2) (s,c))

  (* Letval *)
[~let:] (∀s v p e c cl ev.
    eval_exp cl (localise s p) e = Value ev
    ⇒ transCong (s,Let v p e c)
                (LTau p (SOME v))
                (s |+ ((v,p), ev),c))

(* Letexn *)
[~letexn:] (∀s v p e c cl exn.
    eval_exp cl (localise s p) e = Exn exn
    ⇒ transCong (s,Let v p e c)
                (LTau p (SOME v))
                (s, Nil))
                
  (* If (True) *)
[~if_true:] (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME (BoolV T)
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p NONE) (s,c1))

  (* If (False) *)
[~if_false:] (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME (BoolV F)
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p NONE) (s,c2))

  (* Asynchrony *)
[~com_asynch:] (∀s c s' c' p1 v1 p2 v2 alpha.
    transCong (s,c) alpha (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ transCong (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))

[~sel_async:] (∀s c s' c' p1 b p2 alpha.
    transCong (s,c) alpha (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ transCong (s,Sel p1 b p2 c) alpha (s',Sel p1 b p2 c'))

  (* Congruence *)
[~cong:] (∀c1 c2 c1' c2' alpha.
    c1 ≲ c1'
    ∧ transCong (s,c1') alpha (s',c2')
    ∧ c2' ≲ c2
    ⇒ transCong (s,c1) alpha (s',c2))
End

val transCong_pairind = save_thm("transCong_pairind",
  theorem"transCong_strongind"
  |> Q.SPEC `λa0 a1 a2. P (FST a0) (SND a0) a1 (FST a2) (SND a2)`
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN `P`
);

val (lncong_rules, lncong_ind, lncong_cases) = Hol_reln `
(* Basic congruence rules *)

  (* Symmetric *)
  (∀c. lncong c c)

  (* Reflexive *)
∧ (∀c1 c2.
    lncong c1 c2
    ⇒ lncong c2 c1)

  (* Transitive *)
∧ (∀c1 c2 c3.
     lncong c1 c2
     ∧ lncong c2 c3
     ⇒ lncong c1 c3)

(* Swapping rules *)

(* Swapping communications and selections is only posible if the
   processes involved in each operations are diferent (all of them)
*)
∧ (∀p1 p2 p3 p4 v1 v2 v3 v4 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ lncong (Com p1 v1 p2 v2 (Com p3 v3 p4 v4 c))
            (Com p3 v3 p4 v4 (Com p1 v1 p2 v2 c)))
∧ (∀p1 p2 p3 p4 v1 v2 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ lncong (Com p1 v1 p2 v2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Com p1 v1 p2 v2 c)))
∧ (∀p1 p2 p3 p4 v1 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ lncong (Sel p1 v1 p2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Sel p1 v1 p2 c)))

(* Let swaps need to make sure no pair of process and variable is
   shared betwen operations (this includes the arguments to the let
   function)
*)
∧ (∀p1 p2 p3 v1 v2 v3 e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ lncong (Com p1 v1 p2 v2 (Let v3 p3 e c))
            (Let v3 p3 e (Com p1 v1 p2 v2 c)))
∧ (∀v v' p p' e e' c.
    p ≠ p'
    ⇒ lncong (Let v p e (Let v' p' e' c))
           (Let v' p' e' (Let v p e c)))
∧ (∀p1 p2 p3 b v e c.
    p1 ≠ p3 ∧ p2 ≠ p3
    ⇒ lncong (Sel p1 b p2 (Let v p3 e c))
            (Let v p3 e (Sel p1 b p2 c)))

(* If Rules *)
∧ (∀p q e1 e2 c1 c2 c1' c2'.
    p ≠ q
    ⇒ lncong (IfThen e1 p (IfThen e2 q c1 c2)  (IfThen e2 q c1' c2'))
            (IfThen e2 q (IfThen e1 p c1 c1') (IfThen e1 p c2  c2')))
∧ (∀p1 p2 p v1 v2 c1 c2 e.
    p ∉ {p1;p2}
    ⇒ lncong (Com p1 v1 p2 v2 (IfThen e p c1 c2))
            (IfThen e p (Com p1 v1 p2 v2 c1) (Com p1 v1 p2 v2 c2)))
∧ (∀p1 p2 b c1 c2 p e.
    p ∉ {p1;p2}
    ⇒ lncong (Sel p1 b p2 (IfThen e p c1 c2))
            (IfThen e p (Sel p1 b p2 c1) (Sel p1 b p2 c2)))
∧ (∀p1 p2 v e ep c1 c2.
    p1 ≠ p2
    ⇒ lncong (Let v p1 ep (IfThen e p2 c1 c2))
            (IfThen e p2 (Let v p1 ep c1) (Let v p1 ep c2)))

  (* Structural rules *)
∧ (∀p e c1 c1' c2 c2'.
    lncong c1 c1'
    ∧ lncong c2 c2'
    ⇒ lncong (IfThen e p c1 c2) (IfThen e p c1' c2'))
∧ (∀p v e c c'.
    lncong c c'
    ⇒ lncong (Let v p e c) (Let v p e c'))
∧ (∀p1 v1 p2 v2 c c'.
    lncong c c'
    ⇒ lncong (Com p1 v1 p2 v2 c) (Com p1 v1 p2 v2 c'))
∧ (∀p1 b p2 c c'.
    lncong c c'
    ⇒ lncong (Sel p1 b p2 c) (Sel p1 b p2 c'))
`;

val _ = Parse.add_infix("≅l",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅l",``lncong``);

val _ = zip ["lncong_refl", "lncong_sym", "lncong_trans"
            , "lncong_com_swap", "lncong_com_sel_swap"
            , "lncong_sel_swap", "lncong_com_let_swap"
            , "lncong_let_swap", "lncong_sel_let_swap"
            , "lncong_if_swap", "lncong_com_if_swap"
            , "lncong_sel_if_swap", "lncong_let_if_swap"
            , "lncong_if", "lncong_let", "lncong_com"
            , "lncong_sel"]
            (CONJUNCTS lncong_rules) |> map save_thm;

val (flcong_rules, flcong_ind, flcong_cases) = Hol_reln `
(* Basic pre-congruence rules *)

  (* Symmetric *)
  (∀c. flcong c c)

  (* Transitive *)
∧ (∀c1 c2 c3.
     flcong c1 c2
     ∧ flcong c2 c3
     ⇒ flcong c1 c3)

  (* Structural rules *)
∧ (∀p e c1 c1' c2 c2'.
    flcong c1 c1'
    ∧ flcong c2 c2'
    ⇒ flcong (IfThen e p c1 c2) (IfThen e p c1' c2'))
∧ (∀p v e c c'.
    flcong c c'
    ⇒ flcong (Let v p e c) (Let v p e c'))
∧ (∀p1 v1 p2 v2 c c'.
    flcong c c'
    ⇒ flcong (Com p1 v1 p2 v2 c) (Com p1 v1 p2 v2 c'))
∧ (∀p1 b p2 c c'.
    flcong c c'
    ⇒ flcong (Sel p1 b p2 c) (Sel p1 b p2 c'))

  (* Recursion *)
∧ (∀x c. flcong (Fix x c) (dsubst c x (Fix x c)))
`;

val _ = Parse.add_infix("≅⟩",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅⟩",``flcong``);

val _ = zip ["flcong_refl" , "flcong_trans"
            , "flcong_if"  , "flcong_let"
            , "flcong_com" , "flcong_sel"
            , "flcong_fix"]
            (CONJUNCTS flcong_rules) |> map save_thm;



val _ = export_theory ()
