(** * ContextTyping.PrimOpConcreteContext

    Concrete primitive-operation context for the current core operators.

    All concrete primitives use graph-precise result qualifiers.  Generator
    primitives take a unit argument; their graph relation enumerates all
    boolean or natural results. *)

From CoreLang Require Import BasicTyping BasicTypingProps SmallStep
  OperationalProps StrongNormalization.
From ContextBase Require Import BaseTactics.
From ContextLogic Require Import FormulaSemantics.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context ConstDenote TypeDenote TypeDenoteRegular TypeEquivCore
  TypeEquivFiberBaseCore TypeEquiv DenotationSetMapFacts TypePersistBase.
From ContextTyping Require Import PrimOpContext.

Definition topq : type_qualifier := qual_top.

Definition primop_R (op : prim_op) (vx vy : value) : Prop :=
  match op with
  | op_eq0 =>
      exists n, vx = vconst (cnat n) /\
        vy = vconst (cbool (n =? 0))
  | op_plus1 =>
      exists n, vx = vconst (cnat n) /\
        vy = vconst (cnat (S n))
  | op_minus1 =>
      exists n, vx = vconst (cnat n) /\
        vy = vconst (cnat (Nat.pred n))
  | op_boolGen =>
      exists b, vx = vconst cunit /\ vy = vconst (cbool b)
  | op_natGen =>
      exists n, vx = vconst cunit /\ vy = vconst (cnat n)
  end.

Definition primop_graph_qual (op : prim_op) : type_qualifier :=
  expr_result_qual (tprim op (vbvar 1)) (LVBound 0).

Ltac fold_over_result_body_in_goal :=
  match goal with
  | |- context [formula_open 0 ?y
        (FFibVars ?D
          (FOver (FAnd (FAtom ?φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase ?b))
              (tret (vbvar 0)) (TBase ?b)))))] =>
      change (formula_open 0 y
        (FFibVars D
          (FOver (FAnd (FAtom φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase b))
              (tret (vbvar 0)) (TBase b))))))
        with (formula_open 0 y (FFibVars D (over_result_body b φ)))
  | |- context [FOver (FAnd (FAtom ?φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b)))] =>
      change (FOver (FAnd (FAtom φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b))))
        with (over_result_body b φ)
  | H : context [FOver (FAnd (FAtom ?φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b)))] |- _ =>
      change (FOver (FAnd (FAtom φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b))))
        with (over_result_body b φ) in H
  | H : context [formula_open 0 ?y
        (FFibVars ?D
          (FOver (FAnd (FAtom ?φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase ?b))
              (tret (vbvar 0)) (TBase ?b)))))] |- _ =>
      change (formula_open 0 y
        (FFibVars D
          (FOver (FAnd (FAtom φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase b))
              (tret (vbvar 0)) (TBase b))))))
        with (formula_open 0 y (FFibVars D (over_result_body b φ))) in H
  end.

Ltac fold_under_result_body_in_goal :=
  match goal with
  | |- context [formula_open 0 ?y
        (FFibVars ?D
          (FUnder (FAnd (FAtom ?φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase ?b))
              (tret (vbvar 0)) (TBase ?b)))))] =>
      change (formula_open 0 y
        (FFibVars D
          (FUnder (FAnd (FAtom φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase b))
              (tret (vbvar 0)) (TBase b))))))
        with (formula_open 0 y (FFibVars D (under_result_body b φ)))
  | |- context [FUnder (FAnd (FAtom ?φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b)))] =>
      change (FUnder (FAnd (FAtom φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b))))
        with (under_result_body b φ)
  | H : context [FUnder (FAnd (FAtom ?φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b)))] |- _ =>
      change (FUnder (FAnd (FAtom φ)
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b))))
        with (under_result_body b φ) in H
  | H : context [formula_open 0 ?y
        (FFibVars ?D
          (FUnder (FAnd (FAtom ?φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase ?b))
              (tret (vbvar 0)) (TBase ?b)))))] |- _ =>
      change (formula_open 0 y
        (FFibVars D
          (FUnder (FAnd (FAtom φ)
            (expr_basic_typing_formula
              (typed_lty_env_bind ∅ (TBase b))
              (tret (vbvar 0)) (TBase b))))))
        with (formula_open 0 y (FFibVars D (under_result_body b φ))) in H
  end.

Ltac fold_result_basic_typing_formula_open :=
  match goal with
  | |- context [formula_open 0 ?y
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b))] =>
      change (formula_open 0 y
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b)))
        with (formula_open 0 y (result_basic_typing_formula b))
  | H : context [formula_open 0 ?y
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase ?b))
          (tret (vbvar 0)) (TBase ?b))] |- _ =>
      change (formula_open 0 y
        (expr_basic_typing_formula
          (typed_lty_env_bind ∅ (TBase b))
          (tret (vbvar 0)) (TBase b)))
        with (formula_open 0 y (result_basic_typing_formula b)) in H
  end.

Definition concrete_primop_sig (op : prim_op) : primop_sig :=
  match op with
  | op_eq0 =>
      mk_primop_sig TNat topq TBool (primop_graph_qual op_eq0)
  | op_plus1 =>
      mk_primop_sig TNat topq TNat (primop_graph_qual op_plus1)
  | op_minus1 =>
      mk_primop_sig TNat topq TNat (primop_graph_qual op_minus1)
  | op_boolGen =>
      mk_primop_sig TUnit topq TBool (primop_graph_qual op_boolGen)
  | op_natGen =>
      mk_primop_sig TUnit topq TNat (primop_graph_qual op_natGen)
  end.

Definition concrete_Φ : primop_ctx := concrete_primop_sig.

Local Lemma expr_eval_prim_fvar_result_has_ltype op x σ v :
  expr_eval_in_store σ (tprim op (vfvar x)) v ->
  basic_value_has_ltype ∅ v (TBase (prim_ret_base (concrete_Φ op))).
Proof.
  unfold expr_eval_in_store, lstore_instantiate_tm.
  cbn [lstore_instantiate_tm_at lstore_instantiate_tm_split_at
    lstore_instantiate_value_at lstore_instantiate_value_split_at].
  destruct (lstore_free_part σ !! x) as [vx|] eqn:Hx.
  - destruct vx; intros Hsteps.
    all: try (exfalso;
      destruct (steps_inv _ _ Hsteps) as [[Heq _]|[e' [Hstep _]]];
      [discriminate|inversion Hstep; subst; inversion H; subst; discriminate]).
    apply reduction_prim_const in Hsteps as [c' [Hstep ->]].
    inversion Hstep; subst; simpl; constructor.
  - intros Hsteps.
    exfalso.
    destruct (steps_inv _ _ Hsteps) as [[Heq _]|[e' [Hstep _]]].
    + discriminate.
    + inversion Hstep; subst; inversion H; subst; discriminate.
Qed.

Local Lemma typed_result_qual_prim_fvar_eq op x :
  typed_result_qual (prim_ret_base (concrete_Φ op))
    (expr_result_qual (tprim op (vfvar x)) (LVBound 0)) =
  expr_result_qual (tprim op (vfvar x)) (LVBound 0).
Proof.
  apply qual_ext.
  - unfold typed_result_qual, expr_result_qual.
    cbn [qual_lvars qual_vars tm_lvars tm_lvars_at value_lvars_at].
    set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    unfold typed_result_qual, expr_result_qual.
    cbn [qual_prop qual_lvars qual_vars lso_store storeAO_store].
    split.
    + intros [Hres _].
      destruct Hres as [Hfresh [v [Hlookup Heval]]].
      split; [exact Hfresh|].
      exists v. split.
      * unfold lstore_on_restrict, storeA_on_restrict in Hlookup.
        cbn [lso_store storeAO_store] in Hlookup.
        apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
        rewrite Hs in Hlookup. exact Hlookup.
      * apply (proj1 (expr_eval_in_store_restrict_lvars
          (tprim op (vfvar x)) s1
          (tm_lvars (tprim op (vfvar x)) ∪ {[LVBound 0]}) v
          ltac:(set_solver))) in Heval.
        rewrite Hs in Heval. exact Heval.
    + intros Hres.
      split.
      * unfold lstore_on_restrict, storeA_on_restrict.
        cbn [lso_store storeAO_store].
        rewrite Hs.
        apply expr_result_at_store_restrict_lvars; [set_solver|exact Hres].
      * destruct Hres as [_ [v [Hlookup Heval]]].
        exists v. split.
        -- rewrite Hs. exact Hlookup.
        -- eapply expr_eval_prim_fvar_result_has_ltype.
           exact Heval.
Qed.

Lemma primop_result_ty_eq op :
  primop_result_ty (concrete_Φ op) =
  match op with
  | op_eq0 => precise_ty TBool (primop_graph_qual op_eq0)
  | op_plus1 => precise_ty TNat (primop_graph_qual op_plus1)
  | op_minus1 => precise_ty TNat (primop_graph_qual op_minus1)
  | op_boolGen => precise_ty TBool (primop_graph_qual op_boolGen)
  | op_natGen => precise_ty TNat (primop_graph_qual op_natGen)
  end.
Proof.
  unfold primop_result_ty, concrete_Φ, concrete_primop_sig.
  destruct op; reflexivity.
Qed.

Lemma primop_arg_ty_eq op :
  primop_arg_ty (concrete_Φ op) =
  over_ty (prim_arg_base (concrete_Φ op)) qual_top.
Proof.
  unfold primop_arg_ty, concrete_Φ, concrete_primop_sig.
  destruct op; reflexivity.
Qed.

Lemma qual_top_lvars_wf_at d D :
  1 <= d ->
  lvars_wf_at d D (qual_vars topq).
Proof.
  intros Hd.
  unfold topq, qual_top_on. cbn [qual_vars qual_lvars].
  intros v Hv. apply elem_of_singleton in Hv as ->.
  cbn [lvar_wf_at]. lia.
Qed.

Lemma primop_graph_qual_lvars_wf_at d D op :
  2 <= d ->
  lvars_wf_at d D (qual_vars (primop_graph_qual op)).
Proof.
  intros Hd v Hv.
  unfold primop_graph_qual, expr_result_qual in Hv.
  cbn [qual_vars qual_lvars tm_lvars tm_lvars_at value_lvars_at
    bvar_lvars_at] in Hv.
  apply elem_of_union in Hv as [Hv|Hv].
  - unfold bvar_lvars_at in Hv.
    destruct (decide (0 <= 1)) as [_|Hbad]; [|lia].
    apply elem_of_singleton in Hv as ->.
    cbn [lvar_wf_at]. lia.
  - apply elem_of_singleton in Hv as ->.
    cbn [lvar_wf_at]. lia.
Qed.

Lemma over_top_basic b :
  basic_context_ty ∅ (CTOver b topq).
Proof.
  cbn [basic_context_ty wf_context_ty_at].
  apply qual_top_lvars_wf_at. lia.
Qed.

Lemma precise_top_wf_at d D b :
  wf_context_ty_at d D (precise_ty b topq).
Proof.
  unfold precise_ty, over_ty, under_ty.
  cbn [wf_context_ty_at erase_ty].
  repeat split; try reflexivity; apply qual_top_lvars_wf_at; lia.
Qed.

Lemma precise_graph_wf_at d D b op :
  1 <= d ->
  wf_context_ty_at d D (precise_ty b (primop_graph_qual op)).
Proof.
  intros Hd.
  unfold precise_ty, over_ty, under_ty.
  cbn [wf_context_ty_at erase_ty].
  repeat split; try reflexivity; apply primop_graph_qual_lvars_wf_at; lia.
Qed.

Lemma primop_erasure op :
  primop_erasure_ok op (concrete_Φ op).
Proof.
  unfold primop_erasure_ok, concrete_Φ, concrete_primop_sig.
  destruct op; reflexivity.
Qed.

Lemma primop_arg_basic op :
  basic_context_ty ∅ (primop_arg_ty (concrete_Φ op)).
Proof.
  rewrite primop_arg_ty_eq.
  apply over_top_basic.
Qed.

Lemma primop_result_wf op :
  wf_context_ty_at 1 ∅ (primop_result_ty (concrete_Φ op)).
Proof.
  rewrite primop_result_ty_eq.
  destruct op; try (apply precise_graph_wf_at; lia); apply precise_top_wf_at.
Qed.

Lemma prim_step_total_for_base op c arg_b ret_b :
  prim_op_type op = (arg_b, ret_b) ->
  base_ty_of_const c = arg_b ->
  exists c', prim_step op c c'.
Proof.
  intros Hop Hbase.
  destruct op; cbn [prim_op_type] in Hop;
    injection Hop as <- <-; destruct c; cbn in Hbase; try discriminate.
  - exists (cbool (n =? 0)). constructor.
  - exists (cnat (S n)). constructor.
  - exists (cnat (Nat.pred n)). constructor.
  - exists (cbool true). constructor.
  - exists (cnat 0). constructor.
Qed.

Lemma primop_arg_env_lookup op x :
  atom_env_to_lty_env
    (ctx_erasure_under ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))))
    !! LVFree x =
  Some (TBase (prim_arg_base (concrete_Φ op))).
Proof.
  rewrite ctx_erasure_under_bind.
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite primop_arg_ty_eq.
  cbn [erase_ty].
  apply map_lookup_union_Some_raw.
  right. split.
  - apply storeA_restrict_lookup_none_l. apply lookup_empty.
  - change ((<[x := TBase (prim_arg_base (concrete_Φ op))]>
        (∅ : gmap atom ty)) !! x =
      Some (TBase (prim_arg_base (concrete_Φ op)))).
    apply map_lookup_insert.
Qed.

Lemma primop_arg_erase_env_lookup op x :
  atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    !! LVFree x =
  Some (TBase (prim_arg_base (concrete_Φ op))).
Proof.
  cbn [erase_ctx].
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite primop_arg_ty_eq.
  cbn [erase_ty].
  change ((<[x := TBase (prim_arg_base (concrete_Φ op))]>
        (∅ : gmap atom ty)) !! x =
      Some (TBase (prim_arg_base (concrete_Φ op)))).
  apply map_lookup_insert.
Qed.

Lemma primop_result_ty_open_eq op x :
  {0 ~> x} (primop_result_ty (concrete_Φ op)) =
  match op with
  | op_eq0 =>
      precise_ty TBool (qual_open_atom 1 x (primop_graph_qual op_eq0))
  | op_plus1 =>
      precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_plus1))
  | op_minus1 =>
      precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_minus1))
  | op_boolGen =>
      precise_ty TBool (qual_open_atom 1 x (primop_graph_qual op_boolGen))
  | op_natGen =>
      precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_natGen))
  end.
Proof.
  rewrite primop_result_ty_eq.
  destruct op; unfold precise_ty, over_ty, under_ty, topq; cbn [cty_open].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma primop_arg_guard_formula
    op x (m : WfWorldT) :
  m ⊨ basic_world_formula
    (<[LVFree x := TBase (prim_arg_base (concrete_Φ op))]> ∅) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env
        (<[x := erase_ty (primop_arg_ty (concrete_Φ op))]>
          (∅ : gmap atom ty)))
      (primop_arg_ty (concrete_Φ op)) (tret (vfvar x)))
    (primop_arg_ty (concrete_Φ op)) (tret (vfvar x)).
Proof.
  intros Hworld_single.
  rewrite primop_arg_ty_eq.
  assert (Hworld :
    m ⊨ basic_world_formula
      (relevant_env
        (atom_env_to_lty_env
          (<[x := TBase (prim_arg_base (concrete_Φ op))]>
            (∅ : gmap atom ty)))
        (CTOver (prim_arg_base (concrete_Φ op)) topq)
        (tret (vfvar x)))).
  {
    eapply basic_world_formula_subenv; [|exact Hworld_single].
    intros v T Hlook.
    destruct v as [k|a].
    - unfold relevant_env, lty_env_restrict_lvars in Hlook.
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
      discriminate.
    - destruct (decide (a = x)) as [->|Hax].
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert in Hlook.
        rewrite decide_True in Hlook by reflexivity.
        transitivity (Some (TBase (prim_arg_base (concrete_Φ op)))).
        * apply map_lookup_insert.
        * exact Hlook.
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert_ne in Hlook by congruence.
        rewrite lookup_empty in Hlook. discriminate.
  }
  assert (Hbasic :
    m ⊨ expr_basic_typing_formula
      (relevant_env
        (atom_env_to_lty_env
          (<[x := TBase (prim_arg_base (concrete_Φ op))]>
            (∅ : gmap atom ty)))
        (CTOver (prim_arg_base (concrete_Φ op)) topq)
        (tret (vfvar x)))
      (tret (vfvar x)) (TBase (prim_arg_base (concrete_Φ op)))).
  {
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    constructor. constructor.
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2.
    - rewrite atom_store_to_lvar_store_lookup_free.
      unfold store_insert, store_empty.
      apply map_lookup_insert.
    - unfold relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars_at].
      unfold over_ty, topq, qual_top.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
      apply elem_of_union_r.
      apply elem_of_singleton. reflexivity.
  }
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    eapply (basic_context_ty_lvars_mono (lvars_of_atoms ∅)).
    + intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      rewrite elem_of_empty in Ha. contradiction.
    + apply basic_context_ty_to_lvars.
      rewrite <- primop_arg_ty_eq.
      apply primop_arg_basic.
  - split; [exact Hworld|]. split; [exact Hbasic|].
    eapply expr_total_formula_tret_of_basic; eauto.
Qed.

Lemma primop_arg_const_from_ctx
    op x (m : WfWorldT) σ :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  (m : WorldT) σ ->
  exists c,
    σ !! x = Some (vconst c) /\
    base_ty_of_const c = prim_arg_base (concrete_Φ op).
Proof.
  intros Hctx Hσ.
  pose proof (ctx_denote_under_basic_world
    ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))) m Hctx) as Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope Htyped]].
  assert (Hxworld : x ∈ world_dom (m : WorldT)).
  {
    apply Hscope. apply lvars_fv_elem.
    apply elem_of_dom. exists (TBase (prim_arg_base (concrete_Φ op))).
    apply primop_arg_env_lookup.
  }
  assert (Hxdom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hxworld.
  }
  change (x ∈ dom (σ : gmap atom value)) in Hxdom.
  apply elem_of_dom in Hxdom as [vx Hxσ].
  unfold lworld_has_type, worldA_has_type in Htyped.
  destruct Htyped as [_ Hstores].
  assert (Hlift : (res_lift_free m : LWorld) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  specialize (Hstores (lstore_lift_free σ) Hlift).
  pose proof (Hstores (LVFree x)
    (TBase (prim_arg_base (concrete_Φ op))) vx
    (primop_arg_env_lookup op x)) as Hval.
  rewrite lstore_lift_free_lookup_free in Hval.
  specialize (Hval Hxσ).
  apply basic_typing_base_canonical_form in Hval as [c [-> Hbase]].
  exists c. split; [exact Hxσ|exact Hbase].
Qed.

Lemma expr_total_formula_tprim_from_primop_arg
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_total_formula (tprim op (vfvar x)).
Proof.
  intros Hctx.
  apply expr_total_atom_world_to_formula.
  split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    cbn [tm_lvars tm_lvars_at value_lvars_at] in Hv.
    destruct v as [k|a].
    + apply elem_of_singleton in Hv. discriminate.
    + apply elem_of_singleton in Hv. inversion Hv. subst a.
      unfold lvars_of_atoms. apply elem_of_map.
      exists x. split; [reflexivity|].
      pose proof (ctx_denote_under_basic_world
        ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))) m Hctx) as Hworld.
      apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
      apply Hscope. apply lvars_fv_elem.
      apply elem_of_dom. exists (TBase (prim_arg_base (concrete_Φ op))).
      apply primop_arg_env_lookup.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
      as [c [Hxσ Hbase]].
    unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
    cbn [lstore_instantiate_tm_at lstore_instantiate_value_at].
    rewrite lstore_free_part_lift_free.
    cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
    change ((σ : gmap atom value) !! x = Some (vconst c)) in Hxσ.
    change (must_terminating
      (tprim op
        (match ((σ : gmap atom value) !! x) with
         | Some u => u
         | None => vfvar x
         end))).
    destruct ((σ : gmap atom value) !! x) as [vx|] eqn:Hlook.
    2:{ congruence. }
    assert (vx = vconst c) as -> by congruence.
    apply must_terminating_tprim_const.
    + constructor. constructor.
    + eapply prim_step_total_for_base.
      * apply primop_erasure.
	      * exact Hbase.
Qed.

Lemma expr_result_formula_self_atom_body e y (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree y) ->
  m ⊨ FFibVars (tm_lvars e)
    (FAtom (expr_result_qual e (LVFree y))).
Proof.
  intros Hexpr.
  apply res_models_FFibVars_iff in Hexpr as [Hscope [Hlc Hfib]].
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_fibvars, formula_fv_atom.
    unfold expr_result_qual, qual_dom, qual_vars.
    unfold expr_result_formula, expr_result_formula_at in Hscope.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope.
    unfold expr_result_qual, qual_dom, qual_vars in Hscope.
    set_solver.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store].
    exact Hfib.
Qed.

Lemma expr_result_formula_self_over_body e y (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree y) ->
  m ⊨ FFibVars (tm_lvars e)
    (FOver (FAtom (expr_result_qual e (LVFree y)))).
Proof.
  intros Hexpr.
  pose proof (expr_result_formula_self_atom_body e y m Hexpr) as Hatom.
  apply res_models_FFibVars_iff in Hatom as [Hscope [Hlc Hfib]].
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope.
    exact Hscope.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store].
    apply res_models_over_intro_same_from_model.
    exact Hfib.
Qed.

Lemma expr_result_formula_self_under_body e y (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree y) ->
  m ⊨ FFibVars (tm_lvars e)
    (FUnder (FAtom (expr_result_qual e (LVFree y)))).
Proof.
  intros Hexpr.
  pose proof (expr_result_formula_self_atom_body e y m Hexpr) as Hatom.
  apply res_models_FFibVars_iff in Hatom as [Hscope [Hlc Hfib]].
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope.
    exact Hscope.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store].
    apply res_models_under_intro_same_from_model.
    exact Hfib.
Qed.

Lemma expr_result_formula_at_self_atom_body D e y (m : WfWorldT) :
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (expr_result_qual e (LVFree y)) ∖ {[LVFree y]})
    (FAtom (expr_result_qual e (LVFree y))).
Proof.
  intros HeD HyD Hres.
  assert (Hsmall : tm_lvars e ⊆ D) by exact HeD.
  pose proof (expr_result_formula_at_coarsen_domain
    (tm_lvars e) D e y m Hsmall ltac:(set_solver) HyD Hres) as Hexpr.
  pose proof (expr_result_formula_self_atom_body e y m Hexpr) as Hatom.
  replace (qual_vars (expr_result_qual e (LVFree y)) ∖ {[LVFree y]})
    with (tm_lvars e) by (unfold expr_result_qual; cbn [qual_vars qual_lvars]; set_solver).
  exact Hatom.
Qed.

Lemma expr_result_formula_at_self_over_body D e y (m : WfWorldT) :
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (expr_result_qual e (LVFree y)) ∖ {[LVFree y]})
    (FOver (FAtom (expr_result_qual e (LVFree y)))).
Proof.
  intros HeD HyD Hres.
  pose proof (expr_result_formula_at_self_atom_body D e y m HeD HyD Hres)
    as Hatom.
  apply res_models_FFibVars_iff in Hatom as [Hscope [Hlc Hfib]].
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope.
    exact Hscope.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store].
    apply res_models_over_intro_same_from_model.
    exact Hfib.
Qed.

Lemma expr_result_formula_at_self_under_body D e y (m : WfWorldT) :
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (expr_result_qual e (LVFree y)) ∖ {[LVFree y]})
    (FUnder (FAtom (expr_result_qual e (LVFree y)))).
Proof.
  intros HeD HyD Hres.
  pose proof (expr_result_formula_at_self_atom_body D e y m HeD HyD Hres)
    as Hatom.
  apply res_models_FFibVars_iff in Hatom as [Hscope [Hlc Hfib]].
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope.
    exact Hscope.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store].
    apply res_models_under_intro_same_from_model.
    exact Hfib.
Qed.

Lemma qual_open_expr_result_qual_bound0 e y :
  lc_tm e ->
  y ∉ fv_tm e ->
  qual_open_atom 0 y (expr_result_qual e (LVBound 0)) =
  expr_result_qual e (LVFree y).
Proof.
  intros Hlc Hy.
  unfold expr_result_qual.
  apply qual_ext.
  - cbn [qual_lvars qual_open_atom].
    pose proof (tm_lvars_open_result_domain 0 y e (LVBound 0) Hy)
      as Hdom.
    rewrite (open_rec_lc_tm e Hlc 0 (vfvar y)) in Hdom.
    unfold swap in Hdom.
    repeat destruct decide; try congruence.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    split; intros Hres.
    + apply expr_result_at_store_open_back_iff in Hres.
      * change (expr_result_at_store e (LVFree y) (lso_store s2)).
        rewrite (open_rec_lc_tm e Hlc 0 (vfvar y)) in Hres.
        unfold swap in Hres.
        repeat destruct decide; try congruence.
        rewrite <- Hs. exact Hres.
      * exact Hy.
      * change (lvars_open 0 y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
    + apply expr_result_at_store_open_back_iff.
      * exact Hy.
      * change (lvars_open 0 y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
      * rewrite (open_rec_lc_tm e Hlc 0 (vfvar y)).
        unfold swap.
        repeat destruct decide; try congruence.
        change (expr_result_at_store e (LVFree y) (lso_store s1)).
        rewrite Hs. exact Hres.
Qed.

Lemma ty_denote_gas_over_self_result_qual
    gas b Σ e (m : WfWorldT) :
  typed_result_qual b (expr_result_qual e (LVBound 0)) =
    expr_result_qual e (LVBound 0) ->
  m ⊨ ty_denote_gas 0 Σ (CTOver b (expr_result_qual e (LVBound 0))) e ->
  m ⊨ ty_denote_gas gas Σ (CTOver b (expr_result_qual e (LVBound 0))) e.
Proof.
  destruct gas as [|gas']; intros Htyped_eq Hzero; [exact Hzero|].
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - apply ty_denote_gas_guard_formula with (gas := 0). exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any (S gas')
      Σ (CTOver b (expr_result_qual e (LVBound 0))) e m Hzero)
      as Hscope_full.
    pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
    pose proof (ty_denote_gas_zero_lc_relevant_env
      Σ (CTOver b (expr_result_qual e (LVBound 0))) e m Hzero)
      as HlcD.
    pose proof (ty_denote_gas_zero_tm_lvars_dom
      Σ (CTOver b (expr_result_qual e (LVBound 0))) e m Hzero)
      as HeD.
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTOver b (expr_result_qual e (LVBound 0))) e m Hzero)
      as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [_ [Hbasic _]]].
    apply expr_basic_typing_formula_models_iff in Hbasic
      as [_ [_ Hbasic_ty]].
    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hbasic_ty) as Hlce.
    eapply res_models_forall_rev_intro; [exact Hscope_forall|].
    exists (lvars_fv (dom (relevant_env Σ
              (CTOver b (expr_result_qual e (LVBound 0))) e)) ∪ fv_tm e).
    intros y Hy my Hdom Hrestrict.
    assert (Hiny : y ∈ world_dom (my : WorldT)).
    {
      rewrite Hdom. set_solver.
    }
    pose proof (formula_scoped_forall_open_res_le m my y
      _ Hscope_forall (res_le_of_projection_eq _ _ Hrestrict) Hiny)
      as Hscope_open.
    assert (HyD : y ∉ lvars_fv (dom (relevant_env Σ
      (CTOver b (expr_result_qual e (LVBound 0))) e))) by set_solver.
    assert (HyDlv : LVFree y ∉ dom (relevant_env Σ
      (CTOver b (expr_result_qual e (LVBound 0))) e)).
    {
      intros Hyin. apply HyD. apply lvars_fv_elem. exact Hyin.
    }
	    assert (Hye : y ∉ fv_tm e) by set_solver.
	    rewrite Htyped_eq in Hscope_open |- *.
	    rewrite !formula_open_impl in Hscope_open |- *.
	    rewrite formula_open_over_self_body_normalize in Hscope_open |- *.
	    2:{ unfold expr_result_qual; cbn [qual_vars qual_lvars]. set_solver. }
	    2:{ unfold expr_result_qual; cbn [qual_vars qual_lvars]. set_solver. }
	    rewrite qual_open_expr_result_qual_bound0 in Hscope_open |- *
	      by (exact Hlce || set_solver).
	    eapply res_models_impl_intro.
	    { exact Hscope_open. }
    intros Hres.
    change (my ⊨ formula_open 0 y
      (expr_result_formula_at
        (lvars_shift_from 0 (dom (relevant_env Σ
          (CTOver b (expr_result_qual e (LVBound 0))) e)))
        (tm_shift 0 e) (LVBound 0))) in Hres.
	    rewrite (formula_open_result_first_expr_result_formula_at_shift0
	      y (dom (relevant_env Σ
	        (CTOver b (expr_result_qual e (LVBound 0))) e)) e
	      HlcD HyD Hlce Hye) in Hres.
	    eapply (expr_result_formula_at_self_over_body
	      (dom (relevant_env Σ
	        (CTOver b (expr_result_qual e (LVBound 0))) e)) e y my);
	      [exact HeD | exact HyDlv | exact Hres].
Qed.

Lemma ty_denote_gas_under_self_result_qual
    gas b Σ e (m : WfWorldT) :
  typed_result_qual b (expr_result_qual e (LVBound 0)) =
    expr_result_qual e (LVBound 0) ->
  m ⊨ ty_denote_gas 0 Σ (CTUnder b (expr_result_qual e (LVBound 0))) e ->
  m ⊨ ty_denote_gas gas Σ (CTUnder b (expr_result_qual e (LVBound 0))) e.
Proof.
  destruct gas as [|gas']; intros Htyped_eq Hzero; [exact Hzero|].
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - apply ty_denote_gas_guard_formula with (gas := 0). exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any (S gas')
      Σ (CTUnder b (expr_result_qual e (LVBound 0))) e m Hzero)
      as Hscope_full.
    pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
    pose proof (ty_denote_gas_zero_lc_relevant_env
      Σ (CTUnder b (expr_result_qual e (LVBound 0))) e m Hzero)
      as HlcD.
    pose proof (ty_denote_gas_zero_tm_lvars_dom
      Σ (CTUnder b (expr_result_qual e (LVBound 0))) e m Hzero)
      as HeD.
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTUnder b (expr_result_qual e (LVBound 0))) e m Hzero)
      as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [_ [Hbasic _]]].
    apply expr_basic_typing_formula_models_iff in Hbasic
      as [_ [_ Hbasic_ty]].
    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hbasic_ty) as Hlce.
    eapply res_models_forall_rev_intro; [exact Hscope_forall|].
    exists (lvars_fv (dom (relevant_env Σ
              (CTUnder b (expr_result_qual e (LVBound 0))) e)) ∪ fv_tm e).
    intros y Hy my Hdom Hrestrict.
    assert (Hiny : y ∈ world_dom (my : WorldT)).
    {
      rewrite Hdom. set_solver.
    }
    pose proof (formula_scoped_forall_open_res_le m my y
      _ Hscope_forall (res_le_of_projection_eq _ _ Hrestrict) Hiny)
      as Hscope_open.
    assert (HyD : y ∉ lvars_fv (dom (relevant_env Σ
      (CTUnder b (expr_result_qual e (LVBound 0))) e))) by set_solver.
    assert (HyDlv : LVFree y ∉ dom (relevant_env Σ
      (CTUnder b (expr_result_qual e (LVBound 0))) e)).
    {
      intros Hyin. apply HyD. apply lvars_fv_elem. exact Hyin.
	    }
	    assert (Hye : y ∉ fv_tm e) by set_solver.
	    rewrite Htyped_eq in Hscope_open |- *.
	    rewrite !formula_open_impl in Hscope_open |- *.
	    rewrite formula_open_under_self_body_normalize in Hscope_open |- *.
	    2:{ unfold expr_result_qual; cbn [qual_vars qual_lvars]. set_solver. }
	    2:{ unfold expr_result_qual; cbn [qual_vars qual_lvars]. set_solver. }
	    rewrite qual_open_expr_result_qual_bound0 in Hscope_open |- *
	      by (exact Hlce || set_solver).
	    eapply res_models_impl_intro.
	    { exact Hscope_open. }
    intros Hres.
    change (my ⊨ formula_open 0 y
      (expr_result_formula_at
        (lvars_shift_from 0 (dom (relevant_env Σ
          (CTUnder b (expr_result_qual e (LVBound 0))) e)))
        (tm_shift 0 e) (LVBound 0))) in Hres.
	    rewrite (formula_open_result_first_expr_result_formula_at_shift0
	      y (dom (relevant_env Σ
	        (CTUnder b (expr_result_qual e (LVBound 0))) e)) e
	      HlcD HyD Hlce Hye) in Hres.
	    eapply (expr_result_formula_at_self_under_body
	      (dom (relevant_env Σ
	        (CTUnder b (expr_result_qual e (LVBound 0))) e)) e y my);
	      [exact HeD | exact HyDlv | exact Hres].
Qed.

Lemma primop_graph_qual_open_arg op x :
  qual_open_atom 1 x (primop_graph_qual op) =
  expr_result_qual (tprim op (vfvar x)) (LVBound 0).
Proof.
  unfold primop_graph_qual, expr_result_qual.
  apply qual_ext.
  - cbn [qual_lvars qual_open_atom].
    cbn [tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at].
    pose proof (tm_lvars_open_result_domain
      1 x (tprim op (vbvar 1)) (LVBound 0)) as Hdom.
    cbn [fv_tm fv_value] in Hdom.
    specialize (Hdom ltac:(set_solver)).
    cbn [open_tm open_value tm_lvars tm_lvars_at value_lvars_at
      bvar_lvars_at] in Hdom.
    unfold swap in Hdom.
    repeat match type of Hdom with
    | context[decide ?P] => destruct (decide P); try congruence
    end.
    exact Hdom.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars qual_open_atom].
    split; intros Hres.
    + apply expr_result_at_store_open_back_iff in Hres.
      * change (expr_result_at_store (tprim op (vfvar x)) (LVBound 0)
          (lso_store s2)).
        cbn [open_tm open_value] in Hres.
        unfold swap in Hres.
        repeat match type of Hres with
        | context[decide ?P] => destruct (decide P); try congruence
        end.
        rewrite <- Hs. exact Hres.
      * cbn [fv_tm fv_value]. set_solver.
      * change (lvars_open 1 x (tm_lvars (tprim op (vbvar 1))) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
    + apply expr_result_at_store_open_back_iff.
      * cbn [fv_tm fv_value]. set_solver.
      * change (lvars_open 1 x (tm_lvars (tprim op (vbvar 1))) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
      * cbn [open_tm open_value].
        unfold swap.
        repeat match goal with
        | |- context[decide ?P] => destruct (decide P); try congruence
        end.
        change (expr_result_at_store (tprim op (vfvar x)) (LVBound 0)
          (lso_store s1)).
        rewrite Hs. exact Hres.
Qed.

Lemma ty_denote_gas_precise_self_result_qual
    gas b Σ e (m : WfWorldT) :
  typed_result_qual b (expr_result_qual e (LVBound 0)) =
    expr_result_qual e (LVBound 0) ->
  m ⊨ ty_denote_gas 0 Σ (precise_ty b (expr_result_qual e (LVBound 0))) e ->
  m ⊨ ty_denote_gas gas Σ (precise_ty b (expr_result_qual e (LVBound 0))) e.
Proof.
  destruct gas as [|gas']; intros Htyped_eq Hzero; [exact Hzero|].
  unfold precise_ty, over_ty, under_ty in *.
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - apply ty_denote_gas_guard_formula with (gas := 0). exact Hzero.
  - rewrite res_models_and_iff.
	    split.
	    + apply ty_denote_gas_over_self_result_qual.
	      exact Htyped_eq.
	      eapply ty_denote_gas_zero_inter_l. exact Hzero.
	    + apply ty_denote_gas_under_self_result_qual.
	      exact Htyped_eq.
	      eapply ty_denote_gas_zero_inter_r. exact Hzero.
Qed.

Local Lemma topq_over_open_body b y (m : WfWorldT) :
  (forall ρ, (m : WorldT) ρ ->
    exists v, ρ !! y = Some v /\
      basic_value_has_ltype ∅ v (TBase b)) ->
  y ∈ world_dom (m : WorldT) ->
  m ⊨ over_open_body b topq y.
Proof.
  intros Hytyped Hym.
  unfold over_open_body.
  replace (qual_vars (qual_open_atom 0 y topq) ∖ {[LVFree y]})
    with (∅ : lvset).
  2:{
    rewrite qual_open_atom_vars.
    unfold topq, qual_top, qual_top_on.
    cbn [qual_vars qual_lvars].
    rewrite set_swap_singleton. base_swap_normalize. set_solver.
  }
  apply res_models_fibvars_empty_intro.
  apply res_models_over_FAtom_intro_store_holds.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_over, formula_fv_atom.
    intros a Ha.
    pose proof (qual_open_atom_dom_subset 0 y (typed_result_qual b topq))
      as Hsub.
    apply Hsub in Ha.
    unfold typed_result_qual, topq, qual_top, qual_top_on, qual_dom in Ha.
    cbn [qual_vars qual_lvars] in Ha.
    rewrite lvars_fv_union, lvars_fv_singleton_bound in Ha.
    set_solver.
  - intros ρ Hρ.
    destruct (Hytyped ρ Hρ) as [vy [Hyv Hvy]].
    unfold qualifier_holds_store.
    assert (Hlc_typed_top :
      lc_lvars (qual_vars (qual_open_atom 0 y (typed_result_qual b topq)))).
    {
      rewrite qual_open_atom_vars.
      unfold typed_result_qual, topq, qual_top, qual_top_on.
      cbn [qual_vars qual_lvars].
      rewrite set_swap_union, !set_swap_singleton.
      base_swap_normalize.
      intros v Hv. destruct v as [k|a]; [exfalso; set_solver|exact I].
    }
    assert (Hsub_typed_top :
      lvars_fv (qual_vars (qual_open_atom 0 y (typed_result_qual b topq))) ⊆
        dom (ρ : StoreT)).
    {
      rewrite qual_open_atom_vars.
      unfold typed_result_qual, topq, qual_top, qual_top_on.
      cbn [qual_vars qual_lvars].
      rewrite set_swap_union, !set_swap_singleton.
      base_swap_normalize.
		      rewrite lvars_fv_union, !lvars_fv_singleton_free.
		      intros a Ha.
		      assert (a = y) by set_solver. subst a.
          change (y ∈ dom (ρ : gmap atom value)).
          by apply elem_of_dom_2 in Hyv.
		    }
    exists Hlc_typed_top, Hsub_typed_top.
    cbn [qual_open_atom qual_prop typed_result_qual qual_vars qual_lvars].
    split; [exact I|].
    exists vy. split; [|exact Hvy].
    unfold lstore_on_open_back, lstore_on_lift_store.
    cbn [lso_store storeAO_store].
    rewrite lstore_swap_lookup_inv_value.
    base_swap_normalize.
    apply storeA_restrict_lookup_some_2.
    + rewrite lstore_lift_free_lookup_free. exact Hyv.
    + unfold topq, qual_top, qual_top_on.
      cbn [qual_vars qual_lvars].
      rewrite set_swap_singleton. base_swap_normalize.
      set_solver.
Qed.

Local Lemma topq_over_typed_body y b (m : WfWorldT) :
	  y ∈ world_dom (m : WorldT) ->
  (forall ρ, (m : WorldT) ρ ->
    exists v, ρ !! y = Some v /\
      basic_value_has_ltype ∅ v (TBase b)) ->
  m ⊨ FFibVars
    (qual_vars (qual_open_atom 0 y topq) ∖ {[LVFree y]})
    (formula_open 0 y (over_result_body b topq)).
Proof.
  intros Hy Hytyped.
  apply over_open_body_to_typed; [exact Hy|].
  apply topq_over_open_body; [exact Hytyped|exact Hy].
Qed.

Lemma ty_denote_gas_over_top_from_zero
    gas b Σ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTOver b topq) e ->
  m ⊨ ty_denote_gas gas Σ (CTOver b topq) e.
Proof.
  destruct gas as [|gas']; intros Hzero; [exact Hzero|].
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - apply ty_denote_gas_guard_formula with (gas := 0). exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any (S gas')
      Σ (CTOver b topq) e m Hzero) as Hscope_full.
    pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
    pose proof (ty_denote_gas_zero_lc_relevant_env
      Σ (CTOver b topq) e m Hzero) as HlcD.
	    pose proof (ty_denote_gas_guard_of_zero
	      Σ (CTOver b topq) e m Hzero) as Hguard.
	    repeat rewrite res_models_and_iff in Hguard.
	    destruct Hguard as [_ [Hworld [Hbasic _]]].
	    apply expr_basic_typing_formula_models_iff in Hbasic
	      as [_ [_ Hbasic_ty]].
	    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hbasic_ty) as Hlce.
    eapply res_models_forall_rev_intro; [exact Hscope_forall|].
    exists (lvars_fv (dom (relevant_env Σ (CTOver b topq) e)) ∪ fv_tm e).
    intros y Hy my Hdom Hrestrict.
    assert (Hiny : y ∈ world_dom (my : WorldT)) by (rewrite Hdom; set_solver).
    pose proof (formula_scoped_forall_open_res_le m my y
      _ Hscope_forall (res_le_of_projection_eq _ _ Hrestrict) Hiny)
      as Hscope_open.
    assert (HyD : y ∉ lvars_fv (dom (relevant_env Σ (CTOver b topq) e)))
      by set_solver.
    assert (Hye : y ∉ fv_tm e) by set_solver.
    eapply res_models_impl_intro; [exact Hscope_open|].
    intros Hres.
    change (my ⊨ formula_open 0 y
      (expr_result_formula_at
        (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b topq) e)))
        (tm_shift 0 e) (LVBound 0))) in Hres.
	    rewrite (formula_open_result_first_expr_result_formula_at_shift0
	      y (dom (relevant_env Σ (CTOver b topq) e)) e
	      HlcD HyD Hlce Hye) in Hres.
	    replace (set_swap (LVBound 0) (LVFree y)
	        (qual_vars topq ∖ {[LVBound 0]}))
	      with (qual_vars (qual_open_atom 0 y topq) ∖ {[LVFree y]}).
    2:{
	      rewrite lvars_open_difference_bound.
	      rewrite <- qual_open_atom_vars.
	      reflexivity.
	    }
	    assert (Hytyped :
	        forall ρ, (my : WorldT) ρ ->
	          exists v, ρ !! y = Some v /\
	            basic_value_has_ltype ∅ v (TBase b)).
	    {
	      intros ρ Hρ.
	      assert (HeD : tm_lvars e ⊆
	          dom (relevant_env Σ (CTOver b topq) e)).
	      {
	        transitivity (lvars_of_atoms (fv_tm e)).
	        - apply tm_lvars_lc_subset_atoms_fv.
	          apply tm_lvars_lc. exact Hlce.
	        - exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_ty).
	      }
	      assert (HyDlv : LVFree y ∉
	          dom (relevant_env Σ (CTOver b topq) e)).
	      {
	        intros Hyin. apply HyD.
	        apply lvars_fv_elem. exact Hyin.
	      }
	      pose proof (expr_result_formula_at_models_elim
	        (dom (relevant_env Σ (CTOver b topq) e)) e y my
	        HeD HyDlv Hres ρ Hρ)
	        as Hstore.
	      destruct Hstore as [_ [v [Hylook Heval]]].
	      change (((lstore_lift_free ρ : LStoreT) : gmap logic_var value)
	        !! LVFree y = Some v) in Hylook.
	      rewrite lstore_lift_free_lookup_free in Hylook.
	      exists v. split; [exact Hylook|].
	      apply basic_value_has_ltype_of_empty_atom_typing.
	      pose proof (res_models_kripke m my
	        (basic_world_formula (relevant_env Σ (CTOver b topq) e))
	        (res_le_of_projection_eq _ _ Hrestrict) Hworld) as Hworld_my.
	      apply basic_world_formula_models_iff in Hworld_my
	        as [HlcRel [HdomRel HtypedRel]].
	      unfold lworld_has_type, worldA_has_type in HtypedRel.
	      destruct HtypedRel as [_ Hstores_typed].
	      pose proof (Hstores_typed (lstore_lift_free ρ)
	        ltac:(exists ρ; split; [exact Hρ|reflexivity]))
	        as Hρ_ltyped.
		      eapply basic_tm_eval_value_type
		        with (Σ := relevant_env Σ (CTOver b topq) e)
		             (σ := store_restrict ρ
		                (lvars_fv (dom (relevant_env Σ (CTOver b topq) e))))
		             (e := e)
		             (T := TBase b).
	      - exact HlcRel.
	      - intros x vx Hxv.
	        apply storeA_restrict_lookup_some in Hxv as [HxRel Hρx].
	        apply lvars_fv_elem in HxRel.
	        apply elem_of_dom in HxRel as [Tx HΣx].
	        exists Tx. split; [exact HΣx|].
	        eapply Hρ_ltyped; [exact HΣx|].
	        change (((lstore_lift_free ρ : LStoreT) : gmap logic_var value)
	          !! LVFree x = Some vx).
	        rewrite lstore_lift_free_lookup_free. exact Hρx.
	      - exact Hbasic_ty.
	      - unfold tm_eval_in_store.
	        eapply (proj1 (expr_eval_in_store_restrict_lvars e
	          (lstore_lift_free
	            (store_restrict ρ
	              (lvars_fv (dom (relevant_env Σ (CTOver b topq) e)))) : LStoreT)
	          (dom (relevant_env Σ (CTOver b topq) e)) v HeD)).
	        rewrite (ContextBasicDenotation.TermEval.lstore_lift_free_restrict_fv_lvars_eq
	          ρ (dom (relevant_env Σ (CTOver b topq) e)) HlcRel).
	        eapply (proj2 (expr_eval_in_store_restrict_lvars e
	          (lstore_lift_free ρ : LStoreT)
	          (dom (relevant_env Σ (CTOver b topq) e)) v HeD)).
	        exact Heval.
	      - intros x Hx.
	        change (x ∈ dom
	          (store_restrict ρ
		            (lvars_fv (dom (relevant_env Σ (CTOver b topq) e))) :
		            gmap atom value)).
		        rewrite storeA_restrict_dom.
		        apply elem_of_intersection. split.
		        + rewrite (wfworld_store_dom my ρ Hρ).
			          apply HdomRel.
			          apply lvars_fv_elem.
			          apply (basic_tm_has_ltype_lvars _ _ _ Hbasic_ty).
		          unfold lvars_of_atoms. apply elem_of_map.
		          exists x. split; [reflexivity|exact Hx].
		        + apply lvars_fv_elem.
		          apply (basic_tm_has_ltype_lvars _ _ _ Hbasic_ty).
		          unfold lvars_of_atoms. apply elem_of_map.
		          exists x. split; [reflexivity|exact Hx].
	    }
	    exact (topq_over_typed_body y b my Hiny Hytyped).
Qed.

Lemma over_top_denotation_gas gas b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTOver b topq) e)
    (CTOver b topq) e ->
  m ⊨ ty_denote_gas gas Σ (CTOver b topq) e.
Proof.
  intros Hguard.
  apply ty_denote_gas_over_top_from_zero.
  apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
Qed.

Lemma primop_opened_result_guard_formula
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
      ({0 ~> x} (primop_result_ty (concrete_Φ op)))
      (tprim op (vfvar x)))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)).
Proof.
  intros Hctx.
  rewrite primop_result_ty_open_eq.
  set (τres :=
    match op with
    | op_eq0 =>
        precise_ty TBool (qual_open_atom 1 x (primop_graph_qual op_eq0))
    | op_plus1 =>
        precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_plus1))
    | op_minus1 =>
        precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_minus1))
    | op_boolGen =>
        precise_ty TBool (qual_open_atom 1 x (primop_graph_qual op_boolGen))
    | op_natGen =>
        precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_natGen))
    end).
  set (Σres := relevant_env
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
    τres
    (tprim op (vfvar x))).
  assert (Hworld_ctx :
    m ⊨ basic_world_formula
      (atom_env_to_lty_env
        (ctx_erasure_under ∅ (CtxBind x (primop_arg_ty (concrete_Φ op)))))).
  {
    eapply ctx_denote_under_basic_world. exact Hctx.
  }
  assert (Hworld : m ⊨ basic_world_formula Σres).
  {
    subst Σres.
    eapply basic_world_formula_subenv; [|exact Hworld_ctx].
    intros v T Hlook.
    unfold relevant_env, lty_env_restrict_lvars in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    destruct v as [k|a].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
      discriminate.
    - rewrite ctx_erasure_under_bind.
      rewrite !atom_store_to_lvar_store_lookup_free in Hlook |- *.
      cbn [erase_ctx] in Hlook.
      apply map_lookup_union_Some_raw.
      right. split.
      * apply storeA_restrict_lookup_none_l. apply lookup_empty.
      * exact Hlook.
  }
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    subst τres Σres.
    eapply basic_context_ty_lvars_relevant_env.
    eapply (basic_context_ty_lvars_mono (lvars_of_atoms {[x]})).
    + intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply elem_of_singleton in Ha as ->.
      apply elem_of_dom. exists (TBase (prim_arg_base (concrete_Φ op))).
      apply primop_arg_erase_env_lookup.
    + apply basic_context_ty_to_lvars.
      unfold basic_context_ty.
      rewrite <- primop_result_ty_open_eq.
      replace ({[x]} : aset) with ((∅ : aset) ∪ {[x]}) by set_solver.
      apply (wf_context_ty_at_open_at 0 ∅
        (primop_result_ty (concrete_Φ op)) x);
        [set_solver|apply primop_result_wf].
  - split; [exact Hworld|]. split.
    + apply expr_basic_typing_formula_models_iff.
      apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
      split; [exact Hlc|]. split; [exact Hscope|].
      replace (erase_ty τres)
        with (TBase (prim_ret_base (concrete_Φ op)))
        by (subst τres; destruct op; reflexivity).
      econstructor.
      * apply primop_erasure.
      * constructor.
        subst Σres.
        unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        -- apply primop_arg_erase_env_lookup.
        -- subst τres. unfold relevant_lvars.
           cbn [tm_lvars tm_lvars_at value_lvars_at].
           destruct op;
             unfold precise_ty, over_ty, under_ty, topq, qual_top_on,
               primop_graph_qual, expr_result_qual;
             cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars
               tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at].
           all: apply elem_of_union_r.
           all: apply elem_of_singleton; reflexivity.
    + apply expr_total_formula_tprim_from_primop_arg. exact Hctx.
Qed.

Lemma primop_graph_result_denotation
    op x :
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ⊫
    ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
      ({0 ~> x} (primop_result_ty (concrete_Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros m Hctx.
  unfold ty_denote.
  rewrite primop_result_ty_open_eq.
  pose proof (primop_opened_result_guard_formula op x m Hctx) as Hguard.
  rewrite primop_result_ty_open_eq in Hguard.
  destruct op; cbn [cty_depth].
	  - rewrite primop_graph_qual_open_arg in Hguard |- *.
	    apply ty_denote_gas_precise_self_result_qual.
	    apply typed_result_qual_prim_fvar_eq.
	    apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
	  - rewrite primop_graph_qual_open_arg in Hguard |- *.
	    apply ty_denote_gas_precise_self_result_qual.
	    apply typed_result_qual_prim_fvar_eq.
	    apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
	  - rewrite primop_graph_qual_open_arg in Hguard |- *.
	    apply ty_denote_gas_precise_self_result_qual.
	    apply typed_result_qual_prim_fvar_eq.
	    apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
	  - rewrite primop_graph_qual_open_arg in Hguard |- *.
	    apply ty_denote_gas_precise_self_result_qual.
	    apply typed_result_qual_prim_fvar_eq.
	    apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
	  - rewrite primop_graph_qual_open_arg in Hguard |- *.
	    apply ty_denote_gas_precise_self_result_qual.
	    apply typed_result_qual_prim_fvar_eq.
	    apply ty_denote_gas_zero_of_guard_formula. exact Hguard.
Qed.

Lemma primop_result_denotation_arg_world
    op x (m : WfWorldT) :
  m ⊨ ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ->
  m ⊨ basic_world_formula (<[LVFree x := TBase (prim_arg_base (concrete_Φ op))]> ∅).
Proof.
  intros Hden.
  unfold ty_denote in Hden.
  rewrite primop_result_ty_open_eq in Hden.
  pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld _]].
  eapply basic_world_formula_subenv; [|exact Hworld].
  intros v T Hlook.
  destruct v as [k|a].
  - rewrite lookup_insert_ne in Hlook by discriminate.
    rewrite lookup_empty in Hlook. discriminate.
  - destruct (decide (a = x)) as [->|Hax].
    + rewrite lookup_insert_eq in Hlook. inversion Hlook. subst T.
      unfold relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2.
      * apply primop_arg_erase_env_lookup.
      * unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars_at].
        unfold precise_ty, over_ty, under_ty, topq, qual_top.
        cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
        apply elem_of_union_r.
        apply elem_of_singleton. reflexivity.
    + rewrite lookup_insert_ne in Hlook by congruence.
      rewrite lookup_empty in Hlook. discriminate.
Qed.

Lemma primop_graph_result_to_arg_ctx
    op x :
  ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ⊫
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))).
Proof.
  intros m Hden.
  pose proof (primop_result_denotation_arg_world op x m Hden) as Hworld_arg.
  eapply ctx_denote_bind_from_arg_denotation.
  - apply primop_arg_basic.
  - rewrite primop_arg_ty_eq. cbn [erase_ty].
    apply map_lookup_insert.
  - rewrite primop_arg_ty_eq.
    pose proof (primop_arg_guard_formula op x m Hworld_arg) as Hguard_arg.
    rewrite primop_arg_ty_eq in Hguard_arg.
    exact (over_top_denotation_gas
      (cty_depth (CTOver (prim_arg_base (concrete_Φ op)) topq))
      (prim_arg_base (concrete_Φ op))
      (atom_env_to_lty_env
        (<[x := erase_ty (primop_arg_ty (concrete_Φ op))]>
          (∅ : gmap atom ty)))
      (tret (vfvar x)) m Hguard_arg).
Qed.

Theorem concrete_Φ_wf : wf_primop_ctx concrete_Φ.
Proof.
  intros op.
  refine {| wf_primop_erasure := primop_erasure op;
            wf_primop_arg_basic := primop_arg_basic op;
            wf_primop_result_basic := primop_result_wf op;
            wf_primop_semantic := _ |}.
  unfold primop_semantic_ok.
  intros x. split.
  - apply primop_graph_result_denotation.
  - apply primop_graph_result_to_arg_ctx.
Qed.
