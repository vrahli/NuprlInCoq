Require Export bar.


Definition swap_cs_choice_seq_vals {o} (r : cs_swap) (vals : @ChoiceSeqVals o) : ChoiceSeqVals :=
  map (swap_cs_cterm r) vals.

Definition swap_cs_default {o} (r : cs_swap) (d : nat -> @ChoiceSeqVal o) : nat -> ChoiceSeqVal :=
  fun n => swap_cs_cterm r (d n).

Definition swap_cs_restriction_pred {o} (r : cs_swap) (M : @RestrictionPred o) : RestrictionPred :=
  fun n t => M n (swap_cs_cterm r t).

Lemma swap_cs_restriction_pred_default {o}
      (r  : cs_swap)
      (d  : nat -> @ChoiceSeqVal o)
      (M  : @RestrictionPred o)
      (Md : forall n, M n (d n)) : forall n, swap_cs_restriction_pred r M n (swap_cs_default r d n).
Proof.
  introv.
  unfold swap_cs_default, swap_cs_restriction_pred; simpl.
  rewrite swap_cs_cterm_idem; auto.
Defined.

Definition cs_name2restr {o} (name : choice_sequence_name) : option (@ChoiceSeqRestriction o) :=
  match csn_kind name with
  | cs_kind_nat n =>
    if deq_nat n 0
    then Some csc_nat
    else if deq_nat n 1
         then Some csc_bool
         else None
  | cs_kind_seq l => Some (natSeq2restriction l)
  end.

Definition swap_cs_choice_seq_restr {o}
           (r     : cs_swap)
           (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match restr with
  | csc_type M => csc_type (swap_cs_restriction_pred r M)
(*  | csc_coq_law f => csc_coq_law (fun n => swap_cs_cterm r (f n))
  | csc_res P => csc_res (swap_cs_restriction_pred r P)*)
  end.

(* We make sure that we generate compatible restrictions in case one name
   in the swapping has a [cs_kind_nat 0] space, while the other one has a
   [cs_kind_seq l] space, for example. *)
Definition swap_cs_choice_seq_restr_comp {o}
           (r     : cs_swap)
           (name  : choice_sequence_name)
           (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match cs_name2restr name with
  | Some restr => restr
  | None => swap_cs_choice_seq_restr r restr
  end.

Definition swap_cs_choice_seq_entry {o}
           (r : cs_swap)
           (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkChoiceSeqEntry
      _
      (swap_cs_choice_seq_vals r vals)
      (swap_cs_choice_seq_restr r restr)
  end.

Fixpoint swap_cs_soterm {o} (r : cs_swap) (t : @SOTerm o) : SOTerm :=
  match t with
  | sovar v ts => sovar v (map (swap_cs_soterm r) ts)
  | soterm op bs => soterm (swap_cs_op r op) (map (swap_cs_sobterm r) bs)
  end
with swap_cs_sobterm {o} (r : cs_swap) (bt : @SOBTerm o) : SOBTerm :=
       match bt with
       | sobterm vs t => sobterm vs (swap_cs_soterm r t)
       end.

Lemma implies_wf_soterm_swap_cs_soterm {o} :
  forall (r : cs_swap) (t : @SOTerm o),
    wf_soterm t
    -> wf_soterm (swap_cs_soterm r t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "sovar".
    allrw @wf_sovar.
    introv i.
    apply in_map_iff in i; exrepnd; subst.
    applydup wf in i1.
    apply ind in i1; auto.

  - Case "soterm".
    allrw @wf_soterm_iff.
    allrw map_map; unfold compose.
    autorewrite with slow.
    repnd; dands; auto.

    + rewrite <- wf0.
      apply eq_maps; introv i.
      destruct x; unfold num_bvars; simpl; auto.

    + introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *; ginv.
      eapply ind; eauto.
Qed.
Hint Resolve implies_wf_soterm_swap_cs_soterm : slow.

Lemma so_free_vars_swap_cs_soterm {o} :
  forall (r : cs_swap) (t : @SOTerm o),
    so_free_vars (swap_cs_soterm r t) = so_free_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    autorewrite with list; f_equal.
    rewrite flat_map_map.
    apply eq_flat_maps; introv i.
    apply ind in i.
    unfold compose; auto.

  - Case "soterm".
    rewrite flat_map_map.
    apply eq_flat_maps; introv i.
    unfold compose; auto.
    destruct x; simpl.
    apply ind in i; rewrite i; auto.
Defined.
Hint Rewrite @so_free_vars_swap_cs_soterm : slow.

Lemma implies_socovered_swap_cs_soterm {o} :
  forall r (t : @SOTerm o) vars,
    socovered t vars
    -> socovered (swap_cs_soterm r t) vars.
Proof.
  introv cov.
  unfold socovered in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_socovered_swap_cs_soterm : slow.

Lemma get_utokens_so_swap_cs_soterm {o} :
  forall (r : cs_swap) (t : @SOTerm o),
    get_utokens_so (swap_cs_soterm r t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    rewrite flat_map_map; unfold compose; simpl.
    apply eq_flat_maps; introv i; tcsp.

  - Case "soterm".
    rewrite flat_map_map.
    autorewrite with slow.
    f_equal.
    apply eq_flat_maps; introv i.
    unfold compose; auto.
    destruct x; simpl.
    apply ind in i; rewrite i; auto.
Defined.
Hint Rewrite @get_utokens_so_swap_cs_soterm : slow.

Lemma implies_no_utokens_swap_cs_soterm {o} :
  forall r (t : @SOTerm o),
    no_utokens t
    -> no_utokens (swap_cs_soterm r t).
Proof.
  introv nou.
  unfold no_utokens in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_no_utokens_swap_cs_soterm : slow.

Lemma swap_cs_correct_abs {o}
      (r    : cs_swap)
      (abs  : opabs)
      (vars : list sovar_sig)
      (rhs  : @SOTerm o)
      (cor  : correct_abs abs vars rhs) : correct_abs abs vars (swap_cs_soterm r rhs).
Proof.
  unfold correct_abs in *; repnd.
  dands; eauto 3 with slow.
Qed.

Definition swap_cs_lib_entry {o} (r : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name e =>
    lib_cs (swap_cs r name) (swap_cs_choice_seq_entry r e)
  | lib_abs abs vars rhs correct =>
    lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Fixpoint swap_cs_plib {o} (r : cs_swap) (lib : @plibrary o) :=
  match lib with
  | [] => []
  | entry :: entries => swap_cs_lib_entry r entry :: swap_cs_plib r entries
  end.

Ltac dterm name :=
  match goal with
  (* ** on conclusion ** *)
  | [ |- context[ match ?c with | [] => _ | _ :: _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ |- context[ match ?c with | vterm _ => _ | oterm _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ |- context[ match ?c with | Can _ => _ | NCan _ => _ | Exc => _ | Abs _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    remember c as name0; destruct name0 as [name1|name1|name1|name1]
  | [ |- context[ match ?c with | bterm _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ |- context[ match (match ?c with | csuccess _ => _ | cfailure _ _ => _ end) with _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ |- context[ match ?c with | csuccess _ => _ | cfailure _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ |- context[ match ?c with _ => _ end ] ] =>
    match type of c with
    | CanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    | NonCanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    end

  (* ** on hypotheses ** *)
  | [ H : context[ match ?c with | [] => _ | _ :: _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ H : context[ match ?c with | vterm _ => _ | oterm _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ H : context[ match ?c with | Can _ => _ | NCan _ => _ | Exc => _ | Abs _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    remember c as name0; destruct name0 as [name1|name1|name1|name1]
  | [ H : context[ match ?c with | bterm _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ H : context[ match (match ?c with | csuccess _ => _ | cfailure _ _ => _ end) with _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ H : context[ match ?c with | csuccess _ => _ | cfailure _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ H : context[ match ?c with _ => _ end ] |- _ ] =>
    match type of c with
    | CanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    | NonCanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    end
  end.

Ltac dterms name :=
  repeat (dterm name; subst; simpl in *; ginv; eauto 2 with slow).

Definition cs_size {o} (lib : @library o) (name : choice_sequence_name) : nat :=
  match find_cs lib name with
  | Some e => length (cse_vals e)
  | None => 0
  end.

Lemma find_cs_value_at_implies_lt_cs_size {o} :
  forall (lib : @library o) name n v,
    find_cs_value_at lib name n = Some v
    -> n < cs_size lib name.
Proof.
  introv h.
  unfold find_cs_value_at in h.
  unfold cs_size.
  remember (find_cs lib name) as fcs.
  symmetry in Heqfcs.
  destruct fcs; ginv.
  rewrite find_value_of_cs_at_is_select in h; eauto 3 with slow.
Qed.
Hint Resolve find_cs_value_at_implies_lt_cs_size : slow.

Hint Resolve Nat.le_max_l : num.
Hint Resolve Nat.le_max_r : num.
Hint Resolve Nat.le_refl : num.
Hint Resolve le_trans : num.

Lemma cs_size_le_lib_depth {o} :
  forall name (lib : @library o),
    cs_size lib name <= lib_depth lib.
Proof.
  introv.
  unfold cs_size.
  destruct lib as [lib cond]; simpl.
  induction lib; simpl; auto.
  destruct a; simpl; boolvar; subst; eauto 3 with slow num.
Qed.
Hint Resolve cs_size_le_lib_depth : slow.

Lemma find_cs_value_at_implies_lt_lib_depth {o} :
  forall (lib : @library o) name n v,
    find_cs_value_at lib name n = Some v
    -> n < lib_depth lib.
Proof.
  introv h.
  apply find_cs_value_at_implies_lt_cs_size in h.
  pose proof (cs_size_le_lib_depth name lib) as q; omega.
Qed.
Hint Resolve find_cs_value_at_implies_lt_lib_depth : slow.

Lemma length_swap_cs_choice_seq_vals {o} :
  forall sw (vals : @ChoiceSeqVals o),
    length (swap_cs_choice_seq_vals sw vals) = length vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_swap_cs_choice_seq_vals : slow.

Lemma entry_depth_swap_cs_lib_entry {o} :
  forall sw (e : @library_entry o),
    entry_depth (swap_cs_lib_entry sw e) = entry_depth e.
Proof.
  introv; destruct e; simpl; auto.
  destruct entry as [vals restr]; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @entry_depth_swap_cs_lib_entry : slow.

Lemma lib_depth_swap_cs_plib {o} :
  forall sw (lib : @plibrary o),
    lib_depth (swap_cs_plib sw lib) = lib_depth lib.
Proof.
  induction lib; simpl; auto; allrw; autorewrite with slow; auto.
Qed.
Hint Rewrite @lib_depth_swap_cs_plib : slow.

Ltac apply_comp_success :=
  match goal with
  | [ H : context[compute_step_apply]     |- _ ] => apply compute_step_apply_success     in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_eapply]    |- _ ] => apply compute_step_eapply_success    in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_spread]    |- _ ] => apply compute_step_spread_success    in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_decide]    |- _ ] => apply compute_step_decide_success    in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_dsup]      |- _ ] => apply compute_step_dsup_success      in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_sleep]     |- _ ] => apply compute_step_sleep_success     in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_tuni]      |- _ ] => apply compute_step_tuni_success      in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_minus]     |- _ ] => apply compute_step_minus_success     in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_parallel]  |- _ ] => apply compute_step_parallel_success  in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_last_cs]   |- _ ] => apply compute_step_last_cs_success   in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_comp_seq1] |- _ ] => apply compute_step_comp_seq1_success in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_comp_seq2] |- _ ] => apply compute_step_comp_seq2_success in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_swap_cs1]  |- _ ] => apply compute_step_swap_cs1_success  in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_swap_cs2]  |- _ ] => apply compute_step_swap_cs2_success  in H; repndors; exrepnd; subst; GC; ginv
  | [ H : context[compute_step_ncan_nil]  |- _ ] => apply compute_step_ncan_nil_success  in H; repndors; exrepnd; subst; GC; ginv
  end.

Lemma swap_cs_can_twice {o} :
  forall sw (c : @CanonicalOp o),
    swap_cs_can sw (swap_cs_can sw c) = c.
Proof.
  introv; destruct c; simpl; auto; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_can_twice : slow.

Lemma swap_cs_inj :
  forall (sw : cs_swap) (name1 name2 : choice_sequence_name),
    swap_cs sw name1 = swap_cs sw name2
    -> name1 = name2.
Proof.
  introv h.
  destruct sw; simpl in *; boolvar; subst; auto; tcsp.
Qed.

Lemma swap_cs_can_twice2 {o} :
  forall sw nfo (c : @CanonicalOp o),
    swap_cs_can
      (swap_cs_nfo_name1 (swap_cs_nfo sw nfo),
       swap_cs_nfo_name2 (swap_cs_nfo sw nfo))
      (swap_cs_can sw c)
    = swap_cs_can
        sw
        (swap_cs_can (swap_cs_nfo_name1 nfo, swap_cs_nfo_name2 nfo) c).
Proof.
  introv.
  destruct c; simpl; auto.
  destruct nfo as [n1 n2]; simpl; boolvar; subst; auto;
    try apply swap_cs_inj in e; subst; auto; tcsp; try congruence.
Qed.

Lemma swap_cs_sub_sw_sub {o} :
  forall sw a b l,
    @swap_cs_sub o sw (sw_sub a b l) = sw_sub (swap_cs sw a) (swap_cs sw b) l.
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl; auto.
Qed.
Hint Rewrite @swap_cs_sub_sw_sub : slow.

Lemma swap_cs_term_push_swap_cs_sub_term {o} :
  forall sw a b l (t : @NTerm o),
    swap_cs_term sw (push_swap_cs_sub_term a b l t)
    = push_swap_cs_sub_term (swap_cs sw a) (swap_cs sw b) l (swap_cs_term sw t).
Proof.
  introv; unfold push_swap_cs_sub_term.
  rewrite <- lsubst_aux_swap_cs_term; autorewrite with slow; auto.
Qed.

Lemma on_success_csuccess {o} :
  forall (c : @Comput_Result o) f b,
    on_success c f = csuccess b
    -> {x : NTerm & c = csuccess x /\ b = f x}.
Proof.
  introv h; destruct c; simpl in *; ginv; eauto.
Qed.

Lemma implies_swap_cs_ncan_diff_try :
  forall sw ncan,
    ncan <> NTryCatch
    -> swap_cs_ncan sw ncan <> NTryCatch.
Proof.
  introv h q.
  destruct ncan; simpl in *; tcsp; ginv.
Qed.
Hint Resolve implies_swap_cs_ncan_diff_try : slow.

Lemma implies_isvalue_like_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    isvalue_like t
    -> isvalue_like (swap_cs_term sw t).
Proof.
  introv isv.
  unfold isvalue_like in *; repndors.
  { apply iscan_implies in isv; exrepnd; subst; simpl; tcsp. }
  { apply isexc_implies2 in isv; exrepnd; subst; simpl; tcsp. }
Qed.
Hint Resolve implies_isvalue_like_swap_cs_term : slow.

Lemma implies_isnoncan_like_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    isnoncan_like t
    -> isnoncan_like (swap_cs_term sw t).
Proof.
  introv isn.
  unfold isnoncan_like in *; repndors.
  { apply isnoncan_implies in isn; exrepnd; subst; simpl; tcsp. }
  { apply isabs_implies in isn; exrepnd; subst; simpl; tcsp. }
Qed.
Hint Resolve implies_isnoncan_like_swap_cs_term : slow.

Lemma maybe_new_var_swap_cs_term {o} :
  forall v l sw (t : @NTerm o),
    maybe_new_var v l (swap_cs_term sw t) = maybe_new_var v l t.
Proof.
  introv; unfold maybe_new_var; boolvar; auto.
  unfold newvar; autorewrite with slow; auto.
Qed.
Hint Rewrite @maybe_new_var_swap_cs_term : slow.

Lemma swap_cs_term_pushdown_fresh {o} :
  forall sw v (t : @NTerm o),
    swap_cs_term sw (pushdown_fresh v t) = pushdown_fresh v (swap_cs_term sw t).
Proof.
  introv; destruct t as [z|op bs]; simpl; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; repeat rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl; fold_terms; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_term_pushdown_fresh : slow.

Fixpoint swap_cs_utok_sub {o} r (sub : @utok_sub o) :=
  match sub with
  | [] => []
  | (a,t) :: sub => (a, swap_cs_term r t) :: swap_cs_utok_sub r sub
  end.

Lemma utok_sub_find_swap_cs_utok_sub {o} :
  forall sw (sub : @utok_sub o) a,
    utok_sub_find (swap_cs_utok_sub sw sub) a
    = match utok_sub_find sub a with
      | Some t => Some (swap_cs_term sw t)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; tcsp; repnd; simpl in *; boolvar; subst; tcsp.
Qed.

Lemma swap_cs_term_subst_utokens_aux {o} :
  forall sw (t : @NTerm o) sub,
    swap_cs_term sw (subst_utokens_aux t sub)
    = subst_utokens_aux (swap_cs_term sw t) (swap_cs_utok_sub sw sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  destruct op; simpl; tcsp;
    try (complete (f_equal; repeat rewrite map_map; unfold compose; apply eq_maps; introv i;
                   destruct x; simpl; f_equal; eapply ind; eauto)).
  destruct c; simpl;
    try (complete (f_equal; repeat rewrite map_map; unfold compose; apply eq_maps; introv i;
                   destruct x; simpl; f_equal; eapply ind; eauto)).
  unfold subst_utok.
  rewrite utok_sub_find_swap_cs_utok_sub.
  remember (utok_sub_find sub g) as find; symmetry in Heqfind; destruct find; simpl; auto;
    try (complete (f_equal; repeat rewrite map_map; unfold compose; apply eq_maps; introv i;
                   destruct x; simpl; f_equal; eapply ind; eauto)).
Qed.
Hint Rewrite @swap_cs_term_subst_utokens_aux : slow.

Lemma free_vars_utok_sub_swap_cs_utok_sub {o} :
  forall sw (sub : @utok_sub o),
    free_vars_utok_sub (swap_cs_utok_sub sw sub)
    = free_vars_utok_sub sub.
Proof.
  induction sub; introv; repnd; simpl; tcsp.
  autorewrite with slow; allrw; auto.
Qed.
Hint Rewrite @free_vars_utok_sub_swap_cs_utok_sub : slow.

Lemma swap_cs_term_subst_utokens {o} :
  forall sw (t : @NTerm o) sub,
    swap_cs_term sw (subst_utokens t sub)
    = subst_utokens (swap_cs_term sw t) (swap_cs_utok_sub sw sub).
Proof.
  introv; unfold subst_utokens; simpl; autorewrite with slow; boolvar; simpl; autorewrite with slow; auto.
  rewrite change_bvars_alpha_swap_cs_term; auto.
Qed.
Hint Rewrite @swap_cs_term_subst_utokens : slow.

Lemma swap_cs_term_subst {o} :
  forall  r (t : @NTerm o) v u,
    swap_cs_term r (subst t v u)
    = subst (swap_cs_term r t) v (swap_cs_term r u).
Proof.
  introv; rewrite subst_swap_cs_term; auto.
Qed.
Hint Rewrite @swap_cs_term_subst : slow.

Lemma swap_cs_term_lsubst {o} :
  forall r (t : @NTerm o) sub,
    swap_cs_term r (lsubst t sub)
    = lsubst (swap_cs_term r t) (swap_cs_sub r sub).
Proof.
  introv; rewrite lsubst_swap_cs_term; auto.
Qed.
Hint Rewrite @swap_cs_term_lsubst : slow.

Lemma find_cs_swap {o} :
  forall sw (lib : @plibrary o) name,
    find_cs (swap_cs_plib sw lib) (swap_cs sw name)
    = match find_cs lib name with
      | Some e => Some (swap_cs_choice_seq_entry sw e)
      | None => None
      end.
Proof.
  induction lib; introv; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.
  apply swap_cs_inj in e; tcsp.
Qed.

Lemma find_cs_value_at_swap {o} :
  forall sw (lib : @plibrary o) name n,
    find_cs_value_at (swap_cs_plib sw lib) (swap_cs sw name) n
    = match find_cs_value_at lib name n with
      | Some c => Some (swap_cs_cterm sw c)
      | None => None
      end.
Proof.
  introv; unfold find_cs_value_at.
  rewrite find_cs_swap.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; auto.
  repeat rewrite find_value_of_cs_at_is_select.
  destruct c as [vals restr]; simpl.
  unfold swap_cs_choice_seq_vals; rewrite select_map; tcsp.
Qed.

Lemma isexc_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    isexc t
    -> isexc (swap_cs_term sw t).
Proof.
  introv h; apply isexc_implies2 in h; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve isexc_swap_cs_term : slow.

Lemma implies_eapply_wf_can_swap {o} :
  forall sw c (bs : list (@BTerm o)),
    eapply_wf_def (oterm (Can c) bs)
    -> eapply_wf_def (oterm (Can (swap_cs_can sw c)) (map (swap_cs_bterm sw) bs)).
Proof.
  introv wf; unfold eapply_wf_def in *; repndors; exrepnd; subst.
  { inversion wf0; subst; simpl; left; exists (swap_cs sw name); tcsp. }
  { inversion wf1; subst; simpl; right; exists v (swap_cs_term sw b); tcsp. }
Qed.
Hint Resolve implies_eapply_wf_can_swap : slow.

Lemma last_cs_entry_swap {o} :
  forall sw (e : @ChoiceSeqEntry o),
    last_cs_entry (swap_cs_choice_seq_entry sw e)
    = match last_cs_entry e with
      | Some t => Some (swap_cs_cterm sw t)
      | None => None
      end.
Proof.
  destruct e as [vals restr]; simpl.
  induction vals; simpl in *; tcsp.
  destruct vals; simpl in *; tcsp.
Qed.

Lemma swap_cs_term_find_last_entry_default {o} :
  forall sw lib name (t : @NTerm o),
    swap_cs_term sw (find_last_entry_default lib name t)
    = find_last_entry_default (swap_cs_plib sw lib) (swap_cs sw name) (swap_cs_term sw t).
Proof.
  introv; unfold find_last_entry_default.
  rewrite find_cs_swap.
  remember (find_cs lib name) as fcs; destruct fcs; tcsp.
  rewrite last_cs_entry_swap.
  destruct (last_cs_entry c); tcsp.
  unfold CSVal2term.
  destruct c0; simpl; tcsp.
Qed.
Hint Rewrite @swap_cs_term_find_last_entry_default : slow.

Lemma co_wf_swap_cs_can {o} :
  forall sw c (x : @CanonicalOp o) bs,
    co_wf c (swap_cs_can sw x) bs = co_wf c x bs.
Proof.
  introv; unfold co_wf; simpl; autorewrite with slow.
  destruct x; simpl; tcsp.
Qed.
Hint Rewrite @co_wf_swap_cs_can : slow.

Lemma ca_wf_swap_cs_can {o} :
  forall sw (x : @CanonicalOp o) bs,
    ca_wf (swap_cs_can sw x) bs = ca_wf x bs.
Proof.
  introv; unfold ca_wf; simpl; autorewrite with slow.
  destruct x; simpl; tcsp.
Qed.
Hint Rewrite @ca_wf_swap_cs_can : slow.

Lemma get_param_from_cop_swap_cs_can {o} :
  forall sw (c : @CanonicalOp o),
    get_param_from_cop (swap_cs_can sw c)
    = match get_param_from_cop c with
      | Some (PKc x) => Some (PKc (swap_cs sw x))
      | x => x
      end.
Proof.
  destruct c; simpl; tcsp.
Qed.

Lemma canonical_form_test_for_swap_cs_can {o} :
  forall sw c (x : @CanonicalOp o),
    canonical_form_test_for c (swap_cs_can sw x)
    = canonical_form_test_for c x.
Proof.
  introv; destruct x; simpl; tcsp.
Qed.
Hint Rewrite @canonical_form_test_for_swap_cs_can : slow.

Definition swap_cs_sosub_kind {o} sw (k : @sosub_kind o) :=
  match k with
  | sosk vs t => sosk vs (swap_cs_term sw t)
  end.

Fixpoint swap_cs_sosub {o} sw (sub : @SOSub o) :=
  match sub with
  | [] => []
  | (v,k) :: sub => (v, swap_cs_sosub_kind sw k) :: swap_cs_sosub sw sub
  end.

Lemma sosub_kind_swap_cs_sosub {o} :
  forall sw (sub : @SOSub o) x,
    sosub_find (swap_cs_sosub sw sub) x
    = match sosub_find sub x with
      | Some k => Some (swap_cs_sosub_kind sw k)
      | None => None
      end.
Proof.
  induction sub; introv; repnd; simpl in *; tcsp.
  destruct a; simpl in *; tcsp.
  destruct x; simpl in *; tcsp; boolvar; subst; tcsp; simpl; tcsp.
Qed.

Lemma swap_cs_sub_combine {o} :
  forall sw l (ts : list (@NTerm o)),
    swap_cs_sub sw (combine l ts)
    = combine l (map (swap_cs_term sw) ts).
Proof.
  induction l; introv; simpl; tcsp.
  destruct ts; simpl; tcsp.
  rewrite IHl; auto.
Qed.
Hint Rewrite @swap_cs_sub_combine : slow.

Lemma swap_cs_sosub_sosub_filter {o} :
  forall sw (sub : @SOSub o) vs,
    swap_cs_sosub sw (sosub_filter sub vs)
    = sosub_filter (swap_cs_sosub sw sub) vs.
Proof.
  induction sub; introv; repnd; simpl; auto.
  destruct a; simpl; boolvar; simpl; tcsp.
  rewrite IHsub; auto.
Qed.
Hint Rewrite @swap_cs_sosub_sosub_filter : slow.

Lemma swap_apply_list {o} :
  forall sw l (t : @NTerm o),
    swap_cs_term sw (apply_list t l)
    = apply_list (swap_cs_term sw t) (map (swap_cs_term sw) l).
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl; simpl; tcsp.
Qed.

Lemma swap_cs_term_soterm2nterm {o} :
  forall sw (t : @SOTerm o),
    swap_cs_term sw (soterm2nterm t)
    = soterm2nterm (swap_cs_soterm sw t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; auto;[|].

  { rewrite swap_apply_list.
    repeat rewrite map_map.
    f_equal.
    apply eq_maps; introv i; unfold compose; simpl; tcsp. }

  { f_equal.
    repeat rewrite map_map.
    apply eq_maps; introv i; unfold compose; simpl; tcsp.
    destruct x; simpl; f_equal; eapply ind; eauto. }
Qed.

Lemma swap_cs_term_sosub_aux {o} :
  forall sw (t : @SOTerm o) sub,
    swap_cs_term sw (sosub_aux sub t)
    = sosub_aux (swap_cs_sosub sw sub) (swap_cs_soterm sw t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  { rewrite sosub_kind_swap_cs_sosub; autorewrite with slow.
    remember (sosub_find sub (v,length ts)) as find; destruct find; tcsp.
    { destruct s; simpl in *; tcsp.
      rewrite <- lsubst_aux_swap_cs_term; simpl; tcsp.
      autorewrite with slow; tcsp.
      repeat rewrite map_map; unfold compose; simpl; tcsp.
      f_equal; f_equal.
      apply eq_maps; introv i; tcsp. }
    rewrite swap_apply_list; simpl.
    f_equal; repeat rewrite map_map; unfold compose; simpl.
    apply eq_maps; introv i; tcsp. }

  { f_equal; repeat (rewrite map_map); unfold compose; simpl.
    apply eq_maps; introv i; destruct x; simpl; f_equal.
    erewrite ind; eauto; autorewrite with slow; auto. }
Qed.

Lemma fo_bound_vars_swap_cs_soterm {o} :
  forall sw (t : @SOTerm o),
    fo_bound_vars (swap_cs_soterm sw t)
    = fo_bound_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; simpl.

  { rewrite flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; tcsp. }

  { rewrite flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x; simpl; erewrite ind; eauto. }
Qed.
Hint Rewrite @fo_bound_vars_swap_cs_soterm : slow.

Lemma all_fo_vars_swap_cs_soterm {o} :
  forall sw (t : @SOTerm o),
    all_fo_vars (swap_cs_soterm sw t)
    = all_fo_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; simpl.

  { rewrite flat_map_map; unfold compose.
    f_equal; apply eq_flat_maps; introv i; tcsp. }

  { rewrite flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x; simpl; erewrite ind; eauto. }
Qed.
Hint Rewrite @all_fo_vars_swap_cs_soterm : slow.

Lemma free_vars_sosub_swap_cs_sosub {o} :
  forall sw (sub : @SOSub o),
    free_vars_sosub (swap_cs_sosub sw sub)
    = free_vars_sosub sub.
Proof.
  induction sub; introv; repnd; simpl in *; tcsp.
  rewrite IHsub.
  destruct a; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @free_vars_sosub_swap_cs_sosub : slow.

Lemma bound_vars_sosub_swap_cs_sosub {o} :
  forall sw (sub : @SOSub o),
    bound_vars_sosub (swap_cs_sosub sw sub)
    = bound_vars_sosub sub.
Proof.
  induction sub; introv; repnd; simpl in *; tcsp.
  rewrite IHsub.
  destruct a; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @bound_vars_sosub_swap_cs_sosub : slow.

Lemma allvars_range_sosub_swap_cs_sosub {o} :
  forall sw (sub : @SOSub o),
    allvars_range_sosub (swap_cs_sosub sw sub)
    = allvars_range_sosub sub.
Proof.
  induction sub; introv; repnd; simpl in *; tcsp.
  rewrite IHsub.
  destruct a; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @allvars_range_sosub_swap_cs_sosub : slow.

Lemma fo_change_bvars_alpha_swap_cs_soterm {o} :
  forall sw (t : @SOTerm o) vs ren,
    fo_change_bvars_alpha vs ren (swap_cs_soterm sw t)
    = swap_cs_soterm sw (fo_change_bvars_alpha vs ren t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl.

  { boolvar; subst; simpl in *; tcsp.
    { destruct ts; simpl in *; tcsp. }
    f_equal; repeat rewrite map_map; unfold compose.
    apply eq_maps; introv i; tcsp. }

  { repeat rewrite map_map; unfold compose.
    f_equal; apply eq_maps; introv i; destruct x; simpl; autorewrite with slow.
    erewrite ind; eauto. }
Qed.
Hint Rewrite @fo_change_bvars_alpha_swap_cs_soterm : slow.

Lemma all_fo_vars_fo_change_bvars_alpha_swap_cs_soterm {o} :
  forall sw (t : @SOTerm o) vs ren,
    all_fo_vars (fo_change_bvars_alpha vs ren (swap_cs_soterm sw t))
    = all_fo_vars (fo_change_bvars_alpha vs ren t).
Proof.
  introv; autorewrite with slow; auto.
Qed.
Hint Rewrite @all_fo_vars_fo_change_bvars_alpha_swap_cs_soterm : slow.

Lemma swap_cs_sub_var_ren {o} :
  forall sw l k,
    @swap_cs_sub o sw (var_ren l k)
    = var_ren l k.
Proof.
  introv; unfold var_ren.
  rewrite swap_cs_sub_combine; simpl.
  rewrite map_map; unfold compose; simpl; tcsp.
Qed.
Hint Rewrite @swap_cs_sub_var_ren : slow.

Lemma swap_cs_sosub_sosub_change_bvars_alpha {o} :
  forall sw (sub : @SOSub o) vs,
    swap_cs_sosub sw (sosub_change_bvars_alpha vs sub)
    = sosub_change_bvars_alpha vs (swap_cs_sosub sw sub).
Proof.
  induction sub; introv; repnd;simpl in *; tcsp; f_equal; tcsp.
  f_equal; tcsp.
  destruct a; simpl.
  unfold sk_change_bvars_alpha; simpl; autorewrite with slow.
  rewrite change_bvars_alpha_swap_cs_term; autorewrite with slow.
  rewrite <- lsubst_aux_swap_cs_term; simpl; autorewrite with slow; tcsp.
Qed.

Lemma swap_cs_term_sosub {o} :
  forall sw (t : @SOTerm o) sub,
    swap_cs_term sw (sosub sub t)
    = sosub (swap_cs_sosub sw sub) (swap_cs_soterm sw t).
Proof.
  introv; unfold sosub; autorewrite with slow.
  boolvar; rewrite swap_cs_term_sosub_aux; tcsp;
    rewrite swap_cs_sosub_sosub_change_bvars_alpha; tcsp.
Qed.

Lemma swap_cs_sosub_mk_abs_subst {o} :
  forall sw vars (bs : list (@BTerm o)),
    swap_cs_sosub sw (mk_abs_subst vars bs)
    = mk_abs_subst vars (map (swap_cs_bterm sw) bs).
Proof.
  induction vars; introv; simpl; tcsp.
  destruct a; simpl; tcsp.
  destruct bs; simpl; tcsp.
  destruct b; simpl; tcsp; boolvar; subst; simpl ;tcsp.
  rewrite IHvars; auto.
Qed.

Lemma swap_cs_term_mk_instance {o} :
  forall sw vars bs (rhs : @SOTerm o),
    swap_cs_term sw (mk_instance vars bs rhs)
    = mk_instance vars (map (swap_cs_bterm sw) bs) (swap_cs_soterm sw rhs).
Proof.
  introv; unfold mk_instance.
  rewrite swap_cs_term_sosub.
  rewrite swap_cs_sosub_mk_abs_subst; auto.
Qed.

Lemma matching_bterms_swap {o} :
  forall sw vars (bs : list (@BTerm o)),
    matching_bterms vars (map (swap_cs_bterm sw) bs)
    <-> matching_bterms vars bs.
Proof.
  introv; unfold matching_bterms; rewrite map_map; unfold compose; split; intro h; rewrite h; clear h;
    apply eq_maps; introv i; destruct x; simpl; tcsp.
Qed.
Hint Rewrite @matching_bterms_swap : slow.

Lemma matching_entry_swap {o} :
  forall sw abs opabs vars (bs : list (@BTerm o)),
    matching_entry abs opabs vars (map (swap_cs_bterm sw) bs)
    <-> matching_entry abs opabs vars bs.
Proof.
  introv; unfold matching_entry in *.
  split; intro h; repnd; dands; autorewrite with slow in *; tcsp.
Qed.
Hint Rewrite @matching_entry_swap : slow.

Lemma find_entry_swap {o} :
  forall sw (lib : @plibrary o) abs bs,
    find_entry (swap_cs_plib sw lib) abs (map (swap_cs_bterm sw) bs)
    = match find_entry lib abs bs with
      | Some e => Some (swap_cs_lib_entry sw e)
      | None => None
      end.
Proof.
  induction lib; introv; simpl; tcsp.
  destruct a; simpl; tcsp.
  boolvar; tcsp; autorewrite with slow in *.
  { apply not_matching_entry_iff in n; tcsp. }
  apply not_matching_entry_iff in n; destruct n; autorewrite with slow; auto.
Qed.

Lemma implies_found_entry_swap_cs_plib {o} :
  forall sw (lib : @plibrary o) abs bs oa vars rhs correct,
    found_entry lib abs bs oa vars rhs correct
    -> found_entry
         (swap_cs_plib sw lib)
         abs
         (map (swap_cs_bterm sw) bs)
         oa
         vars
         (swap_cs_soterm sw rhs)
         (swap_cs_correct_abs sw oa vars rhs correct).
Proof.
  introv f; unfold found_entry in *.
  rewrite find_entry_swap; allrw; simpl; tcsp.
Qed.

Lemma get_utokens_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    get_utokens (swap_cs_term sw t) = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto; autorewrite with slow.
  f_equal.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; eapply ind; eauto.
Qed.
Hint Rewrite @get_utokens_swap_cs_term : slow.

Lemma getc_utokens_swap_cs_cterm {o} :
  forall sw (t : @CTerm o),
    getc_utokens (swap_cs_cterm sw t) = getc_utokens t.
Proof.
  introv; destruct_cterms; simpl; unfold getc_utokens; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @getc_utokens_swap_cs_cterm : slow.

Lemma get_utokens_library_entry_swap_cs_lib_entry {o} :
  forall sw (e : @library_entry o),
    get_utokens_library_entry (swap_cs_lib_entry sw e)
    = get_utokens_library_entry e.
Proof.
  destruct e; simpl; auto; autorewrite with slow; auto.
  destruct entry as [vals restr]; simpl.
  unfold swap_cs_choice_seq_vals; rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_library_entry_swap_cs_lib_entry : slow.

Lemma get_utokens_library_swap_cs_plib {o} :
  forall sw (lib : @plibrary o),
    get_utokens_library (swap_cs_plib sw lib) = get_utokens_library lib.
Proof.
  induction lib; introv; simpl; tcsp; rewrite IHlib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_library_swap_cs_plib : slow.

Lemma get_fresh_atom_swap {o} :
  forall sw (lib : @plibrary o) t,
    get_fresh_atom (swap_cs_plib sw lib) (swap_cs_term sw t)
    = get_fresh_atom lib t.
Proof.
  introv; unfold get_fresh_atom.
  unfold get_utokens_lib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_fresh_atom_swap : slow.

Lemma compute_step_swap_cs1_aux_success_implies {o} :
  forall can1 can2 l1 l2 bs (t : @NTerm o) u,
    compute_step_swap_cs1_aux can1 can2 l1 l2 bs t = csuccess u
    -> {n1 : choice_sequence_name
       & {n2 : choice_sequence_name
       & {w : NTerm
       & can1 = Ncseq n1
       # can2 = Ncseq n2
       # l1 = []
       # l2 = []
       # bs = [bterm [] w]
       # u = mk_swap_cs2 n1 n2 w }}}.
Proof.
  introv comp.
  unfold compute_step_swap_cs2 in comp.
  destruct can1; simpl in comp; ginv.
  destruct can2; simpl in comp; ginv.
  destruct l1; simpl in comp; ginv.
  destruct l2; simpl in comp; ginv.
  destruct bs as [|b]; ginv.
  destruct b; simpl in *; ginv.
  destruct l; simpl in *; ginv.
  destruct bs; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto.
Qed.

Lemma compute_step_swap_cs0_aux_success_implies {o} :
  forall can1 can2 l1 l2 bs (t : @NTerm o) u,
    compute_step_swap_cs0_aux can1 can2 l1 l2 bs t = csuccess u
    -> {n1 : choice_sequence_name
       & {n2 : choice_sequence_name
       & {w : NTerm
       & can1 = Ncseq n1
       # can2 = Ncseq n2
       # l1 = []
       # l2 = []
       # bs = [bterm [] w]
       # u = push_swap_cs0 n1 n2 w }}}.
Proof.
  introv comp.
  unfold compute_step_swap_cs2 in comp.
  destruct can1; simpl in comp; ginv.
  destruct can2; simpl in comp; ginv.
  destruct l1; simpl in comp; ginv.
  destruct l2; simpl in comp; ginv.
  destruct bs as [|b]; ginv.
  destruct b; simpl in *; ginv.
  destruct l; simpl in *; ginv.
  destruct bs; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto.
Qed.

Ltac boolvar2 := repeat (boolvar_step; GC; subst; tcsp).

Lemma swap_cs_op_swap_cs_op {o} :
  forall n1 n2 sw (op : @Opid o),
    swap_cs_op (swap_cs sw n1, swap_cs sw n2) (swap_cs_op sw op)
    = swap_cs_op sw (swap_cs_op (n1, n2) op).
Proof.
  introv; destruct op; simpl; auto.
  { destruct c, sw; simpl; auto; boolvar; subst; tcsp. }
  { destruct n, sw; simpl; auto; boolvar; subst; tcsp;
      try (complete (destruct s; simpl; boolvar2)). }
Qed.

Lemma swap_cs_term_swap_cs_term {o} :
  forall n1 n2 sw (t : @NTerm o),
    swap_cs_term (swap_cs sw n1, swap_cs sw n2) (swap_cs_term sw t)
    = swap_cs_term sw (swap_cs_term (n1, n2) t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  rewrite swap_cs_op_swap_cs_op; auto.
  f_equal.
  allrw map_map; unfold compose; simpl; apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  eapply ind; eauto.
Qed.

Lemma swap_compute_step {o} :
  forall sw lib (a b : @NTerm o),
    compute_step lib a = csuccess b
    -> compute_step (swap_cs_plib sw lib) (swap_cs_term sw a) = csuccess (swap_cs_term sw b).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv comp; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|exc|abs] SCase.

  { SCase "Can".
    csunf comp; simpl in *; ginv; eauto. }

  { SCase "NCan".
    csunf comp; simpl in *.
    dterms w; try (complete (csunf; simpl; eauto));
      try (complete (apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
                     eapply ind in comp1; try (left; eauto); eauto 3 with slow; exrepnd;
                     csunf; simpl; allrw; simpl in *; allrw; simpl in *; auto)).

    { apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *.
      csunf; simpl; autorewrite with slow; auto. }

    { dopid_noncan ncan SSCase; simpl in *;
      try apply_comp_success;
      try (complete (dcwf h));
      try (complete (ginv; csunf; simpl in *; eauto)).

      { SSCase "NTUni".
        ginv; csunf; simpl in *; eauto.
        unfold compute_step_tuni; simpl; boolvar; try omega; autorewrite with slow; auto. }

      { SSCase "NSwapCs2".
        ginv; csunf; simpl in *; eauto.
        unfold push_swap_cs_can; tcsp.
        rewrite swap_cs_can_twice2.
        f_equal; f_equal.
        unfold push_swap_cs_bterms; repeat rewrite map_map; unfold compose.
        apply eq_maps; introv i; destruct x, s; simpl; auto;
          try rewrite swap_cs_term_push_swap_cs_sub_term; auto. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; ginv; subst; simpl in *.
      csunf; simpl.
      rewrite compute_step_catch_if_diff; tcsp; eauto 3 with slow. }

    { apply compute_step_fresh_success in comp; repeat (repndors; exrepnd; GC; ginv; subst; simpl in * );
        try (complete (csunf; simpl; boolvar; tcsp));
        try (rewrite compute_step_fresh_if_isvalue_like2; eauto 3 with slow;[]);
        try (rewrite computation3.compute_step_fresh_if_isnoncan_like; eauto 3 with slow;[]);
        autorewrite with slow; auto.
      pose proof (ind w2 (subst w2 w0 (mk_utoken (get_fresh_atom lib w2))) [w0]) as ind.
      rewrite simple_osize_subst in ind; eauto 3 with slow.
      repeat (autodimp ind hyp); eauto 3 with slow.
      apply ind in comp2; clear ind.
      repeat (autorewrite with slow in *; simpl in *; fold_terms).
      allrw; simpl; auto. }

    { dopid_noncan ncan SSCase; simpl in *;
        try apply_comp_success;
        try (complete (dcwf h));
        try (complete (dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
                       unfold apply_bterm; autorewrite with slow; simpl; eauto)).

      { SSCase "NEApply".
        inversion comp0; subst; clear comp0.
        repndors; exrepnd; subst; simpl in *; tcsp.

        { apply compute_step_eapply2_success in comp1; repeat (repndors; exrepnd; subst; simpl in * ); ginv.
          { inversion comp3; subst; clear comp3; simpl in *.
            csunf; simpl.
            apply iscan_implies in comp0; exrepnd; subst; simpl in *.
            unfold compute_step_eapply; simpl; unfold apply_bterm; autorewrite with slow; auto. }
          { inversion comp1; subst; clear comp1; simpl in *.
            csunf; simpl.
            unfold compute_step_eapply; simpl; boolvar; try omega; autorewrite with slow.
            rewrite find_cs_value_at_swap; allrw; unfold CSVal2term; autorewrite with slow.
            destruct v; simpl; auto. } }

        { fold_terms; rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow. }

        { fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
          erewrite ind; try exact comp1; try (right; left;reflexivity); eauto 3 with slow. } }

      { SSCase "NSwapCs1".
        dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
          unfold apply_bterm; autorewrite with slow; simpl; eauto.
        { apply compute_step_swap_cs1_aux_success_implies in comp; exrepnd; subst; simpl in *; auto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); eauto; eauto 3 with slow.
          simpl in *; allrw; simpl; auto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); eauto; eauto 3 with slow.
          simpl in *; allrw; simpl; auto. } }

      { SSCase "NSwapCs0".
        dterms w; ginv; csunf; simpl in *; repndors; repnd; subst; simpl in *;
          unfold apply_bterm; autorewrite with slow; simpl; eauto.
        { apply compute_step_swap_cs0_aux_success_implies in comp; exrepnd; subst; simpl in *; auto.
          unfold push_swap_cs0, push_swap_cs_sub_term.
          rewrite <- lsubst_aux_swap_cs_term; autorewrite with slow.
          rewrite swap_cs_term_swap_cs_term; auto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); eauto; eauto 3 with slow.
          simpl in *; allrw; simpl; auto. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left); eauto; eauto 3 with slow.
          simpl in *; allrw; simpl; auto. } }

      { inversion comp3; subst; csunf; simpl; autorewrite with slow; tcsp. }

      { inversion comp4; subst; clear comp4; repndors; repnd; subst; simpl in *; csunf; simpl; fold_terms; tcsp.
        boolvar; autorewrite with slow in *; subst; try omega; tcsp. }

      { inversion comp4; subst; clear comp4; repndors; repnd; subst; simpl in *; csunf; simpl; fold_terms; tcsp.
        { unfold sumbool_rec, sumbool_rect; simpl.
          boolvar; try omega; GC; tcsp. }
        { boolvar; subst; try omega.
          autorewrite with slow; tcsp. } }

      { dcwf h; dterms w; simpl in *.
        { apply compute_step_compop_success_can_can in comp; exrepnd; subst; simpl.
          csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          repndors; exrepnd; subst; simpl in *; unfold compute_step_comp; simpl; autorewrite with slow.
          { repeat rewrite get_param_from_cop_swap_cs_can; allrw; boolvar; tcsp. }
          { repeat rewrite get_param_from_cop_swap_cs_can; allrw; destruct pk1, pk2; subst; boolvar; ginv; tcsp;
              inversion e as [xx]; apply swap_cs_inj in xx; subst; tcsp. } }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          simpl in *; allrw; simpl; tcsp. }
        { csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @co_wf_false_implies_not in Heqh0; tcsp)).
          simpl in *; allrw; simpl; tcsp. } }

      { dcwf h; dterms w; simpl in *.
        { apply compute_step_arithop_success_can_can in comp; exrepnd; subst; simpl.
          csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          repndors; exrepnd; subst; simpl in *; unfold compute_step_arith; simpl; autorewrite with slow.
          repeat rewrite get_param_from_cop_swap_cs_can; allrw; boolvar; tcsp. }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          simpl in *; allrw; simpl; tcsp. }
        { csunf; simpl; dcwf h; autorewrite with slow in *; tcsp;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)). }
        { apply on_success_csuccess in comp; exrepnd; subst; simpl in *.
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow.
          csunf; simpl; dcwf h; autorewrite with slow in *;
            try (complete (apply @ca_wf_false_implies_not in Heqh0; tcsp)).
          simpl in *; allrw; simpl; tcsp. } }

      { dterms w; csunf; simpl; autorewrite with slow; tcsp.
        destruct (canonical_form_test_for c w4); tcsp. } }

    { apply compute_step_catch_success in comp; repndors; exrepnd; subst; simpl in *.
      { inversion comp2; subst; simpl in *; clear comp2.
        csunf; simpl; autorewrite with slow; auto. }
      { csunf; simpl.
        rewrite compute_step_catch_if_diff; tcsp; eauto 3 with slow. } }

    { apply compute_step_fresh_success in comp; exrepnd; subst; simpl in *; ginv. } }

  { csunf comp; simpl in *; ginv; csunf; simpl; tcsp. }

  { csunf comp; simpl in *.
    apply compute_step_lib_success in comp; exrepnd; subst.
    csunf; simpl.
    rewrite swap_cs_term_mk_instance.
    eapply found_entry_implies_compute_step_lib_success.
    apply implies_found_entry_swap_cs_plib; eauto. }
Qed.

Lemma swap_compute_at_most_k_steps {o} :
  forall {sw} {lib : @plibrary o} n {a b : @NTerm o},
    compute_at_most_k_steps lib n a = csuccess b
    -> compute_at_most_k_steps (swap_cs_plib sw lib) n (swap_cs_term sw a) = csuccess (swap_cs_term sw b).
Proof.
  induction n; introv comp; simpl in *; ginv; eauto.
  remember (compute_at_most_k_steps lib n a) as comp'; symmetry in Heqcomp'.
  destruct comp'; ginv.
  eapply IHn in Heqcomp'; auto; exrepnd; allrw.
  apply swap_compute_step; auto.
Qed.

Lemma swap_reduces_in_atmost_k_steps {o} :
  forall {sw} {lib : @plibrary o} n {a b : @NTerm o},
    reduces_in_atmost_k_steps lib a b n
    -> reduces_in_atmost_k_steps (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b) n.
Proof.
  introv r.
  unfold reduces_in_atmost_k_steps in *.
  eapply swap_compute_at_most_k_steps in r; eauto.
Qed.

Lemma swap_reduces_to {o} :
  forall {sw} {lib : @plibrary o} {a b : @NTerm o},
    reduces_to lib a b
    -> reduces_to (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  introv r; unfold reduces_to in *; exrepnd.
  eapply swap_reduces_in_atmost_k_steps in r0; eauto.
Qed.

Lemma swap_computes_to_value {o} :
  forall {sw} {lib : @plibrary o} {a b : @NTerm o},
    computes_to_value lib a b
    -> computes_to_value (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  introv r; unfold computes_to_value in *; repnd; dands; auto; eauto 3 with slow.
  eapply swap_reduces_to in r0; eauto; eauto 3 with slow.
Qed.
