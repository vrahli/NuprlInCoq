Require Export swap_cs.
Require Export library.


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

Definition swap_cs_restriction_pred {o} (r : cs_swap) (M : @RestrictionPred o) : RestrictionPred :=
  fun n t => M n (swap_cs_cterm r t).

Definition swap_cs_choice_seq_restr {o}
           (r     : cs_swap)
           (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match restr with
  | csc_type M => csc_type (swap_cs_restriction_pred r M)
(*  | csc_coq_law f => csc_coq_law (fun n => swap_cs_cterm r (f n))
  | csc_res P => csc_res (swap_cs_restriction_pred r P)*)
  end.

Definition swap_cs_choice_seq_vals {o} (r : cs_swap) (vals : @ChoiceSeqVals o) : ChoiceSeqVals :=
  map (swap_cs_cterm r) vals.

Definition swap_cs_default {o} (r : cs_swap) (d : nat -> @ChoiceSeqVal o) : nat -> ChoiceSeqVal :=
  fun n => swap_cs_cterm r (d n).

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

Definition swap_cs_lib_entry {o} (r : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name e => lib_cs (swap_cs r name) (swap_cs_choice_seq_entry r e)
  | lib_abs abs vars rhs correct => lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Fixpoint swap_cs_plib {o} (r : cs_swap) (lib : @plibrary o) :=
  match lib with
  | [] => []
  | entry :: entries => swap_cs_lib_entry r entry :: swap_cs_plib r entries
  end.

Definition swap_cs_in_lib_entry {o} (r : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name e => lib_cs name (swap_cs_choice_seq_entry r e)
  | lib_abs abs vars rhs correct => lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Fixpoint swap_cs_in_plib {o} (r : cs_swap) (lib : @plibrary o) :=
  match lib with
  | [] => []
  | entry :: entries => swap_cs_in_lib_entry r entry :: swap_cs_in_plib r entries
  end.
