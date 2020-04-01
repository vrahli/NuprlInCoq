Require Export rules_choice_util5.


Lemma lsubstc_mk_mqnat {o} :
  forall w (s : @CSub o) c, lsubstc mk_mqnat w s c = mkc_mqnat.
Proof.
  introv; unfold mk_mqnat; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_mk_mqnat : slow.

Lemma lsubstc_mk_lib_depth {o} :
  forall w (s : @CSub o) c, lsubstc mk_lib_depth w s c = mkc_lib_depth.
Proof.
  introv; apply cterm_eq; simpl; tcsp.
Qed.
Hint Rewrite @lsubstc_mk_lib_depth : slow.


Definition rule_depth {o} (H : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member mk_lib_depth mk_mqnat)))
    []
    [].

Lemma rule_depth_true {o} :
  forall uk (lib : library) (H : @bhyps o),
    rule_true uk lib (rule_depth H).
Proof.
  unfold rule_depth, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o mk_axiom (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  lsubst_tac; autorewrite with slow.

  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member
                uk lib' mk_mqnat mk_lib_depth s1 s2 H wT wt ct ct0 cT cT0) as q.
  lsubst_tac; autorewrite with slow in q.
  repeat (autodimp q hyp); eauto 2 with slow.

  clear dependent s1.
  clear dependent s2.
  introv eqh sim.
  autorewrite with slow.
  apply equality_lib_depth_in_mqnat.
Qed.
