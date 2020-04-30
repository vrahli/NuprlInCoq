(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export approx_star_swap.


Lemma swap_cs_soterm_idem {o} :
  forall (r : cs_swap)
         (t : @SOTerm o),
    swap_cs_soterm r (swap_cs_soterm r t) = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; auto;[|].

  { Case "sovar".
    f_equal.
    rewrite map_map; unfold compose; simpl.
    apply eq_map_l; introv i.
    apply ind in i; auto. }

  { Case "soterm".
    autorewrite with slow.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i.
    destruct x; apply ind in i.
    simpl; f_equal; auto. }
Qed.
Hint Rewrite @swap_cs_soterm_idem : slow.

Lemma swap_cs_choice_seq_vals_idem {o} :
  forall sw (vals : @ChoiceSeqVals o),
    swap_cs_choice_seq_vals sw (swap_cs_choice_seq_vals sw vals) = vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals.
  rewrite map_map; unfold compose; simpl.
  apply eq_map_l; introv i; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_vals_idem : slow.

Lemma swap_cs_choice_seq_restr_idem {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    swap_cs_choice_seq_restr sw (swap_cs_choice_seq_restr sw restr)
    = restr.
Proof.
  destruct restr; simpl; autorewrite with slow; dands; f_equal.

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }

(*  { apply functional_extensionality; introv; autorewrite with slow; auto. }

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }*)
Qed.
Hint Rewrite @swap_cs_choice_seq_restr_idem : slow.

Lemma swap_cs_choice_seq_entry_idem {o} :
  forall sw (entry : @ChoiceSeqEntry o),
    swap_cs_choice_seq_entry
      sw
      (swap_cs_choice_seq_entry sw entry)
    = entry.
Proof.
  introv.
  unfold swap_cs_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_entry_idem : slow.

Lemma swap_cs_lib_entry_idem {o} :
  forall sw (e : @library_entry o),
    swap_cs_lib_entry sw (swap_cs_lib_entry sw e) = e.
Proof.
  introv; destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow.

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Rewrite @swap_cs_lib_entry_idem : slow.

Lemma swap_cs_plib_idem {o} :
  forall sw (lib : @plibrary o),
    swap_cs_plib sw (swap_cs_plib sw lib) = lib.
Proof.
  induction lib; introv; simpl; dands; auto.
  autorewrite with slow; tcsp; try congruence.
Qed.
Hint Rewrite @swap_cs_plib_idem : slow.

Lemma swap_cs_bterm_idem {o} :
  forall sw (b : @BTerm o),
    swap_cs_bterm sw (swap_cs_bterm sw b) = b.
Proof.
  introv; destruct b; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_bterm_idem : slow.

Lemma implies_alpha_eq_bterm_swap_cs_bterm {o} :
  forall sw (a b : @BTerm o),
    alpha_eq_bterm a b
    -> alpha_eq_bterm (swap_cs_bterm sw a) (swap_cs_bterm sw b).
Proof.
  introv aeq; destruct a, b; simpl in *.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst; clear aeq.
  econstructor; autorewrite with slow; eauto.
  apply (implies_alpha_eq_swap_cs_term sw) in aeq'.
  repeat rewrite <- lsubst_swap_cs_term in aeq'; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_alpha_eq_bterm_swap_cs_bterm : slow.

Lemma implies_wf_sub_swap_cs_sub {o} :
  forall sw (sub : @Sub o),
    wf_sub sub
    -> wf_sub (swap_cs_sub sw sub).
Proof.
  induction sub; introv wf; repnd; simpl in *; auto.
  allrw @wf_sub_cons_iff; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_wf_sub_swap_cs_sub : slow.

Lemma swap_cs_sub_idem {o} :
  forall sw (sub : @Sub o),
    swap_cs_sub sw (swap_cs_sub sw sub) = sub.
Proof.
  induction sub; introv; repnd; simpl; auto; autorewrite with slow; auto; try congruence.
Qed.
Hint Rewrite @swap_cs_sub_idem : slow.

Lemma implies_approx_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx lib a b
    -> approx (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  cofix ind; introv apx.
  applydup @approx_relates_only_progs in apx as isp; repnd.
  constructor; unfold close_comput; dands; eauto 2 with slow;[|].

  { (* VAL case *)
    introv comp.
    apply (@swap_computes_to_value o sw) in comp.
    autorewrite with slow in comp; simpl in *.

    eapply approx_canonical_form in apx;[|eauto]; exrepnd.
    apply (@swap_computes_to_value o sw) in apx1.
    simpl in *; autorewrite with slow in *.
    eexists; dands; eauto.
    unfold lblift in *; autorewrite with slow in *; repnd; dands; auto.
    introv len; applydup apx0 in len.
    unfold blift in *; exrepnd.
    exists lv (swap_cs_term sw nt1) (swap_cs_term sw nt2).
    rewrite selectbt_map in len2; auto.
    apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len2.
    apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len1.
    simpl in *; autorewrite with slow in *.
    rewrite selectbt_map; auto; try congruence;[].
    dands; auto;[].

    introv.
    unfold approx_open, olift in *; repnd; dands; eauto 3 with slow;[].
    introv wf ispa ispb; left.
    pose proof (len0 (swap_cs_sub sw sub)) as len0.
    apply (implies_isprogram_swap_cs_term sw) in ispa.
    apply (implies_isprogram_swap_cs_term sw) in ispb.
    rewrite swap_cs_term_lsubst in ispa.
    rewrite swap_cs_term_lsubst in ispb.
    autorewrite with slow in *.
    repeat (autodimp len0 hyp); eauto 2 with slow.
    apply (ind _ sw) in len0.
    repeat rewrite <- lsubst_swap_cs_term in len0.
    autorewrite with slow in len0; exact len0. }

  { (* EXC case *)

    introv comp.
    apply (@swap_reduces_to o sw) in comp.
    autorewrite with slow in comp; simpl in *; fold_terms.

    eapply exception_approx in comp; eauto; exrepnd; repndors; tcsp;
      try (complete (inversion comp2)); try (complete (inversion comp1));[].
    apply (@swap_reduces_to o sw) in comp0; simpl in *; fold_terms.
    eexists; eexists; dands; eauto; left.
    { apply (ind _ sw) in comp2; autorewrite with slow in *; auto. }
    { apply (ind _ sw) in comp1; autorewrite with slow in *; auto. } }
Qed.

Lemma implies_approx_open_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx_open lib a b
    -> approx_open (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  introv apx.
  unfold approx_open, olift in *; repnd; dands; eauto 3 with slow.
  introv wf ispa ispb.
  pose proof (apx (swap_cs_sub sw sub)) as apx.
  apply (implies_isprogram_swap_cs_term sw) in ispa.
  apply (implies_isprogram_swap_cs_term sw) in ispb.
  rewrite swap_cs_term_lsubst in ispa.
  rewrite swap_cs_term_lsubst in ispb.
  autorewrite with slow in *.
  repeat (autodimp apx hyp); eauto 2 with slow.
  apply (implies_approx_swap_cs_term _ sw) in apx.
  repeat rewrite swap_cs_term_lsubst in apx.
  autorewrite with slow in *; auto.
Qed.

Lemma alpha_eq_bterm_preserves_osize_bterm {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> osize_bterm b1 = osize_bterm b2.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj lena lenb norep aeq']; subst; clear aeq.
  apply alpha_eq_preserves_osize in aeq'.
  repeat (rewrite lsubst_allvars_preserves_osize in aeq'; eauto 3 with slow).
Qed.

Lemma swap_cs_sub_if_nrut_sub {o} :
  forall sw (sub : @Sub o) l,
    nrut_sub l sub
    -> swap_cs_sub sw sub = sub.
Proof.
  induction sub; introv h; repnd; simpl; auto.
  allrw @nrut_sub_cons; exrepnd; subst; simpl in *; fold_terms.
  erewrite IHsub; eauto.
Qed.

Lemma implies_approx_star_swap_cs_term {o} :
  forall lib sw (a b : @NTerm o),
    approx_star lib a b
    -> approx_star (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b).
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv apx.
  { inversion apx as [? ? ? apx'|]; subst; clear apx.
    apply (implies_approx_open_swap_cs_term _ sw) in apx'; simpl in *.
    constructor; auto. }

  inversion apx as [|? ? ? ? ? len bl apo]; subst; clear apx; simpl in *.
  apply (implies_approx_open_swap_cs_term _ sw) in apo; simpl in *.
  apply (apso _ _ _ _ (map (swap_cs_bterm sw) lbt1')); autorewrite with slow; auto;[].
  unfold lblift_sub in *; repnd; autorewrite with slow in *; dands; auto; GC.
  introv len'; applydup bl in len'.
  repeat (rewrite selectbt_map; auto; try congruence);[].
  unfold blift_sub in *; exrepnd.
  exists lv (swap_cs_term sw nt1) (swap_cs_term sw nt2).
  apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len'1.
  apply (implies_alpha_eq_bterm_swap_cs_bterm sw) in len'2.
  simpl in *; dands; auto;[].
  repndors; exrepnd;[left|right].

  { dands; auto.
    { destruct op; simpl in *; tcsp; try (complete (intro xx; ginv)). }
    remember (bs {[n]}) as bt; destruct bt as [l t].
    eapply (ind t nt1 l); auto.
    { allrw; apply selectbt_in; auto. }
    apply alpha_eq_bterm_preserves_osize_bterm in len'2.
    simpl in *; autorewrite with slow in *; allrw; eauto 3 with slow. }

  subst; simpl in *.
  remember (bs {[n]}) as bt; destruct bt as [l t].
  eapply (ind t _ l) in len'4;
    try (complete (allrw; apply selectbt_in; auto));
    try (complete (rewrite simple_osize_lsubst; eauto 3 with slow;
                   apply alpha_eq_bterm_preserves_osize_bterm in len'2;
                   simpl in *; autorewrite with slow in *; allrw; eauto 3 with slow)).
  repeat rewrite <- lsubst_swap_cs_term in len'4.
  repeat (erewrite swap_cs_sub_if_nrut_sub in len'4; eauto).
  exists sub; dands; autorewrite with slow; auto.
Qed.

Lemma implies_reduces_in_atmost_k_steps_mk_swap_cs2 {o} :
  forall k lib sw (t u : @NTerm o),
    reduces_in_atmost_k_steps (swap_cs_plib sw lib) (swap_cs_term sw t) u k
    -> {k' : nat & k' <= k # reduces_in_atmost_k_steps lib (mk_swap_cs2 sw t) (mk_swap_cs2 sw (swap_cs_term sw u)) k'}.
Proof.
  induction k; introv comp; simpl in *.

  { exists 0; allrw @reduces_in_atmost_k_steps_0; subst; autorewrite with slow; auto. }

  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  destruct t as [v|op bs]; simpl in *.

  { csunf comp1; simpl in *; ginv. }

  destruct op as [can|ncan|nsw|exc|abs]; simpl in *.

  { csunf comp1; simpl in *; ginv.
    apply reduces_atmost_can in comp0; subst; simpl in *; autorewrite with slow.
    exists 0; dands; try omega; allrw @reduces_in_atmost_k_steps_0; auto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }

  { csunf comp1; simpl in *; ginv.
    apply reduces_atmost_exc in comp0; subst; simpl in *; autorewrite with slow.
    exists 0; dands; try omega; allrw @reduces_in_atmost_k_steps_0; auto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }
Qed.

Lemma implies_reduces_to_mk_swap_cs2 {o} :
  forall lib sw (t u : @NTerm o),
    reduces_to (swap_cs_plib sw lib) (swap_cs_term sw t) u
    -> reduces_to lib (mk_swap_cs2 sw t) (mk_swap_cs2 sw (swap_cs_term sw u)).
Proof.
  introv comp; unfold reduces_to in *; exrepnd.
  apply implies_reduces_in_atmost_k_steps_mk_swap_cs2 in comp0; exrepnd.
  exists k'; auto.
Qed.


Lemma extensional_swap_cs2 {o} : forall sw, extensional_op (@NSwapCs2 o sw).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @isprogram_swap_cs2_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_swap_cs2_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  apply computes_to_val_like_in_max_k_steps_swap_cs2_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto));[].
  repndors; exrepnd; subst; GC; fold_terms.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    applydup @reduces_atmost_preserves_program in Hcv4 as ispc1; auto; eauto 2 with slow.
    apply @no_change_after_value_ra with (k2:=k) in Hcv4; auto; try omega; [].
    applydup @reduces_atmost_preserves_program in Hcv4; auto; eauto 2 with slow.
    make_red_val_like Hcv4 h1.

    eapply Hi in h1; try apply implies_approx_star_swap_cs_term; try exact Has0bt; eauto 2 with slow.
    apply (implies_approx_star_swap_cs_term _ sw) in h1; simpl in *; autorewrite with slow in *.

    apply (implies_isprogram_swap_cs_term sw) in ispc1; simpl in *.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    exrepnd; fold_terms.

    unfold computes_to_val_like_in_max_k_steps in Hcv0; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv6; auto; try (complete (destruct k1; simpl; try omega)).
    make_red_val_like Hcv6 g.

    apply Hi with (v := push_swap_cs_can sw (swap_cs_can sw can) lbt') in g; auto; eauto 2 with slow.

    { eapply approx_star_open_trans;[eauto|].
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.

      unfold computes_to_value in h0; repnd.
      apply (@swap_reduces_to o sw) in h2.
      apply implies_reduces_to_mk_swap_cs2 in h2.
      autorewrite with slow in *.
      eapply reduces_to_trans;[exact h2|].
      apply reduces_to_if_step.
      csunf; simpl; auto. }

    { apply implies_isprogram_push_swap_cs_can; eauto 3 with slow. }

    applydup @computes_to_value_wf4 in h0.
    apply approx_star_push_swap_cs_can; auto; eauto 2 with slow.

  - unfold extensional_op_ind in Hi.
    apply isprogram_exception_iff in Hpra; repnd.
    apply (implies_isprogram_swap_cs_term sw) in Hpra.
    apply (implies_isprogram_swap_cs_term sw) in Hpra0.
    autorewrite with slow in *.

    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
      try omega; try (unfold isvalue_like; allsimpl; sp);
      try (apply isprogram_exception; auto);[].
    make_red_val_like Hcv3 h1.
    apply Hi with (v := swap_cs_term sw a1) in h1; auto; eauto 2 with slow;
      try (apply isprogram_exception; auto);
      try (apply implies_approx_star_swap_cs_term).

    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply @approx_trans with (b := mk_swap_cs2 (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) (mk_exception a' e')).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply implies_isprogram_mk_swap_cs2; eauto 3 with slow. }
      apply reduces_to_if_step; try reflexivity. }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      destruct nfo as [n1 n2]; simpl in *.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto. }
Qed.
