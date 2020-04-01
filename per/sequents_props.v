(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents.
Require Export subst_props.


Lemma similarity_move_to_last {o} :
  forall uk lib b H J s1a s1b s2a s2b x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> !LIn x (free_vars_hyps J)
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> (similarity uk lib
          (snoc s1a (x, t1) ++ s1b)
          (snoc s2a (x, t2) ++ s2b)
          (snoc H (mk_nlhyp b x T) ++ J)
          <=>
          similarity uk lib
             (snoc (s1a ++ s1b) (x, t1))
             (snoc (s2a ++ s2b) (x, t2))
             (snoc (H ++ J) (mk_nlhyp b x T))).
Proof.
  introv cov len1 len2 ni1 ni2 ni3; split; intro sim.

  - apply similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim0; [|rw length_snoc; allrw; sp].
    apply app_split in sim2; [|rw length_snoc; allrw; sp].
    repnd; subst; cpx.
    apply similarity_snoc in sim5; simpl in sim5; exrepnd; cpx.

    apply similarity_snoc; simpl.

    assert (cover_vars T (s1a0 ++ s1b0)) as cv.
    clear sim2.
    allrw @cover_vars_eq.
    allrw subvars_prop.
    introv k; apply p in k; rw @dom_csub_app; rw in_app_iff; sp.

    exists (s1a0 ++ s1b0) (s2a0 ++ s2b0) t0 t3 w cv; dands; auto.

    apply similarity_app.
    exists s1a0 s1b0 s2a0 s2b0; dands; auto.

    rw @substitute_hyps_snoc_sub_weak in sim1; auto.

    rewrite @lsubstc_app_cover1 with (c' := p); auto.

  - apply similarity_snoc in sim; simpl in sim; exrepnd; cpx.
    apply similarity_app in sim3; simpl in sim3; exrepnd; subst; cpx.
    apply app_split in sim0; try omega; repnd; subst.
    apply app_split in sim3; try omega; repnd; subst.

    apply similarity_app; simpl.
    exists (snoc s1a0 (x,t0)) s1b0 (snoc s2a0 (x,t3)) s2b0.
    allrw length_snoc.
    dands; auto.

    assert (cover_vars T s1a0) as cv.
    allapply @similarity_dom; repnd.
    allrw @cover_vars_eq.
    rw sim3; auto.

    apply similarity_snoc; simpl.
    exists s1a0 s2a0 t0 t3 w cv; dands; auto.

    rewrite @lsubstc_app_cover1 with (c' := cv) in sim1; auto.
    rw @substitute_hyps_snoc_sub_weak; auto.
Qed.

Lemma sub_eq_hyps_nil_iff {o} :
  forall uk lib hs (s1 s2 : @CSub o),
    sub_eq_hyps uk lib [] [] s1 s2 hs <=> eq_hyps uk lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; introv; split; intro k; auto.
  - inversion k; subst; cpx.
  - inversion k; subst; cpx.
  - inversion k; subst; cpx.
    eapply eq_hyps_cons; eauto.
    apply IHhs; auto.
  - inversion k; subst; cpx.
    eapply sub_eq_hyps_cons; eauto.
    apply IHhs; auto.
Qed.

Lemma sub_eq_hyps_length {o} :
  forall uk lib (hs : @bhyps o) s1 s2 s3 s4,
    sub_eq_hyps uk lib s1 s2 s3 s4 hs
    -> (length s3 = length hs # length s4 = length hs).
Proof.
  induction hs using rev_list_indT; simpl; introv eh;
  inversion eh; subst; simpl; cpx.

  repeat (rewrite length_snoc).
  discover; sp.
Qed.

Lemma sub_eq_hyps_app {o} :
  forall uk lib (hs1 hs2 : @bhyps o) s1 s2 s3 s4,
    sub_eq_hyps uk lib s1 s2 s3 s4 (hs1 ++ hs2)
    <=>
    {s1a, s1b, s2a, s2b : CSub
      , s3 = s1a ++ s1b
      # s4 = s2a ++ s2b
      # length s1a = length hs1
      # length s2a = length hs1
      # sub_eq_hyps uk lib s1 s2 s1a s2a hs1
      # sub_eq_hyps uk lib (s1 ++ s1a) (s2 ++ s2a) s1b s2b hs2}.
Proof.
  induction hs2 using rev_list_indT; simpl; sp.

  - rewrite app_nil_r; split; intro k; exrepnd; subst.

    + applydup @sub_eq_hyps_length in k; sp.
      exists s3 (nil : (@CSub o)) s4 (nil : (@CSub o)); simpl; sp;
      allrewrite app_nil_r; auto.

    + inversion k1; subst; allrewrite app_nil_r; auto; cpx.

  - rewrite snoc_append_l; split; intro k; exrepnd; subst.

    + inversion k; cpx.

      rw IHhs2 in seh; sp; subst.
      exists s1a (snoc s1b (hvar a, t1)) s2a (snoc s2b (hvar a, t2)).
      repeat (rewrite snoc_append_l); sp.

      revert p2 p1 eqt.
      repeat (rw app_assoc); introv eqt.

      eapply sub_eq_hyps_cons; eauto.

    + inversion k1; cpx; clear k1.
      repeat (rw snoc_append_l).

      revert p2 p1 eqt.
      repeat (rw <- app_assoc); introv eqt.

      eapply sub_eq_hyps_cons; eauto.
      apply IHhs2.
      exists s1a s0 s2a s3; sp.
Qed.

Lemma sub_eq_hyps_snoc {o} :
  forall uk lib (hs : @bhyps o) h s1 s2 s3 s4,
    sub_eq_hyps uk lib s1 s2 s3 s4 (snoc hs h)
    <=>
    {s1a, s2a : CSub
     , {t1, t2 : CTerm
     , {w : wf_term (htyp h)
     , {p1 : cover_vars (htyp h) (s1 ++ s1a)
     , {p2 : cover_vars (htyp h) (s2 ++ s2a)
        , s3 = snoc s1a (hvar h, t1)
        # s4 = snoc s2a (hvar h, t2)
        # sub_eq_hyps uk lib s1 s2 s1a s2a hs
        # eqtypes
            uk lib
            (lvl h)
            (lsubstc (htyp h) w (s1 ++ s1a) p1)
            (lsubstc (htyp h) w (s2 ++ s2a) p2)}}}}}.
Proof.
  introv; split; intro k; exrepnd; subst.
  inversion k; subst; cpx.
  exists s0 s5 t1 t2 w p1 p2; sp.
  eapply sub_eq_hyps_cons; eauto.
Qed.

Lemma sub_eq_hyps_move_to_last {o} :
  forall uk lib b H J s1 s2 s1a s1b s2a s2b x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> !LIn x (hyps_free_vars J)
    -> (sub_eq_hyps uk lib
          s1 s2
          (snoc s1a (x, t1) ++ s1b)
          (snoc s2a (x, t2) ++ s2b)
          (snoc H (mk_nlhyp b x T) ++ J)
          <=>
          sub_eq_hyps uk lib
             s1 s2
             (snoc (s1a ++ s1b) (x, t1))
             (snoc (s2a ++ s2b) (x, t2))
             (snoc (H ++ J) (mk_nlhyp b x T))).
Proof.
  introv cov len1 len2 ni1; split; intro h.

  - apply sub_eq_hyps_app in h; simpl in h; exrepnd; cpx.
    apply app_split in h0;
      [|rw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h2;
      [|rw length_snoc; allapply @eq_hyps_length; allrw; sp].
    repnd; subst; cpx.
    apply sub_eq_hyps_snoc in h5; simpl in h5; exrepnd; subst; cpx.

    apply sub_eq_hyps_snoc; simpl.

    assert (cover_vars T (s1 ++ s1a0 ++ s1b0)) as cv1.
    clear h0.
    allrw @cover_vars_eq.
    allrw subvars_prop.
    introv i; apply p1 in i.
    allrw @dom_csub_app; allrw in_app_iff; sp.

    assert (cover_vars T (s2 ++ s2a0 ++ s2b0)) as cv2.
    clear h0.
    allrw @cover_vars_eq.
    allrw subvars_prop.
    introv i; apply p2 in i.
    allrw @dom_csub_app; allrw in_app_iff; sp.

    exists (s1a0 ++ s1b0) (s2a0 ++ s2b0) t0 t3 w cv1 cv2; dands; auto.

    apply sub_eq_hyps_app.
    exists s1a0 s1b0 s2a0 s2b0; dands; auto.

    repeat (rw snoc_append_l in h1).
    apply sub_eq_hyps_snoc_weak2 in h1; auto.

    revert cv1 cv2; repeat (rw app_assoc); introv.
    rewrite @lsubstc_app_cover1 with (c' := p1).
    rewrite @lsubstc_app_cover1 with (c' := p2).
    PI; auto.

  - apply sub_eq_hyps_snoc in h; simpl in h; exrepnd; cpx.
    apply sub_eq_hyps_app in h3; simpl in h3; exrepnd; cpx.
    apply app_split in h1;
      [|allapply @eq_hyps_length; allrw; sp].
    apply app_split in h3;
      [|allapply @eq_hyps_length; allrw; sp].
    repnd; subst.

    apply sub_eq_hyps_app.
    exists (snoc s1a0 (x,t0)) s1b0 (snoc s2a0 (x,t3)) s2b0; dands; auto;
    allrw length_snoc; allrw; auto.

    assert (cover_vars T (s1 ++ s1a0)) as cv1.
    clear h0.
    allapply @sub_eq_hyps_dom; repnd.
    rw @cover_vars_eq; allrw @dom_csub_app; allrw; auto.
    apply subvars_comm_r.
    apply subvars_app_weak_l; auto.

    assert (cover_vars T (s2 ++ s2a0)) as cv2.
    clear h0.
    allapply @sub_eq_hyps_dom; repnd.
    rw @cover_vars_eq; allrw @dom_csub_app; allrw; auto.
    apply subvars_comm_r.
    apply subvars_app_weak_l; auto.

    apply sub_eq_hyps_snoc; simpl.
    exists s1a0 s2a0 t0 t3 w cv1 cv2; dands; auto.

    revert p1 p2 h0; repeat (rw app_assoc); introv h.
    rewrite @lsubstc_app_cover1 with (c' := cv1) in h.
    rewrite @lsubstc_app_cover1 with (c' := cv2) in h.
    PI; auto.

    repeat (rw snoc_append_l).
    apply sub_eq_hyps_snoc_weak; auto.
Qed.

Lemma eq_hyps_move_to_last {o} :
  forall uk lib b H J s1a s1b s2a s2b x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> !LIn x (hyps_free_vars J)
    -> (eq_hyps uk lib
          (snoc s1a (x, t1) ++ s1b)
          (snoc s2a (x, t2) ++ s2b)
          (snoc H (mk_nlhyp b x T) ++ J)
          <=>
          eq_hyps uk lib
             (snoc (s1a ++ s1b) (x, t1))
             (snoc (s2a ++ s2b) (x, t2))
             (snoc (H ++ J) (mk_nlhyp b x T))).
Proof.
  introv cov len1 len2 ni1.

  pose proof (sub_eq_hyps_move_to_last uk lib b H J [] [] s1a s1b s2a s2b x t1 t2 T) as h;
    repeat (autodimp h hyp).
  repeat (rw @sub_eq_hyps_nil_iff in h); auto.
Qed.

Lemma hyps_functionality_move_to_last {o} :
  forall uk lib b H J s1 s2 x (t : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1 = length H
    -> !LIn x (free_vars_hyps J)
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> hyps_functionality uk lib (snoc s1 (x, t) ++ s2) (snoc H (mk_nlhyp b x T) ++ J)
    -> hyps_functionality uk lib (snoc (s1 ++ s2) (x, t)) (snoc (H ++ J) (mk_nlhyp b x T)).
Proof.
  introv cov len ni1 ni2 ni3 hf sim.

  dup sim as sim'.
  apply similarity_snoc in sim; simpl in sim; exrepnd; cpx.
  apply similarity_app in sim3; simpl in sim3; exrepnd; subst; cpx.
  apply app_split in sim0; try omega; repnd; subst.

  pose proof (hf (snoc s2a0 (x,t2) ++ s2b)) as h; clear hf.

  autodimp h hyp.

  apply similarity_move_to_last; auto.
  apply eq_hyps_move_to_last; auto.
Qed.

Lemma substitute_hyps_move_to_last {o} :
  forall H s1 s2 x (t : @CTerm o),
    !LIn x (dom_csub s2)
    -> substitute_hyps (snoc s1 (x, t) ++ s2) H
       = substitute_hyps (snoc (s1 ++ s2) (x, t)) H.
Proof.
  induction H; introv ni; simpl; auto.
  apply eq_cons; auto.
  destruct a; simpl.
  apply equal_hyps.
  apply csubst_snoc_app_move_to_last; auto.
Qed.

Lemma similarity_move_down {o} :
  forall uk lib b H J K s1a s1b s1c s2a s2b s2c x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> length s1b = length J
    -> length s2b = length J
    -> !LIn x (free_vars_hyps J)
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> (similarity uk lib
          ((snoc s1a (x, t1) ++ s1b) ++ s1c)
          ((snoc s2a (x, t2) ++ s2b) ++ s2c)
          ((snoc H (mk_nlhyp b x T) ++ J) ++ K)
          <=>
          similarity uk lib
             (snoc (s1a ++ s1b) (x, t1) ++ s1c)
             (snoc (s2a ++ s2b) (x, t2) ++ s2c)
             (snoc (H ++ J) (mk_nlhyp b x T) ++ K)).
Proof.
  introv cov len1 len2 len3 len4 ni1 ni2 ni3; split; intro sim.

  - apply similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim0; [|allrw length_app; allrw length_snoc; allrw; sp].
    apply app_split in sim2; [|allrw length_app; allrw length_snoc; allrw; sp].
    repnd; subst; cpx.

    apply similarity_app; allrw length_snoc; allrw length_app; allrw length_snoc.
    exists (snoc (s1a ++ s1b) (x, t1)) s1b0 (snoc (s2a ++ s2b) (x, t2)) s2b0; dands; auto;
    allrw length_snoc; allrw length_app; allrw length_snoc; allrw; sp.

    apply similarity_move_to_last; auto.
    rw <- @substitute_hyps_move_to_last; auto.

    apply similarity_app in sim5; exrepnd; cpx.
    apply app_split in sim0; [|allrw length_snoc; allrw; sp].
    apply app_split in sim5; [|allrw length_snoc; allrw; sp].
    repnd; subst; cpx.
    rw @substitute_hyps_snoc_sub_weak in sim2; auto.
    apply similarity_dom in sim2; repnd.
    allrw @vars_hyps_substitute_hyps; allrw; sp.

  - apply similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim0; [|allrw length_snoc; allrw length_app; allrw; sp].
    apply app_split in sim2; [|allrw length_snoc; allrw length_app; allrw; sp].
    repnd; subst; cpx.

    apply similarity_app; allrw length_snoc; allrw length_app; allrw length_snoc.
    exists (snoc s1a (x, t1) ++ s1b) s1b0 (snoc s2a (x, t2) ++ s2b) s2b0; dands; auto;
    allrw length_snoc; allrw length_app; allrw length_snoc; allrw; sp.

    apply similarity_move_to_last; auto.
    rw @substitute_hyps_move_to_last; auto.

    apply similarity_snoc in sim5; simpl in sim5; exrepnd; cpx.
    apply similarity_app in sim6; exrepnd; cpx.
    apply app_split in sim0; [|allrw length_snoc; allrw; sp].
    apply app_split in sim6; [|allrw length_snoc; allrw; sp].
    repnd; subst; cpx.
    apply similarity_dom in sim5; repnd.
    allrw @vars_hyps_substitute_hyps; allrw; sp.
Qed.

Lemma sub_eq_hyps_move_to_last_in_sub {o} :
  forall uk lib H s1a s1b s2a s2b s3 s4 x (t1 t2 : @CTerm o),
    !LIn x (dom_csub s1b)
    -> !LIn x (dom_csub s2b)
    -> (sub_eq_hyps uk lib
          (snoc s1a (x,t1) ++ s1b)
          (snoc s2a (x,t2) ++ s2b)
          s3 s4 H
          <=>
          sub_eq_hyps uk lib
             (snoc (s1a ++ s1b) (x, t1))
             (snoc (s2a ++ s2b) (x, t2))
             s3 s4 H).
Proof.
  induction H using rev_list_indT; simpl; introv ni1 ni2; split; intro k;
  inversion k; subst; cpx; clear k.

  - pose proof (lsubstc_snoc_app_move_down (htyp a) s1a s1b s1 x t1 w p1 ni1) as h.
    exrepnd.
    rw h0 in eqt; clear h0.

    pose proof (lsubstc_snoc_app_move_down (htyp a) s2a s2b s2 x t2 w p2 ni2) as k.
    exrepnd.
    rw k0 in eqt; clear k0.

    eapply sub_eq_hyps_cons; eauto.
    apply IHlist; auto.

  - pose proof (lsubstc_snoc_app_move_down2 (htyp a) s1a s1b s1 x t1 w p1 ni1) as h.
    exrepnd.
    rw h0 in eqt; clear h0.

    pose proof (lsubstc_snoc_app_move_down2 (htyp a) s2a s2b s2 x t2 w p2 ni2) as k.
    exrepnd.
    rw k0 in eqt; clear k0.

    eapply sub_eq_hyps_cons; eauto.
    apply IHlist; auto.
Qed.

Lemma sub_eq_hyps_move_down {o} :
  forall uk lib b H J K s1 s2 s1a s1b s1c s2a s2b s2c x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> length s1b = length J
    -> length s2b = length J
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> (sub_eq_hyps uk lib
          s1 s2
          ((snoc s1a (x, t1) ++ s1b) ++ s1c)
          ((snoc s2a (x, t2) ++ s2b) ++ s2c)
          ((snoc H (mk_nlhyp b x T) ++ J) ++ K)
          <=>
          sub_eq_hyps uk lib
             s1 s2
             ((snoc (s1a ++ s1b) (x, t1)) ++ s1c)
             ((snoc (s2a ++ s2b) (x, t2)) ++ s2c)
             ((snoc (H ++ J) (mk_nlhyp b x T)) ++ K)).
Proof.
  introv cov len1 len2 len3 len4 ni1 ni2; split; intro h.

  - apply sub_eq_hyps_app in h; simpl in h; exrepnd; cpx.
    apply app_split in h0;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h2;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    exrepnd; subst; cpx.

    apply sub_eq_hyps_app.
    exists (snoc (s1a ++ s1b) (x, t1)) s1b0 (snoc (s2a ++ s2b) (x, t2)) s2b0;
      dands; auto; allrw length_snoc; allrw length_app; allrw; auto.

    apply sub_eq_hyps_move_to_last; auto.

    repeat (rw snoc_append_l).
    repeat (rw app_assoc in h1).
    repeat (rw snoc_append_l in h1).
    apply sub_eq_hyps_move_to_last_in_sub in h1; auto.
    repeat (rw app_assoc); auto.

    apply sub_eq_hyps_app in h5; exrepnd; cpx.
    apply app_split in h0;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h5;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    repnd; subst; cpx.
    apply sub_eq_hyps_dom in h2; repnd; allrw; sp.

    apply sub_eq_hyps_app in h5; exrepnd; cpx.
    apply app_split in h0;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h5;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    repnd; subst; cpx.
    apply sub_eq_hyps_dom in h2; repnd; allrw; sp.

  - apply sub_eq_hyps_app in h; simpl in h; exrepnd; cpx.
    apply app_split in h0;
      [|allrw length_snoc; allrw length_app; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h2;
      [|allrw length_snoc; allrw length_app; allapply @eq_hyps_length; allrw; sp].
    exrepnd; subst; cpx.

    apply sub_eq_hyps_app.
    exists (snoc s1a (x, t1) ++ s1b) s1b0 (snoc s2a (x, t2) ++ s2b) s2b0;
      dands; auto; allrw length_app; allrw length_snoc; allrw; auto.

    apply sub_eq_hyps_move_to_last; auto.

    repeat (rw snoc_append_l in h1).
    repeat (rw app_assoc).
    repeat (rw snoc_append_l).
    repeat (rw app_assoc in h1); auto.
    apply sub_eq_hyps_move_to_last_in_sub in h1; auto.

    apply sub_eq_hyps_snoc in h5; simpl in h5; exrepnd; subst; cpx.
    apply sub_eq_hyps_app in h6; exrepnd; cpx.
    apply app_split in h2;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h6;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    repnd; subst; cpx.
    apply sub_eq_hyps_dom in h5; repnd; allrw; sp.

    apply sub_eq_hyps_snoc in h5; simpl in h5; exrepnd; subst; cpx.
    apply sub_eq_hyps_app in h6; exrepnd; cpx.
    apply app_split in h2;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    apply app_split in h6;
      [|allrw length_app; allrw length_snoc; allapply @eq_hyps_length; allrw; sp].
    repnd; subst; cpx.
    apply sub_eq_hyps_dom in h5; repnd; allrw; sp.
Qed.

Lemma eq_hyps_move_down {o} :
  forall uk lib b H J K s1a s1b s1c s2a s2b s2c x (t1 t2 : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1a = length H
    -> length s2a = length H
    -> length s1b = length J
    -> length s2b = length J
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> (eq_hyps uk lib
          ((snoc s1a (x, t1) ++ s1b) ++ s1c)
          ((snoc s2a (x, t2) ++ s2b) ++ s2c)
          ((snoc H (mk_nlhyp b x T) ++ J) ++ K)
          <=>
          eq_hyps uk lib
             ((snoc (s1a ++ s1b) (x, t1)) ++ s1c)
             ((snoc (s2a ++ s2b) (x, t2)) ++ s2c)
             ((snoc (H ++ J) (mk_nlhyp b x T)) ++ K)).
Proof.
  introv cov len1 len2 len3 len4 ni1 ni2.

  pose proof (sub_eq_hyps_move_down uk lib b H J K [] [] s1a s1b s1c s2a s2b s2c x t1 t2 T) as h;
    repeat (autodimp h hyp).
  repeat (rw @sub_eq_hyps_nil_iff in h); auto.
Qed.

Lemma hyps_functionality_move_down {o} :
  forall uk lib b H J K s1 s2 s3 x (t : @CTerm o) T,
    covered T (vars_hyps H)
    -> length s1 = length H
    -> length s2 = length J
    -> !LIn x (free_vars_hyps J)
    -> !LIn x (hyps_free_vars J)
    -> !LIn x (vars_hyps J)
    -> (hyps_functionality uk lib
          ((snoc s1 (x, t) ++ s2) ++ s3)
          ((snoc H (mk_nlhyp b x T) ++ J) ++ K)
        <=> hyps_functionality uk lib
              (snoc (s1 ++ s2) (x, t) ++ s3)
              (snoc (H ++ J) (mk_nlhyp b x T) ++ K)).
Proof.
  introv cov len1 len2 ni1 ni2 ni3; split; introv hf sim.

  - dup sim as sim'.

    apply similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim0; allrw length_snoc; allrw length_app; try omega; repnd; subst.
    apply similarity_snoc in sim5; simpl in sim5; exrepnd; cpx.
    apply similarity_app in sim6; simpl in sim6; exrepnd; subst; cpx.
    apply app_split in sim0; try omega; repnd; subst.

    apply eq_hyps_move_down; auto;
    [ allapply @similarity_length; repnd; allrw @length_substitute_hyps; allrw; auto
    | ].

    apply hf.
    apply similarity_move_down; auto.
    allapply @similarity_length; repnd; allrw @length_substitute_hyps; allrw; auto.

  - dup sim as sim'.

    apply similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim0; [|allrw length_app; allrw length_snoc; allrw; sp].
    repnd; subst.
    apply similarity_app in sim5; simpl in sim5; exrepnd; subst; cpx.
    apply app_split in sim0; [|allrw length_app; allrw length_snoc; allrw; sp].
    repnd; subst.
    apply similarity_snoc in sim8; simpl in sim8; exrepnd; cpx.
    allrw length_app; allrw length_snoc; cpx.

    apply eq_hyps_move_down; auto;
    [ allapply @similarity_length; repnd; allrw @length_substitute_hyps; allrw; auto
    | ].

    apply hf.
    apply similarity_move_down; auto.
    allapply @similarity_length; repnd; allrw @length_substitute_hyps; allrw; auto.
Qed.

Lemma vs_wf_hypotheses_eqvars {o} :
  forall vs1 vs2 (H : @bhyps o),
    eqvars vs1 vs2
    -> vs_wf_hypotheses vs1 H
    -> vs_wf_hypotheses vs2 H.
Proof.
  induction H using rev_list_indT; simpl; introv eqv wf; auto.
  inversion wf; cpx.
  allrw in_app_iff; allrw not_over_or; repnd.
  constructor; auto.
  - allrw @isprog_vars_eq; repnd; dands; auto.
    allrw subvars_prop; introv k; discover; allrw in_app_iff; sp.
    left.
    rw eqvars_prop in eqv.
    apply eqv; auto.
  - rw in_app_iff; rw not_over_or; sp.
    rw eqvars_prop in eqv; discover; sp.
Qed.

Lemma vs_wf_hypotheses_snoc_weak_iff {p} :
  forall v vs hs,
    !LIn v (@free_vars_hyps p hs)
    -> vs_wf_hypotheses (snoc vs v) hs
    -> vs_wf_hypotheses vs hs.
Proof.
  induction hs using rev_list_indT; introv ni wf; allsimpl; auto.
  inversion wf; cpx.
  allrw in_app_iff; allrw in_snoc; allrw not_over_or; repnd.
  allrw @free_vars_hyps_snoc; allrw in_app_iff; allrw not_over_or; repnd.
  allrw in_remove_nvars.
  constructor; auto.
  - allrw @isprog_vars_eq; repnd; dands; auto.
    allrw subvars_prop; introv i; discover.
    allrw in_app_iff; allrw in_snoc; sp; subst.
    destruct (in_deq NVar deq_nvar v (vars_hyps hs)); sp.
    provefalse; apply ni; sp.
  - allrw in_app_iff; allrw not_over_or; dands; auto.
Qed.
