(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export Classical_Prop.
Require Export per_props_union.
Require Export per_props_equality.
Require Export per_props_squash.
Require Export per_props_not.
Require Export sequents_squash.
Require Export lsubstc_vars.
Require Export rules_choice.


Lemma mkcv_union_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_union [v] a b)
    = mkc_union (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @mkcv_union_substc : slow.

Lemma mkcv_or_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_or [v] a b)
    = mkc_or (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @mkcv_or_substc : slow.

Lemma mk_cv_app_r_mkc_var {o} :
  forall (a : @CTerm o) v t,
    substc a v (mk_cv_app_r [] [v] t) = substc a v t.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @mk_cv_app_r_mkc_var : slow.

Lemma lsubstc_vars_void {o} :
  forall (w : @wf_term o mk_void) s vs c,
    lsubstc_vars mk_void w s vs c
    = mkcv_void vs.
Proof.
  introv; apply cvterm_eq; simpl; auto.
  unfold mk_void, mk_false; simpl.
  unfold csubst.
  rewrite cl_lsubst_trivial; simpl; auto; eauto 3 with slow.
Qed.
Hint Rewrite @lsubstc_vars_void : slow.

Lemma lsubstc_vars_mk_not_as_mkcv {o} :
  forall (t : @NTerm o) (w : wf_term (mk_not t))
         (s : CSub) (vs : list NVar)
         (c : cover_vars_upto (mk_not t) s vs),
  {w1 : wf_term t $
  {c1 : cover_vars_upto t s vs $
  alphaeqcv
    vs
    (lsubstc_vars (mk_not t) w s vs c)
    (mkcv_not vs (lsubstc_vars t w1 s vs c1))}}.
Proof.
  introv.
  pose proof (lsubstc_vars_mk_fun_as_mkcv t mk_void w s vs c) as q; exrepnd.
  exists w1 c1; auto.
  unfold mk_not; rewrite mkcv_not_eq; auto.
  autorewrite with slow in *; auto.
Qed.

Hint Rewrite @mkcv_not_substc : slow.

Lemma isprog_vars_choice_seq_implies {o} :
  forall vs name, @isprog_vars o vs (mk_choice_seq name).
Proof.
  introv.
  allrw @isprog_vars_eq.
  simpl in *; autorewrite with slow.
  repnd; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_choice_seq_implies : slow.

Definition mkcv_choice_seq {o} vs (n : choice_sequence_name) : @CVTerm o vs :=
  exist (isprog_vars vs) (mk_choice_seq n) (isprog_vars_choice_seq_implies vs n).

Definition exists_1_choice {o} (a : choice_sequence_name) (n : NVar) : @CTerm o :=
  mkc_exists
    mkc_tnat
    n
    (mkcv_equality
       _
       (mkcv_apply _ (mkcv_choice_seq _ a) (mkc_var n))
       (mkcv_one _)
       (mkcv_tnat _)).

Lemma int_in_uni {o} : forall i lib, @equality o lib mkc_int mkc_int (mkc_uni i).
Proof.
  introv.
  exists (per_bar_eq lib (univi_eq_lib_per lib i)).
  dands; auto; eauto 3 with slow;[].

  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl.
  exists (equality_of_int_bar lib').
  apply CL_int.
  unfold per_int; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve int_in_uni : slow.

Lemma mkc_less_aux_in_uni {o} :
  forall i lib (a b c d e f g h : @CTerm o) ka kb ke kf,
    ccomputes_to_valc_ext lib a (mkc_integer ka)
    -> ccomputes_to_valc_ext lib b (mkc_integer kb)
    -> ccomputes_to_valc_ext lib e (mkc_integer ke)
    -> ccomputes_to_valc_ext lib f (mkc_integer kf)
    -> (equality lib (mkc_less a b c d) (mkc_less e f g h) (mkc_uni i)
        <=>
        (
          ((ka < kb)%Z # (ke < kf)%Z # equality lib c g (mkc_uni i))
          [+]
          ((kb <= ka)%Z # (kf <= ke)%Z # equality lib d h (mkc_uni i))
          [+]
          ((ka < kb)%Z # (kf <= ke)%Z # equality lib c h (mkc_uni i))
          [+]
          ((kb <= ka)%Z # (ke < kf)%Z # equality lib d g (mkc_uni i))
        )
       ).
Proof.
  introv ca cb ce cf.

  assert (ccequivc_ext
            lib
            (mkc_less a b c d)
            (mkc_less (mkc_integer ka) (mkc_integer kb) c d)) as c1.
  { apply ccomputes_to_valc_integer_implies_ccomputes_to_valc_mkc_less; auto. }

  assert (ccequivc_ext
            lib
            (mkc_less e f g h)
            (mkc_less (mkc_integer ke) (mkc_integer kf) g h)) as c2.
  { apply ccomputes_to_valc_integer_implies_ccomputes_to_valc_mkc_less; auto. }

  split; intro k; repnd.

  - destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                c) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                g) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[exact c3|].
      eapply equality_respects_cequivc_right;[exact c4|].
      eapply equality_respects_cequivc_left;[exact c1|].
      eapply equality_respects_cequivc_right;[exact c2|].
      auto.

    + right; right; left; dands; auto; try omega.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                c) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                h) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[exact c3|].
      eapply equality_respects_cequivc_right;[exact c4|].
      eapply equality_respects_cequivc_left;[exact c1|].
      eapply equality_respects_cequivc_right;[exact c2|].
      auto.

    + right; right; right; dands; auto; try omega.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                d) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                g) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[exact c3|].
      eapply equality_respects_cequivc_right;[exact c4|].
      eapply equality_respects_cequivc_left;[exact c1|].
      eapply equality_respects_cequivc_right;[exact c2|].
      auto.

    + right; left; dands; auto; try omega.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                d) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                h) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[exact c3|].
      eapply equality_respects_cequivc_right;[exact c4|].
      eapply equality_respects_cequivc_left;[exact c1|].
      eapply equality_respects_cequivc_right;[exact c2|].
      auto.

  - eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; exact c1|].
    eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; exact c2|].
    clear c1 c2 ca cb ce cf.
    repndors; exrepnd.

    + assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                c) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                g) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; exact c3|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; exact c4|].
      auto.

    + assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                d) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                h) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; exact c3|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; exact c4|].
      auto.

    + assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                c) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                h) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; exact c3|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; exact c4|].
      auto.

    + assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                d) as c3 by eauto 3 with slow.

      assert (ccequivc_ext
                lib
                (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                g) as c4 by eauto 3 with slow.

      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; exact c3|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; exact c4|].
      auto.
Qed.

(*Lemma mkc_less_in_uni {o} :
  forall i lib (a b c d e f g h : @CTerm o),
    equality lib (mkc_less a b c d) (mkc_less e f g h) (mkc_uni i)
    <=>
    all_in_ex_bar
      lib
      (fun lib =>
         {ka , kb , ke , kf : Z
         , a ===>(lib) (mkc_integer ka)
         # b ===>(lib) (mkc_integer kb)
         # e ===>(lib) (mkc_integer ke)
         # f ===>(lib) (mkc_integer kf)
         # (
             ((ka < kb)%Z # (ke < kf)%Z # equality lib c g (mkc_uni i))
             {+}
             ((kb <= ka)%Z # (kf <= ke)%Z # equality lib d h (mkc_uni i))
             {+}
             ((ka < kb)%Z # (kf <= ke)%Z # equality lib c h (mkc_uni i))
             {+}
             ((kb <= ka)%Z # (ke < kf)%Z # equality lib d g (mkc_uni i))
           )}).
Proof.
  introv.

  split; intro q; exrepnd.

  - applydup @equality_in_uni in q as k.
    applydup @tequality_refl in k.
    applydup @tequality_sym in k.
    apply tequality_refl in k1.
    allrw @fold_type.
    apply types_converge in k0.
    apply types_converge in k1.

    eapply all_in_ex_bar_modus_ponens2;[|exact k0|exact k1].
    clear k0 k1; introv x k0 k1.
    spcast.

    apply hasvaluec_mkc_less in k0.
    apply hasvaluec_mkc_less in k1.
    exrepnd.

    exists k6 k0 k2 k1; dands; spcast; eauto with slow;
    try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto 3 with slow)).

    pose proof (mkc_less_aux_in_uni
                  i lib' a b c d e f g h k6 k0 k2 k1) as p.
    repeat (autodimp p hyp);
      try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto 3 with slow)).

    eapply equality_monotone in q;[|exact x].
    apply p in q; sp.

  - apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;[|exact q]; clear q; introv x k.
    exrepnd.
    pose proof (mkc_less_aux_in_uni
                  i lib' a b c d e f g h ka kb ke kf) as p.
    spcast.
    repeat (autodimp p hyp).
    apply p.

    destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.
      repndors; repnd; try omega; auto.

    + right; right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; right; right; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.
Qed.*)

Lemma false_in_uni {p} :
  forall i lib, @equality p lib mkc_false mkc_false (mkc_uni i).
Proof.
  introv.
  rw @mkc_false_eq.
  apply mkc_approx_equality_in_uni.
  apply in_ext_implies_in_open_bar; introv ext.
  split; intro k; spcast; apply not_axiom_approxc_bot in k; sp.
Qed.
Hint Resolve false_in_uni : slow.

Lemma void_in_uni {p} :
  forall i lib, @equality p lib mkc_void mkc_void (mkc_uni i).
Proof.
  introv; rw @mkc_void_eq_mkc_false; eauto 3 with slow.
Qed.
Hint Resolve void_in_uni : slow.

Lemma true_in_uni {p} :
  forall i lib, @equality p lib mkc_true mkc_true (mkc_uni i).
Proof.
  introv.
  rw @mkc_true_eq.
  apply mkc_approx_equality_in_uni.
  apply in_ext_implies_in_open_bar; introv ext.
  split; intro k; spcast; tcsp.
Qed.
Hint Resolve true_in_uni : slow.

Lemma mkc_less_than_in_uni_aux {o} :
  forall i lib (a b c d : @CTerm o) ka kb kc kd,
    a ===>(lib) (mkc_integer ka)
    -> b ===>(lib) (mkc_integer kb)
    -> c ===>(lib) (mkc_integer kc)
    -> d ===>(lib) (mkc_integer kd)
    -> (equality lib (mkc_less_than a b) (mkc_less_than c d) (mkc_uni i)
        <=> (((ka < kb)%Z # (kc < kd)%Z) {+} ((kb <= ka)%Z # (kd <= kc)%Z))).
Proof.
  introv compa compb compc compd.
  allrw @mkc_less_than_eq.
  rw (mkc_less_aux_in_uni i lib a b mkc_true mkc_false c d mkc_true mkc_false ka kb kc kd compa compb compc compd).

  split; intro k; exrepnd; repndors; repnd; tcsp.

  - apply equality_in_uni in k.
    apply true_not_equal_to_false in k; sp.

  - apply equality_in_uni in k.
    apply tequality_sym in k.
    apply true_not_equal_to_false in k; sp.

  - destruct (Z_lt_le_dec ka kb); destruct (Z_lt_le_dec kc kd); tcsp; try omega.

    + left; dands; auto; eauto 3 with slow.

    + assert False; tcsp; repndors; repnd; tcsp; try omega.

    + assert False; tcsp; repndors; repnd; tcsp; try omega.

    + right; left; dands; auto; eauto 3 with slow; try omega.
Qed.

(*Lemma mkc_less_than_in_uni {o} :
  forall i lib (a b c d : @CTerm o),
    equality lib (mkc_less_than a b) (mkc_less_than c d) (mkc_uni i)
    <=>
    all_in_ex_bar
      lib
      (fun lib =>
         {ka , kb , kc , kd : Z
         , a ===>(lib) (mkc_integer ka)
         # b ===>(lib) (mkc_integer kb)
         # c ===>(lib) (mkc_integer kc)
         # d ===>(lib) (mkc_integer kd)
         # (
             ((ka < kb)%Z # (kc < kd)%Z)
             {+}
             ((kb <= ka)%Z # (kd <= kc)%Z)
           )}).
Proof.
  introv.
  allrw @mkc_less_than_eq.
  rw (mkc_less_in_uni i lib a b mkc_true mkc_false c d mkc_true mkc_false).

  split; intro k; exrepnd.

  - eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv x k; exrepnd.
    exists ka kb ke kf; dands; auto.
    repndors; repnd; tcsp.

    + apply equality_in_uni in k1.
      apply true_not_equal_to_false in k1; sp.

    + apply equality_in_uni in k1.
      apply tequality_sym in k1.
      apply true_not_equal_to_false in k1; sp.

  - eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv x k; exrepnd.
    exists ka kb kc kd; dands; auto.
    repndors; repnd; tcsp.

    { left; dands; eauto 3 with slow. }

    { right; left; dands; eauto 3 with slow. }
Qed.*)

Lemma fun_in_uni {p} :
  forall i lib (A1 A2 B1 B2 : @CTerm p),
    equality lib (mkc_fun A1 B1) (mkc_fun A2 B2) (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
      # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A1 -> equality lib' B1 B2 (mkc_uni i))).
Proof.
  intros.
  allrw <- @fold_mkc_fun.
  rw (equality_function lib).
  split; intro teq; repnd; dands; auto; introv x e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq lib' x t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp.

  - pose proof (teq lib' x) as teq.
    autodimp teq hyp.
    exists a; allapply @equality_refl; sp.
    repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma not_in_uni {p} :
  forall i lib (A1 A2 : @CTerm p),
    equality lib (mkc_not A1) (mkc_not A2) (mkc_uni i)
    <=>
    equality lib A1 A2 (mkc_uni i).
Proof.
  intros.
  rw @fun_in_uni; split; sp; eauto 3 with slow.
Qed.

Lemma mkc_le_in_uni_aux {o} :
  forall i lib (a b c d : @CTerm o) ka kb kc kd,
    a ===>(lib) (mkc_integer ka)
    -> b ===>(lib) (mkc_integer kb)
    -> c ===>(lib) (mkc_integer kc)
    -> d ===>(lib) (mkc_integer kd)
    -> (equality lib (mkc_le a b) (mkc_le c d) (mkc_uni i)
        <=> (((ka <= kb)%Z # (kc <= kd)%Z) {+} ((kb < ka)%Z # (kd < kc)%Z))).
Proof.
  introv compa compb compc compd.
  allrw @mkc_le_eq.
  rw @not_in_uni.
  rw (mkc_less_than_in_uni_aux i lib b a d c kb ka kd kc compb compa compd compc).
  split; intro k; repndors; repnd; tcsp; try omega.
Qed.

(*Lemma mkc_le_in_uni {o} :
  forall i lib (a b c d : @CTerm o),
    equality lib (mkc_le a b) (mkc_le c d) (mkc_uni i)
    <=>
    all_in_ex_bar
      lib
      (fun lib =>
         {ka , kb , kc , kd : Z
         , a ===>(lib) (mkc_integer ka)
         # b ===>(lib) (mkc_integer kb)
         # c ===>(lib) (mkc_integer kc)
         # d ===>(lib) (mkc_integer kd)
         # (
             ((ka <= kb)%Z # (kc <= kd)%Z)
             {+}
             ((kb < ka)%Z # (kd < kc)%Z)
           )}).
Proof.
  introv.
  allrw @mkc_le_eq.
  rw @not_in_uni.
  rw @mkc_less_than_in_uni.

  split; intro k.

  - eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv x k; exrepnd; spcast.
    exists kb ka kd kc; dands; spcast; auto.
    repndors; repnd; tcsp.

  - eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv x k; exrepnd; spcast.
    exists kb ka kd kc; dands; spcast; auto.
    repndors; repnd; tcsp.
Qed.*)

Lemma tnat_in_uni {o} : forall i lib, @equality o lib mkc_tnat mkc_tnat (mkc_uni i).
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply equality_set; dands; eauto 3 with slow.
  introv ext ea.
  autorewrite with slow.
  apply equality_in_int in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.
  unfold equality_of_int in ea; exrepnd; spcast.

  clear lib lib' ext y.
  rename lib'0 into lib.

  eapply mkc_le_in_uni_aux; eauto; try rewrite mkc_integer_as_mk_zero; eauto 2 with slow.
  destruct (Z_lt_le_dec k 0); tcsp.
Qed.
Hint Resolve tnat_in_uni : slow.

Hint Rewrite @mkcv_apply_substc : slow.

Lemma substc_mkcv_choice_seq {o} :
  forall v name (t : @CTerm o),
    (mkcv_choice_seq [v] name) [[v \\ t]] = mkc_choice_seq name.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; unfsubst.
Qed.
Hint Rewrite @substc_mkcv_choice_seq : slow.

Definition choice_sequence_name_and_seq2choice_seq_entry {o} (name : choice_sequence_name) (l : list nat) : @ChoiceSeqEntry o :=
  MkChoiceSeqEntry
    _
    (map mkc_nat l)
    (choice_sequence_name2restriction name).

Definition choice_sequence_name_and_seq2entry {o} (name : choice_sequence_name) (l : list nat) : @library_entry o :=
  lib_cs name (choice_sequence_name_and_seq2choice_seq_entry name l).

Lemma entry_extends_choice_sequence_name2entry {o} :
  forall (entry : @library_entry o) name,
    safe_library_entry entry
    -> csn_kind name = cs_kind_seq []
    -> entry_extends entry (choice_sequence_name2entry name)
    -> exists l restr,
        entry = lib_cs name (MkChoiceSeqEntry _ (map mkc_nat l) restr)
        /\ same_restrictions restr (csc_seq []).
Proof.
  introv safe ck ext.
  inversion ext; subst; tcsp; clear ext.

  { exists ([] : list nat) (@choice_sequence_name2restriction o name); dands; tcsp.
    destruct name as [name kind]; simpl in *; repnd; subst; simpl in *; tcsp. }

  unfold choice_sequence_name2restriction in *.
  destruct name as [name kind]; simpl in *; subst.
  simpl in *; tcsp; ginv; repnd.
  unfold correct_restriction in *; simpl in *; repnd.

  assert (forall v, LIn v vals' -> exists (i : nat), v = mkc_nat i) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe n v) as q.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    apply safe0 in q; auto; try omega.
  }
  clear safe.

  assert (exists l, vals' = map mkc_nat l) as h.
  {
    induction vals'; simpl in *; tcsp.
    - exists ([] : list nat); simpl; auto.
    - autodimp IHvals' hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (i :: l); simpl; auto.
  }

  exrepnd; subst.
  exists l (@csc_seq o []); dands; auto; eauto 3 with slow.
Qed.

Lemma map_mkc_nat_ntimes {o} :
  forall n k,
    map mkc_nat (ntimes n k)
    = ntimes n (@mkc_nat o k).
Proof.
  induction n; introv; simpl; auto.
  allrw; simpl; auto.
Qed.

Lemma entry_in_inf_library_extends_const {o} :
  forall n (entry : @library_entry o) d,
    entry_in_inf_library_extends entry n (fun _ => d) -> inf_entry_extends d entry.
Proof.
  induction n; introv i; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_inf_library_extends_const : slow.

(*Lemma matching_entries_preserves_inf_matching_entries_library_entry2inf {o} :
  forall (e1 e2 : @library_entry o) e,
    matching_entries e1 e2
    -> inf_entry_extends (library_entry2inf e2) e
    -> inf_matching_entries (library_entry2inf e1) e.
Proof.
  introv m i.
  unfold inf_entry_extends in i.
  unfold matching_entries in m.
  destruct e1, e2, e; simpl in *; repnd; subst; tcsp.
Qed.
Hint Resolve matching_entries_preserves_inf_matching_entries_library_entry2inf : slow.*)

(*Lemma entry_in_inf_library_extends_library2inf_implies {o} :
  forall n entry d (lib : @library o),
    entry_in_inf_library_extends entry n (library2inf lib d)
    -> inf_entry_extends d entry
       \/ exists e, entry_in_library e lib /\ inf_entry_extends (library_entry2inf e) entry.
Proof.
  induction n; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  { unfold library2inf in *; simpl in *.
    destruct lib; simpl; tcsp.
    right; exists l; tcsp. }

  destruct lib; simpl in *; autorewrite with slow in *.

  { unfold shift_inf_lib, library2inf in i; simpl in i.
    apply entry_in_inf_library_extends_const in i; tcsp. }

  unfold library2inf in i0; simpl in i0.
  apply IHn in i; clear IHn.

  repndors; exrepnd; subst; tcsp.
  right; exists e; dands; tcsp.
  right; dands; auto.
  introv m; apply matching_entries_sym in m; destruct i0; eauto 2 with slow.
Qed.*)

Lemma inf_entry_extends_lib_cs_implies_matching {o} :
  forall (e : @inf_library_entry o) name x,
    inf_entry_extends e (lib_cs name x) -> entry_name_cs name = inf_entry2name e.
Proof.
  introv h.
  destruct e; simpl in *; repnd; subst; tcsp.
Qed.

(*Lemma inf_entry2name_library_entry2inf {o} :
  forall (e : @library_entry o),
    inf_entry2name (library_entry2inf e)
    = entry2name e.
Proof.
  introv; destruct e; simpl; auto.
Qed.
Hint Rewrite @inf_entry2name_library_entry2inf : slow.*)

Lemma two_entries_in_library_with_same_name {o} :
  forall (e1 e2 : @library_entry o) name lib,
    entry2name e1 = entry_name_cs name
    -> entry2name e2 = entry_name_cs name
    -> entry_in_library e1 lib
    -> entry_in_library e2 lib
    -> e1 = e2.
Proof.
  induction lib; introv eqname1 eqname2 h q; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  - destruct h0.
    unfold matching_entries.
    rewrite eqname1, eqname2; simpl; auto.

  - destruct q0.
    unfold matching_entries.
    rewrite eqname1, eqname2; simpl; auto.
Qed.

Lemma implies_list_eq_ntimes :
  forall {A} l (x : A),
    (forall v, LIn v l -> v = x)
    -> l = ntimes (length l) x.
Proof.
  induction l; introv h; simpl in *; tcsp.
  erewrite IHl; eauto.
  pose proof (h a) as q; autodimp q hyp; subst.
  autorewrite with slow; auto.
Qed.
Hint Resolve implies_list_eq_ntimes : slow.

(*Lemma entry_extends_choice_sequence_name2entry_implies {o} :
  forall (lib : @library o) name name0 lib' entry',
    name <> name0
    -> safe_library_entry entry'
    -> csn_kind name = cs_kind_seq []
    -> inf_lib_extends (library2inf lib (simple_inf_choice_seq name0)) lib'
    -> entry_in_library (choice_sequence_name2entry name) lib
    -> entry_in_library entry' lib'
    -> entry_extends entry' (choice_sequence_name2entry name)
    -> exists restr n,
        entry' = lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)
        /\ same_restrictions restr (csc_seq []).
Proof.
  introv dname safe ck iext ilib ilib' ext.
  apply entry_extends_choice_sequence_name2entry in ext; auto; exrepnd; subst.
  simpl in *; repnd.
  exists restr.

  assert (exists n, l = ntimes n 0) as h;
    [|exrepnd; subst; exists n; dands; auto;
      rewrite map_mkc_nat_ntimes; rewrite mkc_zero_eq; auto];[].

  applydup iext in ilib'.
  repndors; simpl in *.

  - exrepnd.
    apply entry_in_inf_library_extends_library2inf_implies in ilib'1; simpl in *.
    repndors; exrepnd; subst; tcsp;[].
    applydup @inf_entry_extends_lib_cs_implies_matching in ilib'0; simpl in *.
    autorewrite with slow in *.

    dup ilib'1 as m.
    eapply two_entries_in_library_with_same_name in m; try exact ilib; simpl; eauto.
    subst e; simpl in *; repnd; GC.
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
    unfold inf_choice_sequence_vals_extend in *; simpl in *.
    unfold choice_seq_vals2inf in *; simpl in *.
    unfold restriction2default in *.
    unfold choice_sequence_name2restriction in ilib'0.
    rewrite ck in *; simpl in *.
    unfold natSeq2default in *; simpl in *.

    assert (forall v, LIn v l -> v = 0) as h.
    {
      introv q.
      apply in_nth in q; exrepnd.
      pose proof (ilib'0 n0 (mkc_nat v)) as q.
      rewrite select_map in q.
      autodimp q hyp.
      { erewrite nth_select1; auto; unfold option_map; rewrite q0 at 1; eauto. }
      autorewrite with slow in q; apply some_inj in q.
      rewrite mkc_zero_eq in q.
      apply mkc_nat_eq_implies in q; auto.
    }

    clear ilib'0 ilib'.
    exists (length l); eauto 3 with slow.

  - unfold entry_in_inf_library_default in ilib'0; simpl in *; repnd; GC.
    unfold correct_restriction in *.
    rewrite ck in *; simpl in *.

    unfold is_default_choice_sequence in *.
    destruct restr; simpl in *; repnd; tcsp.
    exists (length l).
    apply implies_list_eq_ntimes.
    introv i.
    apply in_nth in i; exrepnd.
    pose proof (ilib'0 n (mkc_nat v)) as q.
    rewrite select_map in q.
    autodimp q hyp.
    { erewrite nth_select1; auto; unfold option_map; rewrite i0 at 1; eauto. }
    rewrite safe2 in q; try omega.
    rewrite mkc_zero_eq in q.
    apply mkc_nat_eq_implies in q; auto.
Qed.*)

Lemma select_ntimes :
  forall {A} n m (a : A),
    select n (ntimes m a)
    = if lt_dec n m then Some a else None.
Proof.
  induction n; introv; simpl.

  - destruct m; simpl; auto.

  - destruct m; simpl; auto.
    rewrite IHn.
    boolvar; try omega; tcsp.
Qed.

Hint Rewrite minus_plus : slow nat.

Lemma is_nat_seq_restriction_implies_same_restrictions {o} :
  forall l (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l restr
    -> same_restrictions restr (csc_seq l).
Proof.
  introv h.
  destruct restr; simpl in *; tcsp; repnd; dands; tcsp.

  { introv.
    destruct (lt_dec n (length l)) as [x|x].
    { rewrite h0; auto.
      rewrite natSeq2restrictionPred_iff_cterm_is_nth; tcsp. }
    { rewrite h; try omega.
      rewrite natSeq2restrictionPred_iff_is_nat; tcsp; try omega. } }
Qed.
Hint Resolve is_nat_seq_restriction_implies_same_restrictions : slow.

Lemma entry_extends_cs_zeros {o} :
  forall (entry : @library_entry o) name n restr,
    safe_library_entry entry
    -> csn_kind name = cs_kind_seq []
    -> entry_extends entry (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr))
    -> exists l restr,
        entry = lib_cs name (MkChoiceSeqEntry _ (map mkc_nat l) restr)
        /\ same_restrictions restr (csc_seq []).
Proof.
  introv safe ck ext.
  inversion ext; subst; tcsp; clear ext.

  { exists (ntimes n 0) restr; dands; tcsp.
    { rewrite map_mkc_nat_ntimes; rewrite <- mkc_zero_eq; auto. }
    destruct name as [name kind]; simpl in *; repnd; subst; simpl in *; tcsp.
    unfold correct_restriction in *; simpl in *; eauto 3 with slow. }

  destruct name; simpl in *; subst.
  unfold correct_restriction in *; simpl in *.
  unfold is_nat_seq_restriction in *.
  destruct restr; simpl in *; tcsp; ginv; repnd.

  assert (forall v, LIn v vals' -> exists (i : nat), v = mkc_nat i) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe (n + n0) v) as q.
    rewrite select_app_r in q; autorewrite with slow nat in *; try omega.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    apply safe0 in q; auto; try omega.
  }
  clear safe.

  assert (exists l, vals' = map mkc_nat l) as h.
  {
    induction vals'; simpl in *; tcsp.
    - exists ([] : list nat); simpl; auto.
    - autodimp IHvals' hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (i :: l); simpl; auto.
  }

  exrepnd; subst.
  exists (ntimes n 0 ++ l) (csc_type typ); dands; auto.

  {
    rewrite map_app.
    rewrite map_mkc_nat_ntimes.
    rewrite mkc_zero_eq; auto.
  }

  unfold same_restrictions; simpl; dands; auto.
  { introv; rewrite safe0; try omega.
    unfold natSeq2restrictionPred; autorewrite with slow; tcsp. }
Qed.

(*Lemma entry_extends_cs_zeros_implies {o} :
  forall (lib : @library o) name name0 n restr lib' entry',
    name <> name0
    -> safe_library_entry entry'
    -> csn_kind name = cs_kind_seq []
    -> inf_lib_extends (library2inf lib (simple_inf_choice_seq name0)) lib'
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library entry' lib'
    -> entry_extends entry' (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr))
    -> exists restr n,
        entry' = lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)
        /\ same_restrictions restr (csc_seq []).
Proof.
  introv dname safe ck iext ilib srestr ilib' ext.
  apply entry_extends_cs_zeros in ext; exrepnd; subst; auto;[].
  simpl in *; repnd.
  exists restr0.

  assert (exists n, l = ntimes n 0) as h;
    [|exrepnd; subst; exists n0; dands; auto;
      rewrite map_mkc_nat_ntimes; rewrite mkc_zero_eq; auto].

  applydup iext in ilib'.
  repndors; simpl in *.

  - exrepnd.
    apply entry_in_inf_library_extends_library2inf_implies in ilib'1; simpl in *.
    repndors; exrepnd; subst; tcsp;[].
    applydup @inf_entry_extends_lib_cs_implies_matching in ilib'0; simpl in *.
    autorewrite with slow in *.

    dup ilib'1 as m.
    eapply two_entries_in_library_with_same_name in m; try exact ilib; simpl; eauto;[].
    subst e; simpl in *; repnd; GC.
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
    unfold inf_choice_sequence_vals_extend in *; simpl in *.
    unfold choice_seq_vals2inf in *; simpl in *.
    unfold restriction2default in *.
    unfold same_restrictions in srestr.
    destruct restr; simpl in *; repnd; tcsp.

    assert (forall v, LIn v l -> v = 0) as h.
    {
      introv q.
      apply in_nth in q; exrepnd.
      pose proof (ilib'0 n0 (mkc_nat v)) as q.
      rewrite select_map in q.
      autodimp q hyp.
      { erewrite nth_select1; auto; unfold option_map; rewrite q0 at 1; eauto. }
      autorewrite with slow in q.
      rewrite select_ntimes in q; boolvar; try (apply some_inj in q).

      { rewrite mkc_zero_eq in q.
        apply mkc_nat_eq_implies in q; auto. }

      { rewrite srestr0 in q; unfold natSeq2default in q; autorewrite with slow in q.
        rewrite mkc_zero_eq in q.
        apply mkc_nat_eq_implies in q; auto. }
    }

    clear ilib'0 ilib'.
    exists (length l); eauto 3 with slow.

  - unfold entry_in_inf_library_default in ilib'0; simpl in *; repnd; GC.
    unfold correct_restriction in *.
    rewrite ck in *; simpl in *.

    unfold is_default_choice_sequence in *.
    destruct restr0; simpl in *; repnd; tcsp.
    exists (length l).
    apply implies_list_eq_ntimes.
    introv i.
    apply in_nth in i; exrepnd.
    pose proof (ilib'0 n0 (mkc_nat v)) as q.
    rewrite select_map in q.
    autodimp q hyp.
    { erewrite nth_select1; auto; unfold option_map; rewrite i0 at 1; eauto. }
    rewrite safe2 in q; try omega.
    rewrite mkc_zero_eq in q.
    apply mkc_nat_eq_implies in q; auto.
Qed.*)

Lemma iscvalue_mkc_one {o} :
  @iscvalue o mkc_one.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_one : slow.

Lemma mk_nat_eq_implies {o} :
  forall n m, @mk_nat o n = mk_nat m -> n = m.
Proof.
  introv h.
  inversion h as [q].
  apply Znat.Nat2Z.inj in q; auto.
Qed.

Lemma computes_to_valc_apply_choice_seq_implies_find_cs_value_at_some {o} :
  forall lib name (a : @CTerm o) n v,
    computes_to_valc lib (mkc_eapply (mkc_choice_seq name) a) v
    -> computes_to_valc lib a (mkc_nat n)
    -> exists val, find_cs_value_at lib name n = Some val.
Proof.
  introv comp ca.
  destruct_cterms; simpl in *.
  unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in comp; repnd.
  unfold reduces_to in *; exrepnd.
  pose proof (reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue_like lib name x k x0) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  repndors; exrepnd; simpl in *; tcsp.

  {
    apply reduces_in_atmost_k_steps_implies_computes_to_value in q2; eauto 3 with slow.
    eapply computes_to_value_eq in q2; try exact ca.
    apply mk_nat_eq_implies in q2; subst.
    exists val; auto.
  }

  {
    apply isvalue_implies in comp; repnd.
    apply iscan_implies in comp0; exrepnd; subst; simpl in *; tcsp.
  }
Qed.

Lemma computes_to_valc_apply_choice_seq_implies_eapply {o} :
  forall lib name (a v : @CTerm o),
    computes_to_valc lib (mkc_apply (mkc_choice_seq name) a) v
    -> computes_to_valc lib (mkc_eapply (mkc_choice_seq name) a) v.
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in *; repnd; dands; auto.
  apply reduces_to_split2 in comp0; repndors; subst; simpl in *; tcsp.

  { inversion comp; subst; simpl in *; tcsp. }

  exrepnd.
  csunf comp0; simpl in comp0; ginv; auto.
Qed.
Hint Resolve computes_to_valc_apply_choice_seq_implies_eapply : slow.

Lemma ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc {o} :
  forall lib (a : @CTerm o) k,
    a ===>(lib) (mkc_nat k)
    -> ccomputes_to_valc lib a (mkc_nat k).
Proof.
  introv comp.
  pose proof (comp _ (lib_extends_refl _)) as comp; simpl in comp; exrepnd; spcast.
  apply choiceseq.cequivc_nat_implies_computes_to_valc in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 2 with slow; subst; auto.
Qed.
Hint Resolve ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc : slow.

Lemma entry_extends_preserves_matching_entries_right {o} :
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry1 entry2
    -> matching_entries entry entry1
    -> matching_entries entry entry2.
Proof.
  introv h q.
  inversion h; subst; tcsp.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_right : slow.

Lemma entry_extends_preserves_matching_entries_right_rev {o} :
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry2 entry1
    -> matching_entries entry entry1
    -> matching_entries entry entry2.
Proof.
  introv h q.
  inversion h; subst; tcsp.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_right_rev : slow.

Lemma is_nat_one {o} : forall n, @is_nat o n mkc_one.
Proof.
  introv.
  exists 1.
  apply cterm_eq; simpl; auto.
Qed.
Hint Resolve is_nat_one : slow.

Lemma safe_library_entry_zeros_one {o} :
  forall name n (restr : @ChoiceSeqRestriction o),
    csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> safe_library_entry (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero ++ [mkc_one]) restr)).
Proof.
  introv ck srestr.
  unfold safe_library_entry; simpl; dands; auto.

  {
    unfold correct_restriction.
    allrw; eauto 3 with slow.
    unfold is_nat_seq_restriction.
    unfold same_restrictions in *.
    destruct restr; simpl in *; repnd; tcsp.
    dands; tcsp.
    { introv h.
      rewrite srestr.
      unfold natSeq2restrictionPred; autorewrite with slow; tcsp. }
  }

  {
    unfold choice_sequence_satisfies_restriction.
    unfold same_restrictions in *.
    destruct restr; simpl in *; repnd; tcsp.
    introv h.
    apply srestr.
    unfold natSeq2restrictionPred; autorewrite with slow.
    destruct (lt_dec n0 n) as [xx|xx].

    - rewrite select_app_l in h; autorewrite with slow; auto.
      rewrite select_ntimes in h; boolvar; tcsp; try omega; ginv; eauto 3 with slow.

    - rewrite select_app_r in h; autorewrite with slow in *; auto; try omega.
      destruct (n0 - n); simpl in *; ginv; eauto 3 with slow.
      autorewrite with slow in *; ginv.
  }
Qed.
Hint Resolve safe_library_entry_zeros_one : slow.

Lemma entry_zeros_one_extends {o} :
  forall name n (restr : @ChoiceSeqRestriction o),
    entry_extends
      (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero ++ [mkc_one]) restr))
      (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)).
Proof.
  introv; eauto.
Qed.
Hint Resolve entry_zeros_one_extends : slow.

Lemma lib_equal_names_preserves_shadowed_entry {o} :
  forall e (lib lib1 : @plibrary o),
    map entry2name lib = map entry2name lib1
    -> shadowed_entry e lib
    -> shadowed_entry e lib1.
Proof.
  induction lib; introv eqn sh; simpl in *; destruct lib1; simpl in *; ginv.
  apply cons_inj in eqn; repnd.
  unfold shadowed_entry in *; simpl in *.
  allrw @andb_false_iff.
  repndors; tcsp.
  left.
  unfold diff_entry_names in *.
  rewrite eqn0 in *; auto.
Qed.

(*Lemma implies_lib_extends_snoc_lr_same_names {o} :
  forall (lib lib1 : @library o) (e : library_entry),
    map entry2name lib = map entry2name lib1
    -> lib_extends lib lib1
    -> lib_extends (snoc lib e) (snoc lib1 e).
Proof.
  introv eqn ext.
  remember (forallb (diff_entry_names e) lib) as b; symmetry in Heqb.
  destruct b.

  - apply implies_lib_extends_snoc_lr_if_all_diff; auto.

  - apply lib_extends_snoc_lr_if_all_diff_false; auto.
    eapply lib_equal_names_preserves_shadowed_entry; eauto.
Qed.*)

Lemma entry_extends_implies_same_entry2name {o} :
  forall (e1 e2 : @library_entry o),
    entry_extends e2 e1
    -> entry2name e2 = entry2name e1.
Proof.
  introv ext.
  inversion ext; subst; tcsp.
Qed.

Lemma entry_extends_preserves_non_shadowed_entry {o} :
  forall (e1 e2 : @library_entry o) lib,
    entry_extends e2 e1
    -> non_shadowed_entry e1 lib
    -> non_shadowed_entry e2 lib.
Proof.
  introv ext sh.
  unfold non_shadowed_entry in *.
  apply entry_extends_implies_same_entry2name in ext.
  rewrite forallb_forall in *; introv h.
  apply sh in h.
  unfold diff_entry_names in *.
  rewrite ext in *; auto.
Qed.
Hint Resolve entry_extends_preserves_non_shadowed_entry : slow.

(*Lemma implies_lib_extends_snoc {o} :
  forall e1 e2 (lib : @library o),
    safe_library_entry e2
    -> entry_extends e2 e1
    -> lib_extends (snoc lib e2) (snoc lib e1).
Proof.
  introv safee ext.
  split.

  - introv i; simpl in *.
    apply entry_in_library_snoc_implies in i.
    repndors; repnd; subst; tcsp.

    { apply implies_entry_in_library_extends_snoc; eauto 3 with slow. }

    eapply entry_extends_preserves_entry_in_library_extends; eauto.
    apply implies_entry_in_library_extends_tail_if_all_diff; eauto 3 with slow.

  - introv safe h.
    unfold safe_library in *; simpl in *.
    apply entry_in_library_snoc_implies in h.
    repndors; repnd; subst; tcsp.
    apply safe.
    apply implies_entry_in_library_snoc; eauto 3 with slow.

  - introv h; simpl in .
    apply list_in_snoc in h.
    repndors; subst; tcsp.

    + exists entry1; dands; tcsp; eauto 3 with slow.
      apply list_in_snoc; tcsp.

    + exists e2; dands; tcsp.
      apply list_in_snoc; tcsp.
Qed.*)

Lemma in_lib_nil {o} :
  forall n, @in_lib o n [] <-> False.
Proof.
  introv; split; intro h; tcsp.
  unfold in_lib in *; simpl in *; exrepnd; tcsp.
Qed.
Hint Rewrite @in_lib_nil : slow.

Lemma in_lib_cons {o} :
  forall n e (lib : @plibrary o),
    in_lib n (e :: lib) <-> (same_entry_name n (entry2name e) \/ in_lib n lib).
Proof.
  introv; unfold in_lib; split; intro h; repndors; exrepnd; simpl in *; repndors; subst; tcsp;
    try (complete (eexists; dands; eauto)); try (complete (right; eauto)).
Qed.

Lemma entry_in_library_split {o} :
  forall e (lib : @plibrary o),
    entry_in_library e lib
    -> exists lib1 lib2,
      lib = lib1 ++ e :: lib2
      /\ ~in_lib (entry2name e) lib1.
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst; tcsp.
  { exists ([] : @plibrary o) lib; simpl; autorewrite with slow; dands; tcsp. }
  autodimp IHlib hyp; exrepnd; subst.
  exists (a :: lib1) lib2; simpl; dands; tcsp.
  rewrite in_lib_cons; intro xx; repndors; tcsp.
Qed.

Definition add_mid_entry {o} (lib1 : library) (e : @library_entry o) (lib2 : library) : library :=
  MkLib (lib_pre lib1 ++ e :: lib_pre lib2) (lib_cond lib2).

Lemma add_one_choice_if_not_in_left {o} :
  forall (liba libb : @library o) name a vals r,
    !in_lib (entry_name_cs name) liba
    -> add_one_choice name a (add_mid_entry liba (lib_cs name (MkChoiceSeqEntry _ vals r)) libb)
       = Some (length vals, r, add_mid_entry liba (lib_cs name (MkChoiceSeqEntry _ (snoc vals a) r)) libb).
Proof.
  introv ni.
  unfold add_one_choice; simpl.
  rewrite add_choice_if_not_in_left; auto.
Qed.

Lemma add_one_choice_if_not_in_left0 {o} :
  forall cond (liba libb : @plibrary o) name a vals r,
    !in_lib (entry_name_cs name) liba
    -> add_one_choice name a (MkLib (liba ++ lib_cs name (MkChoiceSeqEntry _ vals r) :: libb) cond)
       = Some (length vals, r, MkLib (liba ++ lib_cs name (MkChoiceSeqEntry _ (snoc vals a) r) :: libb) cond).
Proof.
  introv ni.
  unfold add_one_choice; simpl.
  rewrite add_choice_if_not_in_left; auto.
Qed.

Definition sat_cond_vals_cs_entry {o} (c : @LibCond o) (e : ChoiceSeqEntry) :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    sat_cond_choices c vals
  end.

Definition sat_cond_vals_entry {o} (c : @LibCond o) (e : library_entry) :=
  match e with
  | lib_cs name e => sat_cond_vals_cs_entry c e
  | lib_abs op vars rhs cor => c (soterm2nterm rhs)
  end.

Definition lib_cond_sat_vals_cs_entry {o} (lib : @library o) (e : ChoiceSeqEntry) :=
  match e with
  | MkChoiceSeqEntry _ vals restr => lib_cond_sat_choices lib vals
  end.

Definition lib_cond_sat_vals_entry {o} (lib : @library o) (e : library_entry) :=
  match e with
  | lib_cs name e => lib_cond_sat_vals_cs_entry lib e
  | lib_abs op vars rhs cor => sat_cond_soterm lib rhs
  end.

Lemma lib_extends_middle {o} :
  forall (lib1 lib2 : @library o) (e1 e2 : library_entry),
    safe_library_entry e2
    -> lib_cond_sat_vals_entry lib2 e2
    -> entry_extends e2 e1
    -> !in_lib (entry2name e1) lib1
    -> lib_extends (add_mid_entry lib1 e2 lib2) (add_mid_entry lib1 e1 lib2).
Proof.
  introv safe sat ext ni.
  inversion ext; subst; clear ext; tcsp.
  simpl in *; repnd.
  induction vals' using rev_list_ind; autorewrite with slow in *; eauto.
  rewrite snoc_append_l in safe.
  rewrite snoc_append_l in sat.
  repeat (autodimp IHvals' hyp); eauto 3 with slow.
  { introv i; apply sat; allrw in_snoc; tcsp. }
  eapply lib_extends_trans;[|eauto].
  clear IHvals'.
  destruct restr; simpl in *.

  { apply (lib_extends_cs _ name a (length (vals ++ vals')) typ); auto.
    { rewrite add_one_choice_if_not_in_left; tcsp.
      rewrite snoc_append_l; auto. }
    { apply safe.
      rewrite select_snoc_eq; boolvar; tcsp; try omega. }
    { simpl; apply sat; apply in_snoc; tcsp. } }

(*
  { apply (lib_extends_law _ name a (length (vals ++ vals')) f); auto.
    { rewrite add_choice_if_not_in_left; tcsp.
      rewrite snoc_append_l; auto. }
    pose proof (safe (length (vals ++ vals'))) as safe; autorewrite with slow in *.
    autodimp safe hyp.
    rewrite select_snoc_eq in safe; boolvar; try omega; ginv.
    inversion safe; auto. }

  { apply (lib_extends_res _ name a (length (vals ++ vals')) typ); auto.
    { rewrite add_choice_if_not_in_left; tcsp.
      rewrite snoc_append_l; auto. }
    apply safe.
    rewrite select_snoc_eq; boolvar; tcsp; try omega. }*)
Qed.

Lemma lib_extends_middle0 {o} :
  forall cond (lib1 lib2 : @plibrary o) (e1 e2 : library_entry),
    safe_library_entry e2
    -> sat_cond_vals_entry cond e2
    -> entry_extends e2 e1
    -> !in_lib (entry2name e1) lib1
    -> lib_extends (MkLib (lib1 ++ e2 :: lib2) cond) (MkLib (lib1 ++ e1 :: lib2) cond).
Proof.
  introv safe sat ext ni.
  apply (lib_extends_middle (MkLib lib1 cond) (MkLib lib2 cond)); simpl; auto.
Qed.

Lemma in_ntimes :
  forall {A} (a : A) n v,
    LIn a (ntimes n v) -> a = v.
Proof.
  induction n; introv i; simpl in *; tcsp.
Qed.

Definition lib_names {o} (lib : @plibrary o) : list EntryName := map entry2name lib.

Lemma entry_cs_zeros_implies_exists_extension_with_one {o} :
  forall (lib : @library o) name n restr,
    lib_cond_sat_def lib
    -> sat_cond_restr lib restr
    -> csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> exists (lib' : library),
        lib_names lib' = lib_names lib
        /\ lib_extends lib' lib
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero ++ [mkc_one]) restr)) lib'.
Proof.
  introv def sat ckind same i.
  apply entry_in_library_split in i; exrepnd.
  destruct lib as [lib cond]; simpl in *; subst; simpl in *.
  exists (add_mid_entry (MkLib lib1 cond) (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero ++ [mkc_one]) restr)) (MkLib lib2 cond)); simpl.
  dands; tcsp.

  { unfold lib_names; simpl; repeat (rewrite map_app; simpl); tcsp. }

  { apply lib_extends_middle; simpl; auto.

    { dands; eauto 3 with slow.
      { destruct restr; simpl in *; repnd; tcsp.
        destruct name as [name kind]; simpl in *; subst; simpl in *; tcsp.
        unfold correct_restriction; simpl; dands; tcsp.
        { introv len.
          pose proof (same n0) as same; unfold natSeq2restrictionPred in *; autorewrite with slow in *; auto. } }
      { unfold choice_sequence_satisfies_restriction; destruct restr; simpl in *; tcsp.
        introv sel; repnd.
        apply same; unfold natSeq2restrictionPred; autorewrite with slow.
        destruct (lt_dec n0 n) as [xx|xx].
        { rewrite select_app_l in sel; autorewrite with slow; auto.
          rewrite select_ntimes in sel; boolvar; ginv; eauto 3 with slow. }
        rewrite select_app_r in sel; autorewrite with slow in *; auto; try omega.
        remember (n0 - n) as k; clear Heqk; destruct k; simpl in *; ginv; eauto 3 with slow.
        autorewrite with slow in *; ginv. } }

    dands; tcsp.
    introv i; apply in_app_iff in i; simpl in *; repndors; subst; tcsp; try apply def.
    apply in_ntimes in i; subst; apply def. }

  apply implies_entry_in_library_app_right; simpl; tcsp.
  introv i m; simpl in *.
  unfold matching_entries in m; simpl in *.
  destruct i1; unfold in_lib.
  exists e'; dands; tcsp; apply LIn_implies_In; auto.
Qed.

Hint Resolve nat_in_nat : slow.

Lemma not_in_ext_not_inhabited_exists_1_choice {o} :
  forall (lib : @library o) name v n restr,
    lib_cond_sat_def lib
    -> sat_cond_restr lib restr
    -> csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> safe_library lib
    -> in_ext lib (fun lib => !inhabited_type lib (exists_1_choice name v))
    -> False.
Proof.
  introv sat satr ck srestr ilib safe inh.
  pose proof (entry_cs_zeros_implies_exists_extension_with_one lib name n restr) as q.
  repeat (autodimp q hyp); exrepnd.
  pose proof (inh _ q2) as inh; simpl in inh; destruct inh.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  assert (sat_cond_restr lib' restr) as satr' by eauto 3 with slow.

  clear lib ilib safe sat satr q1 q2.
  rename lib' into lib.
  rename safe' into safe.
  rename sat' into sat.
  rename satr' into satr.

  apply inhabited_exists; dands; eauto 3 with slow.

  {
    introv ext ea.
    autorewrite with slow.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.

    - apply equality_int_nat_implies_cequivc in ea.
      apply ccequivc_ext_bar_iff_ccequivc_bar in ea.
      eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.
      right.
      apply implies_ccequivc_ext_apply; eauto 3 with slow.

    - apply in_ext_implies_all_in_ex_bar; introv ext'; right; eauto 3 with slow.
  }

  exists (@mkc_pair o (mkc_nat n) mkc_axiom).
  apply in_ext_implies_all_in_ex_bar; introv ext.
  exists (@mkc_nat o n) (@mkc_axiom o).
  dands; spcast; eauto 3 with slow;[].
  autorewrite with slow.
  apply member_equality.
  apply equality_in_tnat.
  apply in_ext_implies_in_open_bar.
  introv ext'.

  assert (lib_extends lib'0 lib) as ext0 by eauto 3 with slow.
  clear lib' ext ext'.
  rename lib'0 into lib'.
  exists 1.
  rw <- @mkc_one_eq.
  dands; spcast; eauto 3 with slow.

  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto; eauto 3 with slow.
  rewrite select_app_r; autorewrite with slow; try omega.
  simpl; auto.
Qed.

Lemma one_in_nat {o} :
  forall (lib : @library o), equality lib mkc_one mkc_one mkc_tnat.
Proof.
  introv.
  allrw @mkc_one_eq; eauto 3 with slow.
Qed.
Hint Resolve one_in_nat : slow.

(*Lemma not_exists_1_choice {o} :
  forall (lib : @library o) name v n restr,
    csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> safe_library lib
    -> inhabited_type lib (exists_1_choice name v)
    -> False.
Proof.
  introv ck srestr ilib safe inh.
  unfold exists_1_choice in inh.
  apply inhabited_exists in inh; exrepnd.
  clear inh0 inh1.
  rename inh2 into inh.

  dup inh as iob.

  pose proof (inh _ (lib_extends_refl _)) as inh; exrepnd.
  pose proof (inh1 _ (lib_extends_refl _)) as inh1; cbv beta in inh1.
  applydup xt in ilib.
  apply entry_in_library_extends_implies_entry_in_library in ilib0; exrepnd.
  apply entry_extends_cs_zeros in ilib1; eauto 3 with slow;[]; exrepnd.
  subst.
  autorewrite with slow in *.

  eapply lib_extends_preserves_in_open_bar in iob; eauto.

  assert (safe_library lib'') as safe'' by eauto 3 with slow.
  clear dependent lib.
  clear dependent restr.
  rename lib'' into lib.
  rename restr0 into restr.

  apply member_tnat_iff in inh2.
  apply equality_in_mkc_equality in inh1; repnd; GC.
  clear inh4.
  apply equality_in_tnat in inh3.
  apply e_all_in_ex_bar_as in inh3.
  unfold equality_of_nat in inh3.

  apply (in_open_bar_const lib).
  eapply in_open_bar_comb; try exact inh3; clear inh3.
  eapply in_open_bar_pres; try exact inh2; clear inh2; introv ext inh2 inh3.
  exrepnd.

(*
  unfold all_in_ex_bar in *; exrepnd.
  apply (implies_all_in_bar_intersect_bars_left _ bar) in inh3.
  apply (implies_all_in_bar_intersect_bars_right _ bar0) in inh0.
  remember (intersect_bars bar0 bar) as bar1.
  clear bar0 bar Heqbar1.
  rename bar1 into bar.

  assert (exists n restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.
    applydup q2 in blib0.

    apply entry_in_library_extends_implies_entry_in_library in blib1; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in blib0.
      rewrite blib0 in *; ginv. }

    pose proof (entry_extends_cs_zeros_implies lib name name0 n restr lib' entry') as q.
    repeat (autodimp q hyp).
    exrepnd; subst.
    exists n0 restr0 lib'; dands; auto.
  }

  clear n restr blib3 blib0.
  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (inh0 _ blib2 _ (lib_extends_refl lib')) as inh0.
  pose proof (inh3 _ blib2 _ (lib_extends_refl lib')) as inh3.
  cbv beta in inh0, inh3.

  clear lib bar safe blib1 blib2 inh1.
  rename lib' into lib.
  rename safe' into safe.
  exrepnd; spcast.

  rw @mkc_one_eq in inh1; repeat (rw @mkc_nat_eq in inh1).
  ccomputes_to_valc_ext_val.
  apply Nat2Z.inj in inh1; subst.

  applydup @ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc in inh2; spcast.
  applydup @ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc in inh0; spcast.

  pose proof (implies_compute_to_valc_apply_choice_seq lib a name k0 mkc_zero) as q.
  repeat (autodimp q hyp); eauto 3 with slow; try computes_to_eqval;[].

  pose proof (computes_to_valc_apply_choice_seq_implies_find_cs_value_at_some lib name a k0 mkc_one) as w.
  repeat (autodimp w hyp); eauto 3 with slow;[]; exrepnd.

  apply entry_in_library_implies_find_cs_some in blib0.
  unfold find_cs_value_at in *.
  rewrite blib0 in *.
  simpl in *.
  rewrite find_value_of_cs_at_vals_as_select.
  rewrite find_value_of_cs_at_vals_as_select in w0.
  rewrite select_ntimes in *.
  boolvar; tcsp.
*)
Abort.
*)

Lemma implies_lib_extends_cons {o} :
  forall e1 e2 (lib : @library o),
    safe_library_entry e2
    -> lib_cond_sat_vals_entry lib e2
    -> entry_extends e2 e1
    -> lib_extends (add_one_entry e2 lib) (add_one_entry e1 lib).
Proof.
  introv safee sat ext.
  pose proof (lib_extends_middle (MkLib [] defLC) lib e1 e2) as q; simpl in *; apply q; auto.
  intro xx; autorewrite with slow in *; tcsp.
Qed.

(*
Lemma implies_lib_extends_cons2 {o} :
  forall e (lib2 lib1 : @library o),
    safe_library lib1
    -> lib_extends lib2 lib1
    -> lib_extends (e :: lib2) (e :: lib1).
Proof.
  introv sf1 ext.
  split.

  - introv i; simpl in *; repndors; repnd; subst; tcsp.
    { left; eauto 3 with slow. }
    right; dands; eauto 3 with slow.
    apply ext in i; auto.

  - introv safe h.
    unfold safe_library in *; simpl in *.
    repndors; subst; tcsp.
    repnd; tcsp.
    destruct ext as [ext1 safe1 ss1].
    apply safe1;auto.

  - introv h; simpl in *; repndors; subst; tcsp.

    + exists entry1; dands; tcsp; eauto 3 with slow.

    + apply ext in h; exrepnd.
      exists entry2; dands; tcsp.
Qed.
*)


Lemma implies_sat_lib_cond_add_new_abs {o} :
  forall op vars rhs correct (lib : @library o),
    sat_cond_soterm lib rhs
    -> sat_lib_cond lib
    -> sat_lib_cond (add_new_abs op vars rhs correct lib).
Proof.
  introv sata sat i; simpl in *; repndors; subst; simpl; tcsp; try apply sat; tcsp.
Qed.
Hint Resolve implies_sat_lib_cond_add_new_abs : slow.

Lemma implies_sat_lib_cond_add_new_cs {o} :
  forall name restr (lib : @library o),
    sat_lib_cond lib
    -> sat_cond_restr lib restr
    -> sat_lib_cond (add_new_cs name restr lib).
Proof.
  introv sat satr i; simpl in *; repndors; subst; simpl; tcsp; try apply sat; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_sat_lib_cond_add_new_cs : slow.

Lemma add_choice_preserves_sat_lib_cond {o} :
  forall (c : LibCond) name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> c (get_cterm v)
    -> sat_cond_lib c lib
    -> sat_cond_lib c lib'.
Proof.
  introv addc cond sat i.
  eapply add_choice_implies2 in i; eauto; repndors; exrepnd; subst; tcsp.
  applydup sat in i0; simpl in *; repnd; dands; tcsp.
  introv i; apply in_snoc in i; repndors; subst; tcsp.
Qed.
Hint Resolve add_choice_preserves_sat_lib_cond : slow.

Lemma add_one_choice_preserves_sat_lib_cond {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> sat_cond_cterm lib v
    -> sat_lib_cond lib
    -> sat_lib_cond lib'.
Proof.
  introv h sata satb; destruct lib as [lib cond]; simpl in *; tcsp.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  eapply add_choice_preserves_sat_lib_cond; eauto.
Qed.
Hint Resolve add_one_choice_preserves_sat_lib_cond : slow.

Lemma lib_extends_preserves_sat_lib_cond {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> sat_lib_cond lib2
    -> sat_lib_cond lib1.
Proof.
  introv ext.
  lib_ext_ind ext Case; introv satl; tcsp.
Qed.
Hint Resolve lib_extends_preserves_sat_lib_cond : slow.

Lemma implies_lib_cond_sat_choices_app_left {o} :
  forall (lib1 lib2 : @library o) vals1 vals2,
    same_conds lib2 lib1
    -> lib_cond_sat_choices lib2 (vals1 ++ vals2)
    -> lib_cond_sat_choices lib1 vals1.
Proof.
  introv same sat i.
  unfold sat_cond_cterm in *; rewrite <- same; apply sat; apply in_app_iff; tcsp.
Qed.
Hint Resolve implies_lib_cond_sat_choices_app_left : slow.
