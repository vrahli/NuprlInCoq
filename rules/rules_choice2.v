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


Require Export rules_choice.



Lemma isprog_vars_or_implies {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_or a b).
Proof.
  introv ispa ispb.
  allrw @isprog_vars_eq.
  simpl in *; autorewrite with slow.
  repnd; dands; auto.
  { rw subvars_app_l; dands; auto. }
  { repeat constructor; simpl; introv k; repndors; subst; tcsp; constructor; auto. }
Qed.

Definition mkcv_or {p} vs (A B : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := A in
  let (b,y) := B in
  exist (isprog_vars vs) (mk_or a b) (isprog_vars_or_implies vs a b x y).

Definition mk_cs_eq {p} (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp CompOpEq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Lemma isprog_cs_eq {o} :
  forall a b c d : @NTerm o,
    isprog (mk_cs_eq a b c d)
    <=> (isprog a
         # isprog b
         # isprog c
         # isprog d).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_less.
Qed.

Lemma isprog_cs_eq_implies {o} :
  forall a b c d : @NTerm o,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_cs_eq a b c d).
Proof.
  introv u v w z.
  apply isprog_less; sp.
Qed.

Definition mkc_cs_eq {o} (t1 t2 t3 t4 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
  exist isprog (mk_cs_eq a b c d) (isprog_cs_eq_implies a b c d x y z w).

Lemma implies_isprog_vars_cs_eq {o} :
  forall vs (a b c d : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs d
    -> isprog_vars vs (mk_cs_eq a b c d).
Proof.
  introv u v w z.
  apply isprog_vars_less; sp.
Qed.

Definition mkcv_cs_eq {p} vs (t1 t2 t3 t4 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
  exist (isprog_vars vs) (mk_cs_eq a b c d) (implies_isprog_vars_cs_eq vs a b c d x y z w).

Lemma implies_isprog_vars_btrue {o} :
  forall vs, @isprog_vars o vs mk_btrue.
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; tcsp.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.

Definition mkcv_btrue {o} vs : @CVTerm o vs :=
  exist (isprog_vars vs) mk_btrue (implies_isprog_vars_btrue _).

Lemma implies_isprog_vars_bfalse {o} :
  forall vs, @isprog_vars o vs mk_bfalse.
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; tcsp.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.

Definition mkcv_bfalse {o} vs : @CVTerm o vs :=
  exist (isprog_vars vs) mk_bfalse (implies_isprog_vars_bfalse _).



Definition ls2 {o} (a b : NVar) : @NTerm o :=
  mk_function
    (mk_csname 0)
    a
    (mk_function
       (mk_csname 0)
       b
       (mk_or
          (mk_cequiv (mk_var a) (mk_var b))
          (mk_not (mk_cequiv (mk_var a) (mk_var b))))).

Definition ls2c {o} (a b : NVar) : @CTerm o :=
  mkc_function
    (mkc_csname 0)
    a
    (mkcv_function
       _
       (mkcv_csname _ 0)
       b
       (mkcv_or
          _
          (mkcv_cequiv _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)))
          (mkcv_not _ (mkcv_cequiv _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)))))).

Definition ls2_extract {o} (a b : NVar) : @NTerm o :=
  mk_lam a (mk_lam b (mk_cs_eq (mk_var a) (mk_var b) mk_btrue mk_bfalse)).

Definition ls2c_extract {o} (a b : NVar) : @CTerm o :=
  mkc_lam a (mkcv_lam [a] b (mkcv_cs_eq
                               _
                               (mk_cv_app_l [b] _ (mkc_var a))
                               (mk_cv_app_r [a] _ (mkc_var b))
                               (mkcv_btrue _)
                               (mkcv_bfalse _))).

Lemma lsubstc_ls2_eq {o} :
  forall a b (w : @wf_term o (ls2 a b)) s c,
    lsubstc (ls2 a b) w s c = ls2c a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls2_eq : slow.

Lemma lsubstc_ls2_extract_eq {o} :
  forall a b (w : @wf_term o (ls2_extract a b)) s c,
    lsubstc (ls2_extract a b) w s c = ls2c_extract a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls2_extract_eq : slow.

Lemma substc2_mkcv_or {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_or [v,x] a b)
    = mkcv_or [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_mkcv_or : slow.

Lemma substc2_mkcv_cequiv {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_cequiv [v,x] a b)
    = mkcv_cequiv [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_mkcv_cequiv : slow.

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

Lemma mkcv_cequiv_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_cequiv [v] a b)
    = mkc_cequiv (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @mkcv_cequiv_substc : slow.

Lemma substc2_mkcv_void {o} :
  forall v x (w : @CTerm o),
    substc2 v w x (mkcv_void [v,x])
    = mkcv_void [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst; simpl.
  autorewrite with slow; fold_terms; boolvar; simpl; auto.
  boolvar; auto; tcsp.
Qed.
Hint Rewrite @substc2_mkcv_void : slow.

Lemma substc2_not {o} :
  forall v x (w : @CTerm o) (t : CVTerm [v,x]),
    alphaeqcv
      [v]
      (substc2 v w x (mkcv_not [v,x] t))
      (mkcv_not [v] (substc2 v w x t)).
Proof.
  introv.
  repeat rewrite mkcv_not_eq.
  eapply alphaeqcv_trans;[apply substc2_fun|].
  autorewrite with slow.
  apply alphaeqcv_refl.
Qed.

Lemma implies_ccequivc_ext_cequiv {o} :
  forall lib (f g a b : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_cequiv f a) (mkc_cequiv g b).
Proof.
  introv ceqa ceqb x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  simpl in *; spcast.
  apply cequivc_decomp_cequiv; auto.
Qed.
Hint Resolve implies_ccequivc_ext_cequiv : slow.

Hint Rewrite @mkcv_not_substc : slow.

Lemma apply_apply_ls2c_extract {o} :
  forall lib a b (d : a <> b) (a1 b1 : @CTerm o),
    reduces_toc
      lib
      (mkc_apply (mkc_apply (ls2c_extract a b) a1) b1)
      (mkc_cs_eq a1 b1 mkc_btrue mkc_bfalse).
Proof.
  introv d; introv.
  destruct_cterms.
  unfold reduces_toc; simpl.

  eapply reduces_to_if_split2;[csunf; simpl; eauto|].

  unfold apply_bterm; simpl.
  unflsubst; simpl.
  autorewrite with slow.
  repeat (boolvar;tcsp; simpl).
  fold_terms.

  eapply reduces_to_if_split2;[csunf; simpl; eauto|].

  unfold apply_bterm; simpl.
  unflsubst; simpl.
  autorewrite with slow.
  repeat (boolvar;tcsp; simpl);
    fold_terms;
    rewrite lsubst_aux_trivial2; simpl; eauto 3 with slow;
      introv xx; repndors; ginv; tcsp; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_apply_apply_ls2c_extract {o} :
  forall lib a b (d : a <> b) (a1 b1 : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply (mkc_apply (ls2c_extract a b) a1) b1)
      (mkc_cs_eq a1 b1 mkc_btrue mkc_bfalse).
Proof.
  introv d ext; spcast.
  apply reduces_toc_implies_cequivc.
  apply apply_apply_ls2c_extract; auto.
Qed.

Lemma implies_approx_cs_eq {o} :
  forall lib (a1 a2 a3 a4 b1 b2 b3 b4 : @NTerm o),
    approx lib a1 b1
    -> approx lib a2 b2
    -> approx lib a3 b3
    -> approx lib a4 b4
    -> approx lib (mk_cs_eq a1 a2 a3 a4) (mk_cs_eq b1 b2 b3 b4).
Proof.
  introv h1 h2 h3 h4.
  applydup @approx_relates_only_progs in h1.
  applydup @approx_relates_only_progs in h2.
  applydup @approx_relates_only_progs in h3.
  applydup @approx_relates_only_progs in h4.
  repnd.
  unfold mk_cs_eq.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_cs_eq {o} :
  forall lib (a1 a2 a3 a4 b1 b2 b3 b4 : @CTerm o),
    cequivc lib a1 b1
    -> cequivc lib a2 b2
    -> cequivc lib a3 b3
    -> cequivc lib a4 b4
    -> cequivc lib (mkc_cs_eq a1 a2 a3 a4) (mkc_cs_eq b1 b2 b3 b4).
Proof.
  unfold cequivc.
  introv h1 h2 h3 h4.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud h1.
  repnud h2.
  repnud h3.
  repnud h4.
  repnd.
  split; apply implies_approx_cs_eq; auto.
Qed.

Lemma implies_ccequivc_ext_cs_eq {o} :
  forall lib (a1 a2 a3 a4 b1 b2 b3 b4 : @CTerm o),
    ccequivc_ext lib a1 b1
    -> ccequivc_ext lib a2 b2
    -> ccequivc_ext lib a3 b3
    -> ccequivc_ext lib a4 b4
    -> ccequivc_ext lib (mkc_cs_eq a1 a2 a3 a4) (mkc_cs_eq b1 b2 b3 b4).
Proof.
  introv ceqa ceqb ceqc ceqd x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  pose proof (ceqc _ x) as ceqc.
  pose proof (ceqd _ x) as ceqd.
  simpl in *; spcast.
  apply implies_cequivc_cs_eq; auto.
Qed.
Hint Resolve implies_ccequivc_ext_cs_eq : slow.

Lemma implies_ccequivc_ext_not {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_not a) (mkc_not b).
Proof.
  introv ceq x.
  pose proof (ceq _ x) as ceq.
  simpl in *; spcast.
  apply cequivc_mkc_fun; auto.
Qed.
Hint Resolve implies_ccequivc_ext_not : slow.



(**

<<
   H |- ∀ (a b:Free). a ~ b ∨ !(a ~ b)

     By LS2
>>

 *)


Definition rule_ls2 {o}
           (lib : @library o)
           (a b : NVar)
           (H  : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls2 a b) (ls2_extract a b)))
    []
    [].

Lemma rule_ls2_true {o} :
  forall (lib : library) (a b : NVar) (H : @bhyps o) (d1 : a <> b) (safe : safe_library lib),
    rule_true lib (rule_ls2 lib a b H).
Proof.
  unfold rule_ls2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls2_extract a b) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp; introv h; autorewrite with slow in *; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  assert (tequality lib (ls2c a b) (ls2c a b)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    intros lib' xt a1 a2 ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat (rewrite substc_mkcv_function;[|auto];[]).
    autorewrite with slow.

    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply equality_in_csname_iff in ea.
    apply equality_in_csname_iff in eb.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact eb]; clear ea eb; introv y ea eb; exrepnd; spcast.
    unfold equality_of_csname in *; exrepnd; spcast.

    apply tequality_mkc_or.

    dands.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
         apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
         apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
      apply tequality_mkc_cequiv.
      apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
    }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    eapply tequality_respects_cequivc_left;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    eapply tequality_respects_cequivc_right;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    apply tequality_mkc_cequiv.
    apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
  }

  dands; auto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].
  clear teq.

  intros lib' xt a1 a2 ea.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).
  autorewrite with slow.

  apply equality_in_function2; dands; eauto 3 with slow.

  {
    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply equality_in_csname_iff in ea.
    apply equality_in_csname_iff in eb.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact eb]; clear ea eb; introv y ea eb; exrepnd; spcast.
    unfold equality_of_csname in *; exrepnd; spcast.

    apply tequality_mkc_or.

    dands.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
         apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
         apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
      apply tequality_mkc_cequiv.
      apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
    }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    eapply tequality_respects_cequivc_left;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    eapply tequality_respects_cequivc_right;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    apply tequality_mkc_cequiv.
    apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
  }

  intros lib' xt b1 b2 eb.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ea;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].

  repeat rewrite substcv_as_substc2.
  autorewrite with slow.
  repeat rewrite substc2_mk_cv_app_r; tcsp.
  autorewrite with slow.

  apply equality_in_csname_iff in ea.
  apply equality_in_csname_iff in eb.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact eb]; clear ea eb; introv y ea eb; exrepnd; spcast.
  unfold equality_of_csname in *; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  apply equality_mkc_or.
  dands; eauto 3 with slow.

  {
    apply tequality_mkc_cequiv.
    apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
  }

  {
    eapply type_respects_alphaeqc;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    eapply tequality_respects_cequivc_left;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    eapply tequality_respects_cequivc_right;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
       apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto |].
    apply tequality_mkc_cequiv.
    apply in_ext_implies_all_in_ex_bar; introv xt; tcsp.
  }

  apply in_ext_implies_all_in_ex_bar.
  introv xt.

  eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb0;[|eauto].
  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  destruct (choice_sequence_name_deq name0 name) as [d|d]; subst.

  {
    left.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    eapply cequivc_preserving_equality;
      [|apply ccequivc_ext_sym;apply implies_ccequivc_ext_cequiv;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto ].
    apply equality_in_mkc_cequiv.
    apply in_ext_implies_all_in_ex_bar; introv xt; dands; spcast; eauto 3 with slow.
  }

  {
    right.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    eapply alphaeqc_preserving_equality;
      [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    eapply cequivc_preserving_equality;
      [|apply ccequivc_ext_sym;apply implies_ccequivc_ext_not;
        apply implies_ccequivc_ext_cequiv;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto ].

    apply equality_in_not; dands.

    { apply tequality_mkc_cequiv.
      apply in_ext_implies_all_in_ex_bar; introv xt; tcsp. }

    introv xt inh.
    apply inhabited_cequiv in inh.
    eapply all_in_ex_bar_implies_exists_lib_extends in inh;[|apply lib_extends_refl].
    exrepnd; GC; spcast.
    eapply cequivc_choice_seq in inh0; eauto 3 with slow.
    apply computes_to_valc_isvalue_eq in inh0; ginv;eauto 3 with slow.
  }
Qed.
