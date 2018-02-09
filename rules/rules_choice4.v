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
Require Export per_can.



Lemma isprog_vars_comp_seq1_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_comp_seq1 a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_apply; sp.
Qed.

Lemma isprog_vars_comp_seq2_implies {p} :
  forall l k (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_comp_seq2 l k a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_apply; sp.
Qed.

Lemma isprogram_comp_seq1 {p} :
  forall (a b : @NTerm p), isprogram a -> isprogram b -> isprogram (mk_comp_seq1 a b).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_apply; sp.
Qed.

Lemma isprogram_comp_seq2 {p} :
  forall l k (a b : @NTerm p), isprogram a -> isprogram b -> isprogram (mk_comp_seq2 l k a b).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_apply; sp.
Qed.

Theorem isprog_comp_seq1 {p} :
  forall (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_comp_seq1 a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_comp_seq1; auto.
Qed.

Theorem isprog_comp_seq2 {p} :
  forall l k (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_comp_seq2 l k a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_comp_seq2; auto.
Qed.

Definition mkc_comp_seq1 {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_comp_seq1 a b) (isprog_comp_seq1 a b x y).

Definition mkc_comp_seq2 {p} l k (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_comp_seq2 l k a b) (isprog_comp_seq2 l k a b x y).

Definition mkcv_comp_seq1 {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_comp_seq1 a b) (isprog_vars_comp_seq1_implies a b vs x y).

Definition mkcv_comp_seq2 {p} vs l k (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_comp_seq2 l k a b) (isprog_vars_comp_seq2_implies l k a b vs x y).


Definition nsls1 {o} (n f a : NVar) : @NTerm o :=
  mk_function
    mk_tnat
    n
    (mk_function
       (mk_natk2nat (mk_var n))
       f
       (mk_exists
          (mk_csname 0)
          a
          (mk_equality
             (mk_var f)
             (mk_var a)
             (mk_natk2nat (mk_var n))))).

Definition nsls1c {o} (n f a : NVar) : @CTerm o :=
  mkc_function
    mkc_tnat
    n
    (mkcv_function
       _
       (mkcv_natk2nat _ (mkc_var n))
       f
       (mkcv_exists
          _
          (mkcv_csname _ 0)
          a
          (mkcv_equality
             [a,f,n]
             (mk_cv_app_l [a] _ (mk_cv_app_r [n] _ (mkc_var f)))
             (mk_cv_app_r [f,n] _ (mkc_var a))
             (mk_cv_app_l [a,f] _ (mkcv_natk2nat _ (mkc_var n)))))).

Definition nsls1_extract {o} (n f : NVar) : @NTerm o :=
  mk_lam n (mk_lam f (mk_pair (mk_comp_seq1 (mk_var n) (mk_var f)) mk_axiom)).

Definition nsls1c_extract {o} (n f : NVar) : @CTerm o :=
  mkc_lam
    n
    (mkcv_lam
       [n]
       f
       (mkcv_pair
          _
          (mkcv_comp_seq1
             _
             (mk_cv_app_l [f] _ (mkc_var n))
             (mk_cv_app_r [n] _ (mkc_var f)))
          (mkcv_ax _))).

Lemma lsubstc_nsls1_eq {o} :
  forall n f a (w : @wf_term o (nsls1 n f a)) s c,
    lsubstc (nsls1 n f a) w s c = nsls1c n f a.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_nsls1_eq : slow.

Lemma lsubstc_nsls1_extract_eq {o} :
  forall n f (w : @wf_term o (nsls1_extract n f)) s c,
    lsubstc (nsls1_extract n f) w s c = nsls1c_extract n f.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_nsls1_extract_eq : slow.

Lemma subst_nsls1_cond1 {o} :
  forall n f a (t : @CTerm o) (d1 : n <> a) (d2 : n <> f),
    alphaeqcv
      _
      (substcv
         [f] t n
         (mkcv_exists
            _
            (mkcv_csname _ 0)
            a
            (mkcv_equality
               _
               (mk_cv_app_l [a] ([f] ++ [n]) (mk_cv_app_r [n] [f] (mkc_var f)))
               (mk_cv_app_r [f, n] [a] (mkc_var a))
               (mk_cv_app_l [a, f] [n] (mkcv_natk2nat [n] (mkc_var n))))))
      (mkcv_exists
         _
         (mkcv_csname _ 0)
         a
         (mkcv_equality
            _
            (mk_cv_app_l [a] _ (mkc_var f))
            (mk_cv_app_r [f] [a] (mkc_var a))
            (mk_cv _ (natk2nat t)))).
Proof.
  introv d1 d2.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfsubst; simpl.

  autorewrite with slow.
  boolvar; tcsp.
  fold_terms.
  simpl.
  repeat (autorewrite with slow; rewrite beq_var_newvar_trivial1; simpl; tcsp;[]).
  boolvar; tcsp;[].

  allrw @fold_image.
  allrw @fold_mk_squash.
  allrw @fold_csname.
  apply implies_alpha_eq_mk_product.
  apply implies_alpha_eq_mk_equality.

  fold (mk_natk2nat x).

  pose proof (substc_mkcv_natk2nat n (mkc_var n) (mk_ct x i)) as q.
  unfold alphaeqc in q; simpl in q.
  unfsubst in q; simpl in q.

  repeat (autorewrite with slow in q; rewrite beq_var_newvar_trivial1 in q; simpl in q; tcsp;[]).
  fold_terms.

  unfsubst in q; simpl in *; boolvar; tcsp.
Qed.

Lemma isprog_vars_lam_pair_comp_seq1 {o} :
  forall n f,
    @isprog_vars o [n] (mk_lam f (mk_pair (mk_comp_seq1 (mk_var n) (mk_var f)) mk_axiom)).
Proof.
  introv.
  repeat constructor; simpl; autorewrite with slow.
  unfold remove_nvars, sub_vars, assert, subsetb; simpl; boolvar; auto.
  simpl; boolvar; simpl; tcsp.
Qed.
Hint Resolve isprog_vars_lam_pair_comp_seq1 : slow.

Lemma isprogram_lam_pair_comp_seq1 {o} :
  forall f (x : @NTerm o),
    isprogram x
    -> isprogram (mk_lam f (mk_pair (mk_comp_seq1 x (mk_var f)) mk_axiom)).
Proof.
  introv isp.
  repeat constructor; simpl.
  { unfold closed; simpl; autorewrite with slow.
    destruct isp as [cl wf]; rewrite cl; autorewrite with slow; auto. }
  introv xx; repndors; subst; tcsp.
  apply bt_wf_iff.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
  apply bt_wf_iff.
  destruct isp; tcsp.
Qed.
Hint Resolve isprogram_lam_pair_comp_seq1 : slow.

Lemma ccequivc_ext_mkc_apply_nsls1c_extract {o} :
  forall lib (a : @CTerm o) n f k (d : n <> f),
    computes_to_valc lib a (mkc_nat k)
    -> ccequivc_ext
         lib
         (mkc_apply (nsls1c_extract n f) a)
         (mkc_lam
            f
            (mkcv_pair
               _
               (mkcv_comp_seq1
                  _
                  (mk_cv _ a)
                  (mkc_var f))
               (mkcv_ax _))).
Proof.
  introv d comp ext; spcast.
  eapply lib_extends_preserves_computes_to_valc in comp;[|eauto].
  destruct_cterms.
  unfold computes_to_valc in *; simpl in *.
  unfold cequivc; simpl.
  eapply cequiv_trans;[apply cequiv_beta; eauto 3 with slow|];[].
  unfsubst; simpl; fold_terms.
  autorewrite with slow.
  repeat (boolvar; simpl; tcsp).
  apply cequiv_refl; eauto 3 with slow.
Qed.

Lemma isprog_vars_pair_comp_seq1 {o} :
  forall n f,
    isprog n
    -> @isprog_vars o [f] (mk_pair (mk_comp_seq1 n (mk_var f)) mk_axiom).
Proof.
  introv isp.
  repeat constructor; simpl; autorewrite with slow.
  { apply isprog_eq in isp.
    destruct isp as [cl wf]; rewrite cl; simpl.
    unfold sub_vars, assert, subsetb; simpl; boolvar; auto. }
  apply wf_term_eq.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
  constructor.
  apply isprog_eq in isp.
  destruct isp as [cl wf]; tcsp.
Qed.
Hint Resolve isprog_vars_pair_comp_seq1 : slow.

Lemma isprogram_pair_comp_seq1 {o} :
  forall (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_pair (mk_comp_seq1 a b) mk_axiom).
Proof.
  introv ispa ispb.
  repeat constructor; simpl.
  { unfold closed; simpl; autorewrite with slow.
    destruct ispa as [cla wfa]; destruct ispb as [clb wfb]; rewrite cla, clb; autorewrite with slow; auto. }
  introv xx; repndors; subst; tcsp;
    apply bt_wf_iff;
    repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp);
    apply bt_wf_iff;
    destruct ispa; destruct ispb; tcsp.
Qed.
Hint Resolve isprogram_pair_comp_seq1 : slow.

Lemma ccequivc_ext_mkc_apply_mkc_lam_pair_comp_seq1 {o} :
  forall lib n f (a : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply
         (mkc_lam f (mkcv_pair _ (mkcv_comp_seq1 _ (mk_cv _ n) (mkc_var f)) (mkcv_ax _)))
         a)
      (mkc_pair (mkc_comp_seq1 n a) mkc_axiom).
Proof.
  introv ext; spcast.
  destruct_cterms.
  unfold cequivc; simpl.
  eapply cequiv_trans;[apply cequiv_beta; eauto 3 with slow|];[].
  unfsubst; simpl; fold_terms.
  rewrite lsubst_aux_trivial_cl_term2; eauto 3 with slow.
  boolvar;tcsp.
  apply cequiv_refl; eauto 2 with slow.
  apply isprogram_pair_comp_seq1; eauto 3 with slow.
Qed.

Lemma implies_approx_comp_seq1 {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_comp_seq1 f a) (mk_comp_seq1 g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  unfold mk_comp_seq1.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_comp_seq1 {p} :
  forall lib f g a b,
    cequivc lib f g
    -> @cequivc p lib a b
    -> cequivc lib (mkc_comp_seq1 f a) (mkc_comp_seq1 g b).
Proof.
  unfold cequivc. introv H1c H2c.
  destruct_cterms. allsimpl. apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_comp_seq1; auto.
Qed.

Lemma implies_ccequivc_ext_comp_seq1 {o} :
  forall lib (f g a b : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_comp_seq1 f a) (mkc_comp_seq1 g b).
Proof.
  introv ceqa ceqb x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  simpl in *; spcast.
  apply implies_cequivc_comp_seq1; auto.
Qed.
Hint Resolve implies_ccequivc_ext_comp_seq1 : slow.

Definition mkc_fresh_choice_nat_seq {o} (l : list nat) : @CTerm o :=
  let cs := "a" in
  mkc_choice_seq (MkChoiceSequenceName cs (cs_kind_seq l)).

Lemma mk_comp_seq2_reduces_to_choice_seq {o} :
  forall lib (f : @NTerm o) l w,
    0 < length l
    -> (forall n i,
           select n l = Some i -> mk_apply f (mk_nat (length w + n)) =v>(lib) mk_nat i)
    -> reduces_to
         lib
         (mk_comp_seq2 w (length w + length l) (mk_apply f (mk_nat (length w))) f)
         (mk_fresh_choice_nat_seq lib (w ++ l)).
Proof.
  induction l; introv cond imp; simpl in *; autorewrite with slow nat; try omega.

  pose proof (imp 0 a) as q; simpl in q; autodimp q hyp.
  autorewrite with slow nat in *.
  destruct q as [q isv].
  eapply reduces_to_trans;[apply reduces_to_prinarg;exact q|].

  destruct (deq_nat (length l) 0) as [d|d].

  { apply reduces_to_if_step.
    csunf; simpl; boolvar; autorewrite with slow in *; try omega.
    destruct l; simpl in *; tcsp; GC.
    rewrite <- snoc_as_append; auto. }

  eapply reduces_to_if_split2.
  { csunf; simpl; boolvar; try omega; autorewrite with slow; eauto. }
  rewrite <- snoc_append_r.
  rewrite <- plus_Snm_nSm.

  pose proof (IHl (snoc w a)) as h.
  autodimp h hyp; try omega;[].
  allrw length_snoc.
  autodimp h hyp.
  introv s.
  pose proof (imp (S n) i) as z; simpl in z; autodimp z hyp.
  rewrite <- plus_Snm_nSm in z; auto.
Qed.

Lemma mk_comp_seq1_reduces_to_choice_seq {o} :
  forall lib k (f : @NTerm o) l,
    length l = k
    -> (forall n i,
           select n l = Some i
           -> computes_to_value lib (mk_apply f (mk_nat n)) (mk_nat i))
    -> computes_to_value lib (mk_comp_seq1 (mk_nat k) f) (mk_fresh_choice_nat_seq lib l).
Proof.
  introv eqlen imp.
  destruct (deq_nat k 0).

  { subst.
    split; eauto 3 with slow.
    apply reduces_to_if_step; csunf; simpl.
    boolvar; autorewrite with slow in *; try omega.
    destruct l; simpl in *; tcsp. }

  eapply computes_to_value_step;
    [|csunf; simpl; boolvar; autorewrite with slow in *; subst; try omega; eauto].

  split; eauto 2 with slow.

  pose proof (mk_comp_seq2_reduces_to_choice_seq lib f l []) as q.
  simpl in *; autorewrite with slow in *.
  repeat (autodimp q hyp); try omega.
Qed.

Lemma ccomputes_to_valc_implies_ex {o} :
  forall lib (a b : @NTerm o),
    Cast (computes_to_value lib a b)
    -> {k : nat
        , reduces_in_atmost_k_steps lib a b k
        # iscan b}.
Proof.
  introv comp; spcast.
  unfold hasvalue, computes_to_value, reduces_to in comp; exrepnd.
  exists k; dands; eauto 2 with slow.
Qed.

Lemma dec_eq_nat {o} :
  forall (t : @NTerm o) k,
    decidable (t = mk_nat k).
Proof.
  introv.
  destruct t as [v|op bs].
  - right; introv xx; ginv.
  - destruct op; try (complete (right; introv xx; ginv)).
    destruct c; try (complete (right; introv xx; ginv)).
    destruct bs; try (complete (right; introv xx; ginv)).
    destruct (Z_noteq_dec z (Z.of_nat k)); subst; tcsp.
    right; introv xx; inversion xx; tcsp.
Qed.

Lemma dec_reduces_in_atmost_k_steps_nat {o} :
  forall lib k (t : @NTerm o) n,
    decidable (reduces_in_atmost_k_steps lib t (mk_nat n) k).
Proof.
  introv.
  unfold reduces_in_atmost_k_steps.
  remember (compute_at_most_k_steps lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct (dec_eq_nat n0 n); subst; tcsp.
    right; introv xx; ginv.
  - right; introv xx; ginv.
Qed.

Lemma computes_to_valc_nat_stable {o} :
  forall lib (a : @CTerm o) k, ccomputes_to_valc lib a (mkc_nat k) -> computes_to_valc lib a (mkc_nat k).
Proof.
  introv.
  destruct_cterms.
  intro h.
  apply ccomputes_to_valc_implies_ex in h; simpl in *.
  assert (exists k0, reduces_in_atmost_k_steps lib x (mk_nat k) k0) as q.
  { exrepnd; eexists; eauto. }
  clear h; rename q into h.
  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in h; auto;
    [|introv; destruct (dec_reduces_in_atmost_k_steps_nat lib x0 x k); tcsp].
  exrepnd.
  split; simpl; auto.
  exists x0; auto.
Qed.

Lemma mkc_comp_seq1_reduces_to_choice_seq {o} :
  forall lib k (f : @CTerm o) l,
    length l = k
    -> (forall n i,
           select n l = Some i
           -> (mkc_apply f (mkc_nat n)) ===>(lib) (mkc_nat i))
    -> computes_to_valc lib (mkc_comp_seq1 (mkc_nat k) f) (mkc_fresh_choice_nat_seq l).
Proof.
  introv eqlen imp.
  destruct_cterms.
  apply mk_comp_seq1_reduces_to_choice_seq; auto.
  introv s.
  apply imp in s.
  apply computes_to_valc_nat_stable in s; auto.
Qed.



(**

<<
   H |- ∀ (n ∈ ℕ) (f ∈ ℕn→ℕ). ∃ (a:Free). f = a ∈ ℕn→ℕ

     By LS1
>>

 *)

Definition rule_nsls1 {o}
           (lib   : @library o)
           (n f a : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (nsls1 n f a) (nsls1_extract n f)))
    []
    [].

Lemma rule_nsls1_true {o} :
  forall lib (n f a : NVar) (H : @bhyps o)
         (d1 : n <> f) (d2 : n <> a) (d3 : a <> f) (safe : safe_library lib),
    rule_true lib (rule_nsls1 lib n f a H).
Proof.
  unfold rule_nsls1, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (nsls1_extract n f) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp.
    introv xx.
    autorewrite with slow in xx; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  assert (tequality lib (nsls1c n f a) (nsls1c n f a)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat (rewrite substc_mkcv_function;[|auto];[]).

    apply equality_in_tnat in ea.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib y safe.
    rename lib' into lib; rename safe' into safe.

    unfold per_props_nat.equality_of_nat in ea; exrepnd; spcast.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_nsls1_cond1; auto|];[].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_nsls1_cond1; auto|];[].

    apply tequality_function; dands; eauto 3 with slow.

    {
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      autorewrite with slow.
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    introv xt ef.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
    autorewrite with slow in *.

    repeat (rewrite mkcv_exists_substc; auto;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  dands; eauto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].

  clear teq.

  introv xt ea.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).

  apply equality_in_tnat in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  unfold per_props_nat.equality_of_nat in ea; exrepnd; spcast.

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
      apply subst_nsls1_cond1; auto];[].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_nsls1c_extract;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_nsls1c_extract;eauto|].

  apply equality_in_function2.
  dands.

  {
    apply tequality_function; dands; eauto 3 with slow.

    {
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      autorewrite with slow.
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    introv xt ef.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
    autorewrite with slow in *.

    repeat (rewrite mkcv_exists_substc; auto;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  introv xt ef.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
  autorewrite with slow in *.
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_mkc_lam_pair_comp_seq1;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_mkc_lam_pair_comp_seq1;eauto|].

  rewrite mkcv_exists_substc; auto.
  autorewrite with slow.
  rewrite substc2_mk_cv_app_r; auto.

  dup ef as en2n.
  eapply cequivc_preserving_equality in ef;
    [|introv ext; spcast; apply implies_cequivc_natk2nat;
      apply computes_to_valc_implies_cequivc;eauto 3 with slow].
  dup ef as enf.
  apply equality_natk2nat_implies2 in enf.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact enf]; clear enf; introv y enf; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  eapply equality_monotone in ef;[|eauto].
  eapply equality_monotone in en2n;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  apply computes_upto_implies_exists_nat_seq in enf; exrepnd.

  apply equality_in_product; dands; eauto 3 with slow.

  {
    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    eapply equality_monotone in en2n;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe enf0.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply equality_refl in en2n.
    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply computes_to_valc_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  remember (MkChoiceSequenceName "a" (cs_kind_seq l)) as name.
  assert (is_nat_or_seq_kind name) as isn by (subst; eauto 3 with slow; tcsp).

  exists (extend_seq_to_bar lib safe k name isn).
  introv br ext.

  exists (mkc_comp_seq1 a0 a1) (mkc_comp_seq1 a' a'0) (@mkc_axiom o) (@mkc_axiom o).
  dands; spcast; eauto 3 with slow.

  {
    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_comp_seq1;
       [apply computes_to_valc_implies_ccequivc_ext;eauto 4 with slow|apply ccequivc_ext_refl]
      |].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym;apply implies_ccequivc_ext_comp_seq1;
       [apply computes_to_valc_implies_ccequivc_ext;eauto 4 with slow|apply ccequivc_ext_refl]
      |].
    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym;
       apply computes_to_valc_implies_ccequivc_ext;
       apply mkc_comp_seq1_reduces_to_choice_seq; eauto;
       introv ss;
       apply enf0 in ss; repnd; spcast; eauto 4 with slow|].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym;
       apply computes_to_valc_implies_ccequivc_ext;
       apply mkc_comp_seq1_reduces_to_choice_seq; eauto;
       introv ss;
       apply enf0 in ss; repnd; spcast; eauto 4 with slow|].
    unfold mkc_fresh_choice_nat_seq.

    apply equality_in_csname_iff.
    apply in_ext_implies_all_in_ex_bar; introv xt'.
    unfold equality_of_csname.
    eexists; dands; spcast;[|eauto 3 with slow|eauto 3 with slow].
    unfold compatible_choice_sequence_name; simpl.
    unfold compatible_cs_kind; boolvar; tcsp.
  }

  autorewrite with slow.
  rw <- @member_equality_iff.
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_comp_seq1;
     [apply computes_to_valc_implies_ccequivc_ext;eauto 4 with slow|apply ccequivc_ext_refl]
    |].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;
     apply computes_to_valc_implies_ccequivc_ext;
     apply mkc_comp_seq1_reduces_to_choice_seq; eauto;
     introv ss;
     apply enf0 in ss; repnd; spcast; eauto 4 with slow|].

  eapply cequivc_preserving_equality;
    [|apply ccequivc_ext_sym;
      introv xt; spcast; apply implies_cequivc_natk2nat;
      apply computes_to_valc_implies_cequivc;eauto 5 with slow].

  simpl in *; exrepnd.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in br2; exrepnd.
  applydup safe' in br2.

  pose proof (extend_library_lawless_upto_implies_exists_nats name lib' lib'' entry k) as q.
  repeat (autodimp q hyp); exrepnd.

  apply implies_equality_natk2nat_prop.
  introv ltk.

  pose proof (q1 m (nth m vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; omega|];[].
  unfold is_nat in w; exrepnd.
  assert (select m vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try omega. }

  assert (safe_library_entry (lib_cs name (MkChoiceSeqEntry _ vals restr))) as safee.
  { eapply entry_in_library_implies_safe_library_entry; eauto 3 with slow. }
  simpl in * |-; repnd.

  pose proof (enf0 m i) as enf0.
  autodimp enf0 hyp;
    [eapply satisfies_cs_kind_seq_implies_select_iff; eauto; try omega; subst; simpl; auto|];[].
  repnd; spcast.

  exists i.
  dands; spcast; eauto 5 with slow;[].

  unfold computes_to_valc; simpl.
  split; eauto 3 with slow.
  eapply reduces_to_if_split2;[csunf; simpl; reflexivity|].
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_eapply; simpl; boolvar; try omega;[].
  autorewrite with slow.

  eapply lib_extends_preserves_find_cs in q0;[|eauto].
  exrepnd; simpl in *.
  destruct entry2; simpl in *.
  unfold find_cs_value_at.
  rewrite <- Heqname.
  allrw;simpl.
  rewrite find_value_of_cs_at_is_select.
  erewrite choice_sequence_vals_extends_implies_select_some; eauto; simpl; auto.
Qed.
Hint Resolve rule_nsls1_true : slow.
