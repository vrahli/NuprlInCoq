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


Require Export alphaeq.
Require Export nat_type.
Require Export csname_type.
Require Export refname_type.


Definition alphaeqc_bterm {o} vs1 (a1 : @CVTerm o vs1) vs2 (a2 : @CVTerm o vs2) :=
  alpha_eq_bterm (bterm vs1 (get_cvterm _ a1)) (bterm vs2 (get_cvterm _ a2)).

Lemma alpha_eq_mk_function {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_function t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_function t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_function {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_function t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_function t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_function in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_function_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_isect {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_isect t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_isect t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_isect {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_isect t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_isect t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_isect in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_isect_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_disect {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_disect t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_disect t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_disect {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_disect t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_disect t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_disect in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_disect_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_set {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_set t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_set t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_set {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_set t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_set t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_set in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_set_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_tunion {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_tunion t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_tunion t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_tunion {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_tunion t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_tunion t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_tunion in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_tunion_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_product {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_product t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_product t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_product {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_product t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_product t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_product in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_product_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_w {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_w t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_w t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_w {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_w t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_w t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_w in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_w_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_m {o} :
  forall (t : @NTerm o) v a u,
    alpha_eq (mk_m t v a) u
    -> {t' : NTerm
        & {v' : NVar
        & {a' : NTerm
        & u = mk_m t' v' a'
        # alpha_eq t t'
        # alpha_eq_bterm (bterm [v] a) (bterm [v'] a')}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  fold_terms.
  exists nt2 x0 nt0; sp.
  apply (al_bterm _ _ [x]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_m {o} :
  forall (t : @CTerm o) v a u,
    alphaeqc (mkc_m t v a) u
    -> {t' : CTerm
        & {v' : NVar
        & {a' : CVTerm [v']
        & u = mkc_m t' v' a'
        # alphaeqc t t'
        # alphaeqc_bterm [v] a [v'] a'}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_m in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_m_iff in j; repnd.

  exists (mk_ct t' j0) v' (mk_cvterm _ a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_pw {o} :
  forall (P : @NTerm o) ap A bp ba B cp ca cb C p u,
    alpha_eq (mk_pw P ap A bp ba B cp ca cb C p) u
    -> {P' : NTerm
        & {ap' : NVar
        & {A' : NTerm
        & {bp' : NVar
        & {ba' : NVar
        & {B' : NTerm
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : NTerm
        & {p' : NTerm
        & u = mk_pw P' ap' A' bp' ba' B' cp' ca' cb' C' p'
        # alpha_eq P P'
        # alpha_eq_bterm (bterm [ap] A) (bterm [ap'] A')
        # alpha_eq_bterm (bterm [bp,ba] B) (bterm [bp',ba'] B')
        # alpha_eq_bterm (bterm [cp,ca,cb] C) (bterm [cp',ca',cb'] C')
        # alpha_eq p p'
          }}}}}}}}}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl; try omega.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  pose proof (i 3) as h4; autodimp h4 hyp; allsimpl.
  pose proof (i 4) as h5; autodimp h5 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3, h4, h5; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  inversion h4 as [? ? ? ? ? disj4 ? ? norep4 aeq4]; subst; allsimpl; cpx; clear h4.
  inversion h5 as [? ? ? ? ? disj5 ? ? norep5 aeq5]; subst; allsimpl; cpx; clear h5.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  fold_terms.
  eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
  dands; try reflexivity; auto.
  - apply (al_bterm _ _ [x]); simpl; tcsp.
  - apply (al_bterm _ _ [x1,y]); simpl; tcsp.
  - apply (al_bterm _ _ [x3,y1,z]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_pw {o} :
  forall (P : @CTerm o) ap A bp ba B cp ca cb C p u,
    alphaeqc (mkc_pw P ap A bp ba B cp ca cb C p) u
    -> {P' : CTerm
        & {ap' : NVar
        & {A' : CVTerm [ap']
        & {bp' : NVar
        & {ba' : NVar
        & {B' : CVTerm [bp',ba']
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : CVTerm [cp',ca',cb']
        & {p' : CTerm
        & u = mkc_pw P' ap' A' bp' ba' B' cp' ca' cb' C' p'
        # alphaeqc P P'
        # alphaeqc_bterm [ap] A [ap'] A'
        # alphaeqc_bterm [bp,ba] B [bp',ba'] B'
        # alphaeqc_bterm [cp,ca,cb] C [cp',ca',cb'] C'
        # alphaeqc p p'
          }}}}}}}}}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_pw in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_pw_iff in j; repnd.

  exists (mk_ct P' j0)
         ap' (mk_cvterm _ A' j1)
         bp' ba' (mk_cvterm _ B' j2).
  exists cp' ca' cb' (mk_cvterm _ C' j3)
         (mk_ct p' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_pm {o} :
  forall (P : @NTerm o) ap A bp ba B cp ca cb C p u,
    alpha_eq (mk_pm P ap A bp ba B cp ca cb C p) u
    -> {P' : NTerm
        & {ap' : NVar
        & {A' : NTerm
        & {bp' : NVar
        & {ba' : NVar
        & {B' : NTerm
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : NTerm
        & {p' : NTerm
        & u = mk_pm P' ap' A' bp' ba' B' cp' ca' cb' C' p'
        # alpha_eq P P'
        # alpha_eq_bterm (bterm [ap] A) (bterm [ap'] A')
        # alpha_eq_bterm (bterm [bp,ba] B) (bterm [bp',ba'] B')
        # alpha_eq_bterm (bterm [cp,ca,cb] C) (bterm [cp',ca',cb'] C')
        # alpha_eq p p'
          }}}}}}}}}}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl; try omega.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  pose proof (i 3) as h4; autodimp h4 hyp; allsimpl.
  pose proof (i 4) as h5; autodimp h5 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3, h4, h5; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  inversion h4 as [? ? ? ? ? disj4 ? ? norep4 aeq4]; subst; allsimpl; cpx; clear h4.
  inversion h5 as [? ? ? ? ? disj5 ? ? norep5 aeq5]; subst; allsimpl; cpx; clear h5.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  fold_terms.
  eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
  dands; try reflexivity; auto.
  - apply (al_bterm _ _ [x]); simpl; tcsp.
  - apply (al_bterm _ _ [x1,y]); simpl; tcsp.
  - apply (al_bterm _ _ [x3,y1,z]); simpl; tcsp.
Qed.

Lemma alphaeqc_mkc_pm {o} :
  forall (P : @CTerm o) ap A bp ba B cp ca cb C p u,
    alphaeqc (mkc_pm P ap A bp ba B cp ca cb C p) u
    -> {P' : CTerm
        & {ap' : NVar
        & {A' : CVTerm [ap']
        & {bp' : NVar
        & {ba' : NVar
        & {B' : CVTerm [bp',ba']
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : CVTerm [cp',ca',cb']
        & {p' : CTerm
        & u = mkc_pm P' ap' A' bp' ba' B' cp' ca' cb' C' p'
        # alphaeqc P P'
        # alphaeqc_bterm [ap] A [ap'] A'
        # alphaeqc_bterm [bp,ba] B [bp',ba'] B'
        # alphaeqc_bterm [cp,ca,cb] C [cp',ca',cb'] C'
        # alphaeqc p p'
          }}}}}}}}}}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_pm in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_pm_iff in j; repnd.

  exists (mk_ct P' j0)
         ap' (mk_cvterm _ A' j1)
         bp' ba' (mk_cvterm _ B' j2).
  exists cp' ca' cb' (mk_cvterm _ C' j3)
         (mk_ct p' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_approx {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_approx t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_approx t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_approx_iff {o} :
  forall (a b : @NTerm o), isprog (mk_approx a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_approx_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_approx {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_approx t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_approx t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_approx in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_approx_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_cequiv {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_cequiv t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_cequiv t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_cequiv_iff {o} :
  forall (a b : @NTerm o), isprog (mk_cequiv a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_cequiv_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_cequiv {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_cequiv t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_cequiv t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_cequiv in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_cequiv_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_texc {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_texc t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_texc t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_texc_iff {o} :
  forall (a b : @NTerm o), isprog (mk_texc a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_texc_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_texc {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_texc t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_texc t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_texc in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_texc_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_union {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_union t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_union t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_union_iff {o} :
  forall (a b : @NTerm o), isprog (mk_union a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_union_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_union {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_union t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_union t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_union in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_union_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_image {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_image t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_image t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_image_iff {o} :
  forall (a b : @NTerm o), isprog (mk_image a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_image_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_image {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_image t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_image t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_image in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_image_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_ffatoms {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_free_from_atoms t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_free_from_atoms t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_ffatoms_iff {o} :
  forall (a b : @NTerm o), isprog (mk_free_from_atoms a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_free_from_atoms_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_ffatoms {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_free_from_atoms t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_free_from_atoms t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_ffatoms in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_ffatoms_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_tequality {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_tequality t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_tequality t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_tequality_iff {o} :
  forall (a b : @NTerm o), isprog (mk_tequality a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_tequality_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_tequality {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_tequality t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_tequality t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_tequality in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_tequality_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_ffatom {o} :
  forall (t : @NTerm o) x a u,
    alpha_eq (mk_free_from_atom t x a) u
    -> {t' : NTerm
        & {x' : NTerm
        & {a' : NTerm
        & u = mk_free_from_atom t' x' a'
        # alpha_eq t t'
        # alpha_eq x x'
        # alpha_eq a a' }}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_ffatom_iff {o} :
  forall (a b c : @NTerm o), isprog (mk_free_from_atom a b c) <=> (isprog a # isprog b # isprog c).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_free_from_atom_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_ffatom {o} :
  forall (t : @CTerm o) x a u,
    alphaeqc (mkc_free_from_atom t x a) u
    -> {t' : CTerm
        & {x' : CTerm
        & {a' : CTerm
        & u = mkc_free_from_atom t' x' a'
        # alphaeqc t t'
        # alphaeqc x x'
        # alphaeqc a a' }}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_ffatom in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_ffatom_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct x' j1) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_effatom {o} :
  forall (t : @NTerm o) x a u,
    alpha_eq (mk_efree_from_atom t x a) u
    -> {t' : NTerm
        & {x' : NTerm
        & {a' : NTerm
        & u = mk_efree_from_atom t' x' a'
        # alpha_eq t t'
        # alpha_eq x x'
        # alpha_eq a a' }}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_effatom_iff {o} :
  forall (a b c : @NTerm o), isprog (mk_efree_from_atom a b c) <=> (isprog a # isprog b # isprog c).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_efree_from_atom_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_effatom {o} :
  forall (t : @CTerm o) x a u,
    alphaeqc (mkc_efree_from_atom t x a) u
    -> {t' : CTerm
        & {x' : CTerm
        & {a' : CTerm
        & u = mkc_efree_from_atom t' x' a'
        # alphaeqc t t'
        # alphaeqc x x'
        # alphaeqc a a' }}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_effatom in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_effatom_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct x' j1) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_equality {o} :
  forall (t : @NTerm o) x a u,
    alpha_eq (mk_equality t x a) u
    -> {t' : NTerm
        & {x' : NTerm
        & {a' : NTerm
        & u = mk_equality t' x' a'
        # alpha_eq t t'
        # alpha_eq x x'
        # alpha_eq a a' }}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_equality_iff {o} :
  forall (a b c : @NTerm o), isprog (mk_equality a b c) <=> (isprog a # isprog b # isprog c).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_equality_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_equality {o} :
  forall (t : @CTerm o) x a u,
    alphaeqc (mkc_equality t x a) u
    -> {t' : CTerm
        & {x' : CTerm
        & {a' : CTerm
        & u = mkc_equality t' x' a'
        # alphaeqc t t'
        # alphaeqc x x'
        # alphaeqc a a' }}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_equality in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_equality_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct x' j1) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_requality {o} :
  forall (t : @NTerm o) x a u,
    alpha_eq (mk_requality t x a) u
    -> {t' : NTerm
        & {x' : NTerm
        & {a' : NTerm
        & u = mk_requality t' x' a'
        # alpha_eq t t'
        # alpha_eq x x'
        # alpha_eq a a' }}}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  pose proof (i 2) as h3; autodimp h3 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2, h3; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  inversion h3 as [? ? ? ? ? disj3 ? ? norep3 aeq3]; subst; allsimpl; cpx; clear h3.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_requality_iff {o} :
  forall (a b c : @NTerm o), isprog (mk_requality a b c) <=> (isprog a # isprog b # isprog c).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_requality_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_requality {o} :
  forall (t : @CTerm o) x a u,
    alphaeqc (mkc_requality t x a) u
    -> {t' : CTerm
        & {x' : CTerm
        & {a' : CTerm
        & u = mkc_requality t' x' a'
        # alphaeqc t t'
        # alphaeqc x x'
        # alphaeqc a a' }}}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_requality in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_requality_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct x' j1) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_partial {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_partial t) u
    -> {t' : NTerm
        & u = mk_partial t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_partial_iff {o} :
  forall (a : @NTerm o), isprog (mk_partial a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_partial_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_partial {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_partial t) u
    -> {t' : CTerm
        & u = mkc_partial t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_partial in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_partial_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_admiss {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_admiss t) u
    -> {t' : NTerm
        & u = mk_admiss t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_admiss_iff {o} :
  forall (a : @NTerm o), isprog (mk_admiss a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_admiss_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_admiss {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_admiss t) u
    -> {t' : CTerm
        & u = mkc_admiss t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_admiss in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_admiss_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_mono {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_mono t) u
    -> {t' : NTerm
        & u = mk_mono t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_mono_iff {o} :
  forall (a : @NTerm o), isprog (mk_mono a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_mono_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_mono {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_mono t) u
    -> {t' : CTerm
        & u = mkc_mono t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_mono in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_mono_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_pertype {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_pertype t) u
    -> {t' : NTerm
        & u = mk_pertype t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_pertype_iff {o} :
  forall (a : @NTerm o), isprog (mk_pertype a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_pertype_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_pertype {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_pertype t) u
    -> {t' : CTerm
        & u = mkc_pertype t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_pertype in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_pertype_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_spertype {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_spertype t) u
    -> {t' : NTerm
        & u = mk_spertype t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_spertype_iff {o} :
  forall (a : @NTerm o), isprog (mk_spertype a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_spertype_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_spertype {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_spertype t) u
    -> {t' : CTerm
        & u = mkc_spertype t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_spertype in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_spertype_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_tuni {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_tuni t) u
    -> {t' : NTerm
        & u = mk_tuni t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_tuni_iff {o} :
  forall (a : @NTerm o), isprog (mk_tuni a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_tuni_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_tuni {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_tuni t) u
    -> {t' : CTerm
        & u = mkc_tuni t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_tuni in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_tuni_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_ipertype {o} :
  forall (t : @NTerm o) u,
    alpha_eq (mk_ipertype t) u
    -> {t' : NTerm
        & u = mk_ipertype t'
        # alpha_eq t t' }.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  clear i.
  unfold selectbt in h1; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_ipertype_iff {o} :
  forall (a : @NTerm o), isprog (mk_ipertype a) <=> isprog a.
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_ipertype_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_ipertype {o} :
  forall (t : @CTerm o) u,
    alphaeqc (mkc_ipertype t) u
    -> {t' : CTerm
        & u = mkc_ipertype t'
        # alphaeqc t t' }.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_ipertype in aeq; exrepnd; subst.
  dup i as j.
  rw @isprog_ipertype_iff in j; repnd.

  exists (mk_ct t' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_base {o} :
  forall (u : @NTerm o),
    alpha_eq mk_base u
    -> u = mk_base.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_base {o} :
  forall (u : @CTerm o),
    alphaeqc mkc_base u
    -> u = mkc_base.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_base in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_int {o} :
  forall (u : @NTerm o),
    alpha_eq mk_int u
    -> u = mk_int.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_int {o} :
  forall (u : @CTerm o),
    alphaeqc mkc_int u
    -> u = mkc_int.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_int in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_csname {o} :
  forall n (u : @NTerm o),
    alpha_eq (mk_csname n) u
    -> u = mk_csname n.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_csname {o} :
  forall n (u : @CTerm o),
    alphaeqc (mkc_csname n) u
    -> u = mkc_csname n.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_csname in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_refname {o} :
  forall n (u : @NTerm o),
    alpha_eq (mk_refname n) u
    -> u = mk_refname n.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_refname {o} :
  forall n (u : @CTerm o),
    alphaeqc (mkc_refname n) u
    -> u = mkc_refname n.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_refname in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_Nat {o} :
  forall (u : @NTerm o),
    alpha_eq mk_Nat u
    -> u = mk_Nat.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_Nat {o} :
  forall (u : @CTerm o),
    alphaeqc mkc_Nat u
    -> u = mkc_Nat.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_Nat in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_atom {o} :
  forall (u : @NTerm o),
    alpha_eq mk_atom u
    -> u = mk_atom.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_atom {o} :
  forall (u : @CTerm o),
    alphaeqc mkc_atom u
    -> u = mkc_atom.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_atom in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_uatom {o} :
  forall (u : @NTerm o),
    alpha_eq mk_uatom u
    -> u = mk_uatom.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_uatom {o} :
  forall (u : @CTerm o),
    alphaeqc mkc_uatom u
    -> u = mkc_uatom.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_uatom in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_uni {o} :
  forall i (u : @NTerm o),
    alpha_eq (mk_uni i) u
    -> u = mk_uni i.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len j]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
Qed.

Lemma alphaeqc_mkc_uni {o} :
  forall i (u : @CTerm o),
    alphaeqc (mkc_uni i) u
    -> u = mkc_uni i.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_uni in aeq; exrepnd; subst.
  apply cterm_eq; simpl; auto.
Qed.

Lemma alpha_eq_mk_sup {o} :
  forall (t : @NTerm o) a u,
    alpha_eq (mk_sup t a) u
    -> {t' : NTerm
        & {a' : NTerm
        & u = mk_sup t' a'
        # alpha_eq t t'
        # alpha_eq a a' }}.
Proof.
  introv aeq.
  inversion aeq as [|? ? ? len i]; subst; allsimpl.
  destruct lbt2; allsimpl; repeat cpx.
  pose proof (i 0) as h1; autodimp h1 hyp; allsimpl.
  pose proof (i 1) as h2; autodimp h2 hyp; allsimpl.
  clear i.
  unfold selectbt in h1, h2; allsimpl.
  inversion h1 as [? ? ? ? ? disj1 ? ? norep1 aeq1]; subst; allsimpl; cpx; clear h1.
  inversion h2 as [? ? ? ? ? disj2 ? ? norep2 aeq2]; subst; allsimpl; cpx; clear h2.
  allrw @var_ren_nil_l; allrw @lsubst_nil.
  eexists; eexists; dands; try reflexivity; auto.
Qed.

Lemma isprog_sup_iff {o} :
  forall (a b : @NTerm o), isprog (mk_sup a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_eq.
  allrw <- @isprogram_sup_iff; tcsp.
Qed.

Lemma alphaeqc_mkc_sup {o} :
  forall (t : @CTerm o) a u,
    alphaeqc (mkc_sup t a) u
    -> {t' : CTerm
        & {a' : CTerm
        & u = mkc_sup t' a'
        # alphaeqc t t'
        # alphaeqc a a' }}.
Proof.
  introv aeq.
  destruct_cterms; simpl in *.
  unfold alphaeqc in *; simpl in *.
  apply alpha_eq_mk_sup in aeq; exrepnd; subst.
  dup i as j.
  apply isprog_sup_iff in j; repnd.

  exists (mk_ct t' j0) (mk_ct a' j); simpl; dands; auto.
  apply cterm_eq; simpl; auto.
Qed.

Ltac alphaeqc_decompose :=
  match goal with
  | [ H : alphaeqc (mkc_function _ _ _) _ |- _ ] => apply alphaeqc_mkc_function in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_isect    _ _ _) _ |- _ ] => apply alphaeqc_mkc_isect    in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_disect   _ _ _) _ |- _ ] => apply alphaeqc_mkc_disect   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_set      _ _ _) _ |- _ ] => apply alphaeqc_mkc_set      in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_tunion   _ _ _) _ |- _ ] => apply alphaeqc_mkc_tunion   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_product  _ _ _) _ |- _ ] => apply alphaeqc_mkc_product  in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_w        _ _ _) _ |- _ ] => apply alphaeqc_mkc_w        in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_m        _ _ _) _ |- _ ] => apply alphaeqc_mkc_m        in H; exrepnd; try subst

  | [ H : alphaeqc (mkc_free_from_atom  _ _ _) _ |- _ ] => apply alphaeqc_mkc_ffatom    in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_efree_from_atom _ _ _) _ |- _ ] => apply alphaeqc_mkc_effatom   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_equality        _ _ _) _ |- _ ] => apply alphaeqc_mkc_equality  in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_requality       _ _ _) _ |- _ ] => apply alphaeqc_mkc_requality in H; exrepnd; try subst

  | [ H : alphaeqc (mkc_approx          _ _) _ |- _ ] => apply alphaeqc_mkc_approx    in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_cequiv          _ _) _ |- _ ] => apply alphaeqc_mkc_cequiv    in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_texc            _ _) _ |- _ ] => apply alphaeqc_mkc_texc      in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_union           _ _) _ |- _ ] => apply alphaeqc_mkc_union     in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_image           _ _) _ |- _ ] => apply alphaeqc_mkc_image     in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_free_from_atoms _ _) _ |- _ ] => apply alphaeqc_mkc_ffatoms   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_tequality       _ _) _ |- _ ] => apply alphaeqc_mkc_tequality in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_sup             _ _) _ |- _ ] => apply alphaeqc_mkc_sup       in H; exrepnd; try subst

  | [ H : alphaeqc (mkc_partial  _) _ |- _ ] => apply alphaeqc_mkc_partial  in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_mono     _) _ |- _ ] => apply alphaeqc_mkc_mono     in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_admiss   _) _ |- _ ] => apply alphaeqc_mkc_admiss   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_pertype  _) _ |- _ ] => apply alphaeqc_mkc_pertype  in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_ipertype _) _ |- _ ] => apply alphaeqc_mkc_ipertype in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_spertype _) _ |- _ ] => apply alphaeqc_mkc_spertype in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_tuni     _) _ |- _ ] => apply alphaeqc_mkc_tuni     in H; exrepnd; try subst

  | [ H : alphaeqc mkc_base        _ |- _ ] => apply alphaeqc_mkc_base    in H; exrepnd; try subst
  | [ H : alphaeqc mkc_int         _ |- _ ] => apply alphaeqc_mkc_int     in H; exrepnd; try subst
  | [ H : alphaeqc mkc_Nat         _ |- _ ] => apply alphaeqc_mkc_Nat     in H; exrepnd; try subst
  | [ H : alphaeqc mkc_atom        _ |- _ ] => apply alphaeqc_mkc_atom    in H; exrepnd; try subst
  | [ H : alphaeqc mkc_uatom       _ |- _ ] => apply alphaeqc_mkc_uatom   in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_uni _)     _ |- _ ] => apply alphaeqc_mkc_uni     in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_csname _)  _ |- _ ] => apply alphaeqc_mkc_csname  in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_refname _) _ |- _ ] => apply alphaeqc_mkc_refname in H; exrepnd; try subst

  | [ H : alphaeqc (mkc_pw _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => apply alphaeqc_mkc_pw in H; exrepnd; try subst
  | [ H : alphaeqc (mkc_pm _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => apply alphaeqc_mkc_pm in H; exrepnd; try subst
  end.
