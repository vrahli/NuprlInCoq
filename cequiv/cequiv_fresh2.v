(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export csubst_fresh.
Require Export cequiv_fresh.


Definition get_utokens_csub {o} (sub : @CSub o) :=
  flat_map getc_utokens (crange sub).

Lemma get_utokens_csub_as {o} :
  forall (s : @CSub o),
    get_utokens_csub s = get_utokens_sub (csub2sub s).
Proof.
  introv.
  unfold get_utokens_csub, get_utokens_sub, crange, range, csub2sub.
  rw map_map; unfold compose; simpl.
  allrw flat_map_map; unfold compose; simpl; tcsp.
Qed.

Lemma cover_vars_uatom {o} :
  forall (sub : @CSub o), cover_vars mk_uatom sub.
Proof.
  intro; rw @cover_vars_eq; rw subvars_eq; simpl; sp.
Qed.
Hint Resolve cover_vars_uatom : slow.

Lemma respects2_l_alphaeqc_cequivc {o} :
  forall lib, respects2_l alphaeqc (@cequivc o lib).
Proof.
  introv aeq ceq.
  apply (alphaeqc_implies_cequivc lib) in aeq; eauto.
  eapply cequivc_trans;[|eauto]; apply cequivc_sym; auto.
Qed.
Hint Resolve respects2_l_alphaeqc_cequivc : respects.

Lemma respects2_r_alphaeqc_cequivc {o} :
  forall lib, respects2_r alphaeqc (@cequivc o lib).
Proof.
  introv aeq ceq.
  apply (alphaeqc_implies_cequivc lib) in aeq; eauto.
  eapply cequivc_trans;[|eauto]; auto.
Qed.
Hint Resolve respects2_r_alphaeqc_cequivc : respects.

Lemma approx_fresh_subst_gen1 {o} :
  forall lib (t : @NTerm o) v a y,
    !LIn a (get_utokens t)
    -> !LIn a (get_utokens y)
    -> isprog_vars [v] t
    -> isprog y
    -> cequiv lib (subst t v (mk_utoken a)) y
    -> approx lib (mk_fresh v t) (subst t v (mk_utoken a)).
Proof.
  introv niat niay ispt ispy ceq.

  assert (approx lib (mk_fresh v t) (mk_fresh v y)) as apr1.
  { apply howetheorem1; try (apply isprogram_fresh); eauto 3 with slow.
    apply (apso _ _ _ _ [bterm [v] y]); simpl; auto.
    - unfold lblift_sub; simpl; dands; auto.
      introv k; destruct n; try lia; clear k.
      unfold selectbt; simpl.
      unfold blift_sub.
      exists [v] t y; dands; eauto 3 with slow.
      right.
      exists [(v,mk_utoken a)]; simpl.
      dands; auto.
      + allrw @fold_subst.
        apply le_bin_rel_approx1_eauto.
        eapply approx_trans;[apply cequiv_le_approx;eauto|].
        rw @subst_trivial; eauto 3 with slow.
        apply approx_refl; eauto 3 with slow.
      + constructor.
        * apply ut_sub_cons; simpl; dands; eauto 3 with slow.
          unfold isutoken; eexists; eauto.
        * unfold get_utokens_sub; simpl.
          rw disjoint_singleton_r; rw in_app_iff; rw not_over_or.
          dands; auto.
    - apply approx_open_refl.
      apply nt_wf_fresh; eauto 3 with slow.
  }

  eapply approx_trans;[eauto|].
  eapply approx_trans;[apply approx_shadowed_fresh1;eauto 3 with slow|].
  eapply approx_trans;[|apply cequiv_le_approx;apply cequiv_sym;eauto].
  apply approx_refl; eauto 3 with slow.
Qed.

Lemma approx_fresh_subst_gen2 {o} :
  forall lib (t : @NTerm o) v a y,
    !LIn a (get_utokens t)
    -> !LIn a (get_utokens y)
    -> isprog_vars [v] t
    -> isprog y
    -> cequiv lib (subst t v (mk_utoken a)) y
    -> approx lib (subst t v (mk_utoken a)) (mk_fresh v t).
Proof.
  introv niat niay ispt ispy ceq.

  assert (approx lib (mk_fresh v y) (mk_fresh v t)) as apr1.
  { apply howetheorem1; try (apply isprogram_fresh); eauto 3 with slow.
    apply (apso _ _ _ _ [bterm [v] t]); simpl; auto.
    - unfold lblift_sub; simpl; dands; auto.
      introv k; destruct n; try lia; clear k.
      unfold selectbt; simpl.
      unfold blift_sub.
      exists [v] y t; dands; eauto 3 with slow.
      right.
      exists [(v,mk_utoken a)]; simpl.
      dands; auto.
      + allrw @fold_subst.
        apply le_bin_rel_approx1_eauto.
        apply cequiv_sym in ceq.
        eapply approx_trans;[|apply cequiv_le_approx;eauto].
        rw @subst_trivial; eauto 3 with slow.
        apply approx_refl; eauto 3 with slow.
      + constructor.
        * apply ut_sub_cons; simpl; dands; eauto 3 with slow.
          unfold isutoken; eexists; eauto.
        * unfold get_utokens_sub; simpl.
          rw disjoint_singleton_r; rw in_app_iff; rw not_over_or.
          dands; auto.
    - apply approx_open_refl.
      apply nt_wf_fresh; eauto 3 with slow.
  }

  eapply approx_trans;[|eauto].
  eapply approx_trans;[|apply approx_shadowed_fresh2;eauto 3 with slow].
  eapply approx_trans;[apply cequiv_le_approx;eauto|].
  apply approx_refl; eauto 3 with slow.
Qed.

Definition getcv_utokens {o} vs (t : @CVTerm o vs) :=
  get_utokens (get_cvterm vs t).

Lemma cequivc_fresh_subst_gen {o} :
  forall lib v (t : @CVTerm o [v]) a y,
    !LIn a (getcv_utokens [v] t)
    -> !LIn a (getc_utokens y)
    -> cequivc lib (substc (mkc_utoken a) v t) y
    -> cequivc lib (mkc_fresh v t) (substc (mkc_utoken a) v t).
Proof.
  introv niat niay ispc.
  destruct_cterms; allsimpl.
  allunfold @cequivc; allsimpl.
  unfold getcv_utokens in niat; allsimpl.
  unfold getc_utokens in niay; allsimpl.

  constructor.
  - eapply approx_fresh_subst_gen1; eauto.
  - eapply approx_fresh_subst_gen2; eauto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/")
*** End:
*)
