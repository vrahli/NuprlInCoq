(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Import approx_star0.


Definition approx_star_sk {o} lib op (sk1 sk2 : @sosub_kind o) :=
  approx_star_bterm lib op (sk2bterm sk1) (sk2bterm sk2).

Lemma approx_star_sk_if_approx_star_sosub_find {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk1
    -> sosub_find (combine vs sks2) sv = Some sk2
    -> approx_star_sk lib op sk1 sk2.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1, sks2; allsimpl; cpx.
  apply binrel_list_cons in aeq; repnd.
  destruct s, s0; boolvar; cpx.

  - provefalse.
    unfold approx_star_sk in aeq; simpl in aeq.
    inversion aeq as [nvs h]; exrepnd.
    inversion h1; inversion h2; subst.
    destruct n1; f_equal; omega.

  - provefalse.
    unfold approx_star_sk in aeq; simpl in aeq.
    inversion aeq as [nvs h]; exrepnd.
    inversion h1; inversion h2; subst.
    destruct n1; f_equal; omega.

  - apply (IHvs sks1 sks2 sk1 sk2 sv); auto.
Qed.

Lemma approx_star_sk_is_approx_star_bterm {o} :
  forall lib op (b1 b2 : @BTerm o),
    approx_star_bterm lib op b1 b2
    <=> approx_star_sk lib op (bterm2sk b1) (bterm2sk b2).
Proof.
  introv.
  unfold approx_star_sk; simpl.
  destruct b1, b2; simpl; sp.
Qed.

Lemma false_if_approx_star_sk_sosub_find {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk
    -> sosub_find (combine vs sks2) sv = None
    -> False.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  destruct s, s0; boolvar; cpx;
  apply binrel_list_cons in aeq; repnd.

  - unfold approx_star_sk in aeq; simpl in aeq;
    inversion aeq as [nvs h]; exrepnd;
    inversion h1; inversion h2; subst;
    destruct n1; f_equal; try omega.

  - eapply IHvs in f1; eauto.
Qed.

Lemma false_if_approx_star_sk_sosub_find2 {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = None
    -> sosub_find (combine vs sks2) sv = Some sk
    -> False.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  destruct s, s0; boolvar; cpx;
  apply binrel_list_cons in aeq; repnd.

  - unfold approx_star_sk in aeq; simpl in aeq;
    inversion aeq as [nvs h]; exrepnd;
    inversion h1; inversion h2; subst;
    destruct n1; f_equal; try omega.

  - eapply IHvs in f1; eauto.
Qed.

Lemma approx_star_apply_list {o} :
  forall lib ts1 ts2 (t1 t2 : @NTerm o),
    approx_star lib t1 t2
    -> bin_rel_nterm (approx_star lib) ts1 ts2
    -> approx_star lib (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; introv ap brel; destruct ts2; allsimpl; tcsp.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - apply binrel_list_cons in brel; repnd.
    apply IHts1; auto.
    apply approx_star_congruence; auto.
    unfold approx_starbts, lblift_sub; simpl; dands; auto.
    introv k.
    destruct n0.
    + unfold selectbt; simpl; auto.
      apply blift_sub_nobnd_congr; auto.
    + destruct n0; try omega.
      unfold selectbt; simpl; auto.
      apply blift_sub_nobnd_congr; auto.
Qed.

Lemma sosub_filter_if_approx_star_sk {o} :
  forall lib op vs (sks1 sks2 : list (@sosub_kind o)) (l : list sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> {vs' : list NVar
        & {sks1' : list sosub_kind
        & {sks2' : list sosub_kind
           & sosub_filter (combine vs sks1) l = combine vs' sks1'
           # sosub_filter (combine vs sks2) l = combine vs' sks2'
           # bin_rel_sk (approx_star_sk lib op) sks1' sks2'
           # subset (combine sks1' sks2') (combine sks1 sks2)
           # subset vs' vs
           # subset sks1' sks1
           # subset sks2' sks2
           # length vs' = length sks1'
           # length vs' = length sks2'
           # sodom (combine vs' sks1') = remove_so_vars l (sodom (combine vs sks1))
           # sodom (combine vs' sks2') = remove_so_vars l (sodom (combine vs sks2)) }}}.
Proof.
  induction vs; destruct sks1, sks2; introv len1 len2 ap; allsimpl; cpx.
  - exists ([] : list NVar) ([] : list (@sosub_kind o)) ([] : list (@sosub_kind o));
      sp; rw remove_so_vars_nil_r; rw combine_nil; sp.
  - destruct s, s0; boolvar; tcsp.

    + apply binrel_list_cons in ap; repnd.
      pose proof (IHvs sks1 sks2 l len1 len2 ap0) as h; exrepd.
      exists vs' sks1' sks2'; dands; auto;
      try (complete (apply subset_cons1; auto));
      try (complete (rw remove_so_vars_cons_r; boolvar; tcsp)).

    + provefalse.
      apply binrel_list_cons in ap; repnd.
      inversion ap as [nvs h]; exrepnd; allsimpl.
      inversion h1; subst.
      inversion h2; subst.
      assert (length l1 = length l0) as x by omega.
      rw x in n1; sp.

    + provefalse.
      apply binrel_list_cons in ap; repnd.
      inversion ap as [nvs h]; exrepnd; allsimpl.
      inversion h1; subst.
      inversion h2; subst.
      assert (length l1 = length l0) as x by omega.
      rw x in l2; sp.

    + apply binrel_list_cons in ap; repnd.
      pose proof (IHvs sks1 sks2 l len1 len2 ap0) as h; exrepd.
      exists (a :: vs') (sosk l0 n :: sks1') (sosk l1 n0 :: sks2');
        simpl; dands; tcsp;
        try (complete (apply eq_cons; auto));
        try (complete (apply subset_cons2; auto));
        try (complete (rw remove_so_vars_cons_r; boolvar; tcsp; apply eq_cons; auto)).
      apply binrel_list_cons; sp.
Qed.

(*
Lemma sosub_aux_approx_star_congr {p} :
  forall lib opr (t : @SOTerm p) (vs : list NVar) (ts1 ts2 : list sosub_kind),
    let sub1 := combine vs ts1 in
    let sub2 := combine vs ts2 in
    wf_soterm t
    -> length vs = length ts1
    -> length vs = length ts2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t)
    (* These 2 disjoints we can always assume because they are ensured by sosub *)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> bin_rel_sk (approx_star_sk lib opr) ts1 ts2
    -> approx_star lib (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind1s t as [v ts ind|op lbt ind] Case; simpl;
  introv wf len1 len2 d1 d2 d3 d4 cov1 cov2 ask.

  - Case "sovar".
    remember (sosub_find (combine vs ts1) (v, length ts)) as o;
      destruct o; symmetry in Heqo;
      remember (sosub_find (combine vs ts2) (v, length ts)) as q;
      destruct q; symmetry in Heqq;
      try (destruct s); try (destruct s0).

    + pose proof (apply_bterm_approx_star_congr
                    lib opr (bterm l n) (bterm l0 n0)
                    (map (sosub_aux (combine vs ts1)) ts)
                    (map (sosub_aux (combine vs ts2)) ts)
                 ) as h.
      repeat (autodimp h hyp).

      * apply approx_star_sk_is_approx_star_bterm; simpl.
        eapply approx_star_sk_if_approx_star_sosub_find;
          [|idtac|exact ask|exact Heqo|exact Heqq]; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux (combine vs ts1) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux (combine vs ts2) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n1 ts default_soterm) as t.
        pose proof (nth_in _ n1 ts default_soterm i) as j.
        rw <- Heqt in j; clear Heqt.

        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub (combine vs ts1))
                         (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub (combine vs ts2))
                         (flat_map fovars ts))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        apply ind; auto.

        { rw disjoint_flat_map_r in d1; apply d1; auto. }

        { rw disjoint_flat_map_r in d2; apply d2; auto. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

      * allrw map_length; unfold num_bvars; simpl; auto.
        allapply @sosub_find_some; sp.

      * allrw map_length; unfold num_bvars; simpl; auto.

      * unfold apply_bterm in h; simpl in h.
        applydup @sosub_find_some in Heqo; repnd.
        applydup @sosub_find_some in Heqq; repnd.
        allrw @cover_so_vars_sovar; repnd.
        revert h.
        change_to_lsubst_aux4; auto; clear h;
        try (complete (allrw disjoint_cons_r; repnd;
                       rw flat_map_map; unfold compose;
                       eapply disjoint_bound_vars_prop3; eauto)).

    + eapply false_if_approx_star_sk_sosub_find in Heqo; eauto; sp.

    + eapply false_if_approx_star_sk_sosub_find2 in Heqo; eauto; sp.

    + apply approx_star_apply_list; auto.

      * apply approx_star_refl; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux (combine vs ts1) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux (combine vs ts2) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n ts default_soterm) as t.
        pose proof (nth_in _ n ts default_soterm i) as j.
        rw <- Heqt in j; clear Heqt.

        rw disjoint_flat_map_r in d1.
        rw disjoint_flat_map_r in d2.
        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub (combine vs ts1))
                         (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub (combine vs ts2))
                         (flat_map fovars ts))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        apply ind; auto.

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

  - Case "soterm".
    allrw @wf_soterm_iff; repnd.

    apply approx_star_congruence;
      [|rw map_map; unfold compose; rw <- wf0;
        apply eq_maps; introv k; destruct x;
        unfold num_bvars; simpl; auto].

    unfold approx_starbts, lblift; allrw map_length; dands; auto.
    introv i.
    unfold selectbt.

    assert (@default_bt p = sosub_b_aux (combine vs ts1) default_sobterm)
      as e by auto.
    rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_bt p).
    assert (@default_bt p = sosub_b_aux (combine vs ts2) default_sobterm)
      as e by auto.
    rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_bt p).
    remember (nth n lbt default_sobterm) as bt.
    pose proof (nth_in _ n lbt default_sobterm i) as j.
    rw <- Heqbt in j; clear Heqbt.

    rw disjoint_flat_map_r in d1.
    rw disjoint_flat_map_r in d2.
    allrw disjoint_app_r; repnd.

    destruct bt; simpl.

    pose proof (sosub_filter_if_approx_star_sk lib vs ts1 ts2 (vars2sovars l)) as h.
    repeat (autodimp h hyp); exrepnd.

    rw h1; rw h2.

    unfold blift.
    exists l (sosub_aux (combine vs' sks1') s) (sosub_aux (combine vs' sks2') s).
    dands; auto.
    eapply ind; eauto.

    + applydup d1 in j as k; simpl in k.
      rw disjoint_app_r in k; repnd.
      rw @free_vars_sosub_combine; auto.
      rw @free_vars_sosub_combine in k; auto.
      rw disjoint_flat_map_l; introv z.
      rw disjoint_flat_map_l in k.
      apply h6 in z.
      applydup k in z; auto.

    + applydup d2 in j as k; simpl in k.
      rw disjoint_app_r in k; repnd.
      rw @free_vars_sosub_combine; auto.
      rw @free_vars_sosub_combine in k; auto.
      rw disjoint_flat_map_l; introv z.
      rw disjoint_flat_map_l in k.
      apply h7 in z.
      applydup k in z; auto.

    + rw disjoint_app_r; dands.

      * rw @bound_vars_sosub_combine; auto.
        rw @free_vars_sosub_combine; auto.
        rw @bound_vars_sosub_combine in d0; auto.
        rw @free_vars_sosub_combine in d0; auto.
        rw disjoint_flat_map_r; introv z.
        rw disjoint_flat_map_l; introv y.
        rw disjoint_flat_map_r in d0.
        applydup h6 in z.
        apply d0 in z0.
        rw disjoint_flat_map_l in z0.
        applydup h6 in y.
        apply z0 in y0; auto.

      * rw @bound_vars_sosub_combine; auto.
        rw disjoint_flat_map_r in d3.
        apply d3 in j; simpl in j; rw disjoint_app_r in j; repnd.
        rw @bound_vars_sosub_combine in j; auto.
        rw disjoint_flat_map_l in j.
        rw disjoint_flat_map_l; introv z.
        apply h6 in z.
        apply j in z; auto.

    + rw disjoint_app_r; dands.

      * rw @bound_vars_sosub_combine; auto.
        rw @free_vars_sosub_combine; auto.
        rw @bound_vars_sosub_combine in d5; auto.
        rw @free_vars_sosub_combine in d5; auto.
        rw disjoint_flat_map_r; introv z.
        rw disjoint_flat_map_l; introv y.
        rw disjoint_flat_map_r in d5.
        applydup h7 in z.
        apply d5 in z0.
        rw disjoint_flat_map_l in z0.
        applydup h7 in y.
        apply z0 in y0; auto.

      * rw @bound_vars_sosub_combine; auto.
        rw disjoint_flat_map_r in d4.
        apply d4 in j; simpl in j; rw disjoint_app_r in j; repnd.
        rw @bound_vars_sosub_combine in j; auto.
        rw disjoint_flat_map_l in j.
        rw disjoint_flat_map_l; introv z.
        apply h7 in z.
        apply j in z; auto.

    + unfold cover_so_vars.
      rw h10.
      rw filter_out_fo_vars_remove_fo_vars; auto.
      rw @cover_so_vars_soterm in cov1; eapply cov1; eauto.

    + unfold cover_so_vars.
      rw h0.
      rw filter_out_fo_vars_remove_fo_vars; auto.
      rw @cover_so_vars_soterm in cov2; eapply cov2; eauto.
Qed.
*)

Definition approx_star_sosub {o} lib op (sub1 sub2 : @SOSub o) :=
  bin_rel_sk (approx_star_sk lib op) (so_range sub1) (so_range sub2).

Lemma approx_star_sosub_implies_same_length {o} :
  forall lib op (sub1 sub2 : @SOSub o),
    approx_star_sosub lib op sub1 sub2 -> length sub1 = length sub2.
Proof.
  introv ap.
  unfold approx_star_sosub, bin_rel_sk, binrel_list in ap; repnd.
  allrw @length_so_range; auto.
Qed.

(*
Lemma sosub_aux_approx_star_congr2 {o} :
  forall lib (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    wf_soterm t
    -> sodom sub1 = sodom sub2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> approx_star_sosub lib sub1 sub2
    -> approx_star lib (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  introv wf e disj1 disj2 disj3 disj4 cov1 cov2 ap.
  pose proof (sosub_aux_approx_star_congr
                lib t
                (so_dom sub1) (so_range sub1) (so_range sub2)) as h.

  allrw <- @sosub_as_combine; allsimpl.
  applydup @eq_sodoms_implies_eq_so_doms in e as e'.

  repeat (autodimp h hyp).
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw e'; rw @length_so_dom; rw @length_so_range; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e' in h; rw <- @sosub_as_combine in h; auto.
Qed.
*)

Lemma alphaeq_sosub_kind_if_alphaeq_sosub_find2 {o} :
  forall (sub1 sub2 : @SOSub o) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    alphaeq_sosub sub1 sub2
    -> sosub_find sub1 sv = Some sk1
    -> sosub_find sub2 sv = Some sk2
    -> alphaeq_sk sk1 sk2.
Proof.
  introv aeq f1 f2.
  applydup @alphaeq_sosub_implies_eq_sodoms in aeq as eqdoms.
  applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
  apply (alphaeq_sosub_kind_if_alphaeq_sosub_find
           (so_dom sub1) (so_range sub1) (so_range sub2) _ _ sv); auto.
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw eqdoms'; rw @length_so_dom; rw @length_so_range; auto.
  - apply alphaeq_sosub_implies_alphaeq_sk; auto.
  - rw <- @sosub_as_combine; auto.
  - rw eqdoms'; rw <- @sosub_as_combine; auto.
Qed.

Lemma approx_star_sk_if_approx_star_sosub_find2 {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = Some sk1
    -> sosub_find sub2 sv = Some sk2
    -> approx_star_sk lib op sk1 sk2.
Proof.
  introv e ap f1 f2.
  applydup @approx_star_sosub_implies_same_length in ap.
  apply (approx_star_sk_if_approx_star_sosub_find
           lib op (so_dom sub1) (so_range sub1) (so_range sub2) _ _ sv); auto.

  - rw @length_so_dom; rw @length_so_range; auto.
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma false_if_approx_star_sosub_find {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = Some sk
    -> sosub_find sub2 sv = None
    -> False.
Proof.
  introv e ap f1 f2.
  pose proof (false_if_approx_star_sk_sosub_find
                lib op (so_dom sub1) (so_range sub1) (so_range sub2)
                sk sv) as h.
  allrw @length_so_dom.
  allrw @length_so_range.
  applydup @approx_star_sosub_implies_same_length in ap.
  repeat (autodimp h hyp).
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma false_if_approx_star_sosub_find2 {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = None
    -> sosub_find sub2 sv = Some sk
    -> False.
Proof.
  introv e ap f1 f2.
  pose proof (false_if_approx_star_sk_sosub_find2
                lib op (so_dom sub1) (so_range sub1) (so_range sub2)
                sk sv) as h.
  allrw @length_so_dom.
  allrw @length_so_range.
  applydup @approx_star_sosub_implies_same_length in ap.
  repeat (autodimp h hyp).
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma eq_maps_combine :
  forall (A B C : tuniv)
         (f : A -> B) (g : C -> B)
         (la : list A) (lc : list C),
    length la = length lc
    -> (forall a c, LIn (a,c) (combine la lc) -> f a = g c)
    -> map f la = map g lc.
Proof.
  induction la; destruct lc; introv len imp; allsimpl; auto; cpx.
  f_equal; sp.
Qed.

Lemma num_bvars_sosub_b_aux {o} :
  forall (b : @SOBTerm o) sub,
    num_bvars (sosub_b_aux sub b) = num_sobvars b.
Proof.
  introv.
  destruct b; simpl; unfold num_bvars; simpl; auto.
Qed.

Lemma so_alphaeq_vs_implies_eq_num_sobvars {o} :
  forall (a b : @SOBTerm o) vs,
    so_alphaeqbt_vs vs a b
    -> num_sobvars a = num_sobvars b.
Proof.
  introv aeq; inversion aeq; subst; simpl; omega.
Qed.

Lemma approx_starbts_map {o} :
  forall lib A op (l1 l2 : list A) (f1 f2 : A -> @BTerm o),
    length l1 = length l2
    -> (forall a1 a2,
          LIn (a1,a2) (combine l1 l2)
          -> approx_star_bterm lib op (f1 a1) (f2 a2))
    -> approx_starbts lib op (map f1 l1) (map f2 l2).
Proof.
  induction l1; destruct l2; introv len imp; allsimpl; auto; cpx.
  - unfold approx_starbts, lblift_sub; simpl; sp.
  - rw @approx_starbts_cons; dands; auto.
Qed.

Lemma filter_out_fo_vars_swap_fo_vars :
  forall vs1 vs2 vs,
    filter_out_fo_vars (swap_fo_vars (mk_swapping vs1 vs2) vs)
    = filter_out_fo_vars vs.
Proof.
  induction vs; introv; simpl; auto.
  destruct a; destruct n0; simpl; auto.
  f_equal; auto.
Qed.

Lemma cover_so_vars_so_swap {o} :
  forall (t : @SOTerm o) sub vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> (cover_so_vars (so_swap (mk_swapping vs1 vs2) t) sub
        <=> cover_so_vars t sub).
Proof.
  introv norep disj.
  unfold cover_so_vars.
  rw @so_free_vars_so_swap; auto.
  rw filter_out_fo_vars_swap_fo_vars; sp.
Qed.

Lemma cover_so_vars_sosub_filter_vars2sovars {o} :
  forall (t : @SOTerm o) sub vs,
    cover_so_vars t (sosub_filter sub (vars2sovars vs))
    <=> cover_so_vars t sub.
Proof.
  introv.
  unfold cover_so_vars.
  rw @sodom_sosub_filter.
  rw filter_out_fo_vars_remove_fo_vars; sp.
Qed.

Lemma sosub_filter_if_not_in_dom {o} :
  forall t (sub : @SOSub o) vs,
    disjoint (sodom sub) vs
    -> sosub_aux (sosub_filter sub vs) t = sosub_aux sub t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv disj; allsimpl; auto.

  - Case "sovar".
    destruct (in_deq sovar_sig sovar_sig_dec (v,length ts) vs) as [i|i].

    + rw disjoint_sym in disj; applydup disj in i.
      remember (sosub_find (sosub_filter sub vs) (v,length ts)) as f1.
      remember (sosub_find sub (v,length ts)) as f2.
      symmetry in Heqf1; symmetry in Heqf2.
      destruct f1; destruct f2.

      * destruct s0.
        apply sosub_find_some in Heqf2; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf2 in Heqf0; sp.

      * destruct s.
        apply sosub_find_some in Heqf1; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf1 in Heqf0.
        rw @sodom_sosub_filter in Heqf0.
        rw in_remove_so_vars in Heqf0; sp.

      * destruct s.
        apply sosub_find_some in Heqf2; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf2 in Heqf0; sp.

      * f_equal.
        apply eq_maps; introv k.
        apply ind; auto.
        rw disjoint_sym; auto.

    + rw @sosub_find_sosub_filter; auto.
      remember (sosub_find sub (v,length ts)) as f; symmetry in Heqf; destruct f.

      * destruct s.
        f_equal; f_equal.
        apply eq_maps; introv k.
        apply ind; auto.

      * f_equal.
        apply eq_maps; introv k.
        apply ind; auto.

  - Case "soterm".
    f_equal.
    apply eq_maps; introv i; destruct x as [l t]; simpl.
    f_equal.
    rw @sosub_filter_swap.
    eapply ind; eauto.
    rw @sodom_sosub_filter.
    introv a b.
    rw disjoint_sym in disj; apply disj in b.
    allrw in_remove_so_vars; sp.
Qed.

Lemma if_disjoint_sovars2vars :
  forall vs1 vs2,
    disjoint (sovars2vars vs1) (sovars2vars vs2)
    -> disjoint vs1 vs2.
Proof.
  introv disj a b.
  destruct t.
  assert (LIn n (sovars2vars vs1)) as h by (apply in_sovars2vars; eexists; eauto).
  apply disj in h.
  rw in_sovars2vars in h.
  destruct h; eexists; eauto.
Qed.

Lemma sovars2vars_vars2sovars :
  forall vs, sovars2vars (vars2sovars vs) = vs.
Proof.
  induction vs; simpl; allrw; sp.
Qed.

Lemma sovars2vars_sodom_is_so_dom {o} :
  forall (sub : @SOSub o), sovars2vars (sodom sub) = so_dom sub.
Proof.
  induction sub; simpl; auto.
  destruct a; destruct s; simpl; allrw; sp.
Qed.

Lemma in_0_vars2sovars :
  forall v vs, LIn (v, 0) (vars2sovars vs) <=> LIn v vs.
Proof.
  introv; rw in_map_iff; split; intro k; exrepnd; allunfold var2sovar; cpx.
  eexists; eauto.
Qed.

Lemma implies_disjoint_allvars {o} :
  forall (t : @NTerm o) vs,
    disjoint (free_vars t) vs
    -> disjoint (bound_vars t) vs
    -> disjoint (allvars t) vs.
Proof.
  introv d1 d2.
  apply disjoint_sym; apply disjoint_to_allvars_r.
  rw disjoint_app_r; dands; apply disjoint_sym; auto.
Qed.

Lemma sosub_filter_r {o} :
  forall (sub : @SOSub o) l1 l2,
    sosub_filter (sosub_filter sub l1) l2
    = sosub_filter sub (l1 ++ l2).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; simpl; boolvar; allrw in_app_iff; tcsp;
  allrw not_over_or; repnd; tcsp; allsimpl; boolvar; tcsp.
  rw IHsub; auto.
Qed.

Lemma vars2sovars_app :
  forall vs1 vs2,
    vars2sovars (vs1 ++ vs2) = vars2sovars vs1 ++ vars2sovars vs2.
Proof.
  introv; unfold vars2sovars; rw map_app; auto.
Qed.

Lemma sosub_aux_sosub_filter_so_swap {o} :
  forall (t : @SOTerm o) sub vs1 vs2 vs,
    disjoint vs1 (free_vars_sosub sub)
    -> disjoint vs1 (bound_vars_sosub sub)
    -> disjoint vs2 (free_vars_sosub sub)
    -> disjoint vs2 (bound_vars_sosub sub)
    -> disjoint vs2 (all_fo_vars t)
    -> disjoint vs1 vs2
    -> disjoint vs vs2
    -> no_repeats vs2
    -> cover_so_vars t sub
    -> subvars vs1 vs
    -> length vs1 = length vs2
    -> sosub_aux (sosub_filter sub (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs)))
                 (so_swap (mk_swapping vs1 vs2) t)
       = cswap (mk_swapping vs1 vs2)
               (sosub_aux (sosub_filter sub (vars2sovars vs)) t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  introv norep cov sv len; allsimpl; auto.

  - Case "sovar".
    destruct (in_deq sovar_sig sovar_sig_dec (v,length ts) (vars2sovars vs)) as [i|i].

    + rw in_map_iff in i; exrepnd; destruct a; allsimpl; allunfold var2sovar; cpx.
      destruct ts; allsimpl; cpx; GC; boolvar; cpx; GC; allsimpl.
      allrw disjoint_singleton_r.

      remember (sosub_find (sosub_filter sub (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs)))
                           (swapvar (mk_swapping vs1 vs2) (nvar v0), 0)) as f1.
      symmetry in Heqf1; destruct f1.

      * destruct s; apply sosub_find_some in Heqf1; repnd.
        destruct l; allsimpl; cpx; GC.
        apply in_sosub_filter in Heqf0; repnd; allsimpl.
        destruct Heqf0.
        rw in_map_iff; unfold var2sovar.
        exists (swapvar (mk_swapping vs1 vs2) (nvar v0)); dands; auto.
        apply in_swapbvars; eexists; eauto.

      * remember (sosub_find (sosub_filter sub (vars2sovars vs))
                             (nvar v0, 0)) as f2.
        symmetry in Heqf2; destruct f2; simpl; auto.

        destruct s; apply sosub_find_some in Heqf2; repnd.
        destruct l; allsimpl; cpx; GC.
        apply in_sosub_filter in Heqf0; allsimpl; repnd.
        destruct Heqf0.
        rw in_map_iff; unfold var2sovar.
        exists (nvar v0); sp.

    + rw @sosub_find_sosub_filter; auto.
      allrw @cover_so_vars_sovar; repnd.
      allrw disjoint_cons_r; repnd.

      boolvar.

      * destruct ts; allsimpl; cpx; GC.
        allrw in_0_vars2sovars.
        rw @sosub_find_sosub_filter;
          [|rw in_0_vars2sovars;auto; rw in_swapbvars; intro k; exrepnd;
            apply swapvars_eq in k0; subst; complete sp].

        destruct (in_deq NVar deq_nvar v vs1) as [j|j];
          [rw subvars_prop in sv; apply sv in j; complete sp|].
        rw swapvar_not_in;auto.

        remember (sosub_find sub (v,0)) as f;
          symmetry in Heqf; destruct f; allsimpl; auto.

        { destruct s; simpl.
          apply sosub_find_some in Heqf; repnd.
          destruct l; allsimpl; cpx; GC.
          allrw @lsubst_aux_nil.
          rw disjoint_flat_map_r in disj1; applydup disj1 in Heqf0 as h1.
          rw disjoint_flat_map_r in disj3; applydup disj3 in Heqf0 as h2.
          rw disjoint_flat_map_r in disj2; applydup disj2 in Heqf0 as h3.
          rw disjoint_flat_map_r in disj4; applydup disj4 in Heqf0 as h4.
          allsimpl.
          allrw remove_nvars_nil_l.
          rw @cswap_trivial; auto; apply implies_disjoint_allvars; eauto with slow. }

        { rw swapvar_not_in; auto. }

      * autodimp cov0 hyp;[destruct ts; allsimpl; complete cpx|].
        simpl; rw map_length.

        rw @sosub_find_sosub_filter;
          [|intro k; rw in_map_iff in k; exrepnd; allunfold var2sovar; cpx;
            destruct ts; allsimpl; complete cpx].

        remember (sosub_find sub (v, length ts)) as f;
          symmetry in Heqf; destruct f;[|apply sosub_find_none in Heqf; complete sp].
        destruct s; simpl.
        allrw map_map; unfold compose.
        rw @lsubst_aux_cswap_cswap; auto.
        applydup @sosub_find_some in Heqf; repnd.

        dup disj1 as d1; dup disj2 as d2; dup disj3 as d3; dup disj4 as d4.
        rw disjoint_flat_map_r in disj1.
        rw disjoint_flat_map_r in disj2.
        rw disjoint_flat_map_r in disj3.
        rw disjoint_flat_map_r in disj4.
        applydup disj1 in Heqf1 as h1.
        applydup disj2 in Heqf1 as h2.
        applydup disj3 in Heqf1 as h3.
        applydup disj4 in Heqf1 as h4.
        allsimpl.
        allrw disjoint_app_r; repnd.

        assert (disjoint vs1 (free_vars n0))
          as k1 by (introv a b; applydup h0 in a; applydup h1 in a;
                    allrw in_remove_nvars; sp).

        assert (disjoint vs2 (free_vars n0))
          as k2 by (introv a b; applydup h5 in a; applydup h3 in a;
                    allrw in_remove_nvars; sp).

        rw @cswap_trivial;
          try (complete (apply implies_disjoint_allvars; eauto with slow));[].

        rw @cswap_sub_combine.
        rw (swapbvars_trivial vs1 vs2 l); eauto with slow;[].

        f_equal; f_equal.
        allrw map_map; unfold compose.
        apply eq_maps; introv j.
        apply ind; auto.

        rw disjoint_flat_map_r in disj0; apply disj0; sp.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t].
    simpl.
    f_equal.
    allrw @sosub_filter_r.
    allrw <- vars2sovars_app.
    allrw <- swapbvars_app.

    rw disjoint_flat_map_r in disj5.
    applydup disj5 in i as j; simpl in j; rw disjoint_app_r in j; repnd.

    allrw @cover_so_vars_soterm.
    applydup cov in i as c.

    eapply ind; eauto.

    + rw disjoint_app_l; dands; eauto with slow.

    + apply subvars_app_weak_l; auto.
Qed.

Lemma subvars_swpbvars :
  forall vs vs1 vs2,
    subvars vs vs1
    -> disjoint vs1 vs2
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> subvars (swapbvars (mk_swapping vs1 vs2) vs) vs2.
Proof.
  introv sv disj norep len.
  rw subvars_prop; introv i.
  rw in_swapbvars in i; exrepnd; subst.
  apply swapvar_implies3; auto.
  rw subvars_prop in sv; apply sv; auto.
Qed.

Lemma btchange_alpha_cswap {o} :
  forall (t : @NTerm o) l1 l2,
    length l1 = length l2
    -> no_repeats l2
    -> disjoint l2 (allvars t)
    -> disjoint l1 l2
    -> alpha_eq_bterm (bterm l1 t) (bterm l2 (cswap (mk_swapping l1 l2) t)).
Proof.
  introv len norep disj1 disj2.
  apply alphaeqbt_eq.
  pose proof (fresh_vars
                (length l1)
                (l1 ++ l2 ++ allvars t ++ allvars (cswap (mk_swapping l1 l2) t)))
    as fv; exrepnd.

  apply (aeqbt [] lvn); auto; try omega.

  rw @cswap_cswap.
  rw mk_swapping_app; auto.
  allrw disjoint_app_r; repnd.
  rw @cswap_disj_chain; auto; try omega;
  allrw disjoint_app_r; dands; eauto with slow.
  apply alphaeq_refl.
Qed.

(*
Lemma approx_star_sk_trans {o} :
  forall lib (sk1 sk2 sk3 : @sosub_kind o),
    approx_star_sk lib sk1 sk2
    -> approx_star_sk lib sk2 sk3
    -> approx_star_sk lib sk1 sk3.
Proof.
  introv ap1 ap2.
  allunfold @approx_star_sk.
  destruct sk1, sk2, sk3; allsimpl.
  allunfold @approx_star_bterm.
  allunfold @blift; exrepnd.

  pose proof (fresh_vars
                (length l)
                (l
                   ++ lv0
                   ++ l0
                   ++ lv
                   ++ l1
                   ++ all_vars n
                   ++ all_vars n0
                   ++ all_vars n1
                   ++ all_vars nt0
                   ++ all_vars nt1
                   ++ all_vars nt2
                   ++ all_vars nt3)) as h; exrepnd.

  applydup @alphaeqbt_numbvars in ap5 as len1; unfold num_bvars in len1; simpl in len1.
  applydup @alphaeqbt_numbvars in ap4 as len2; unfold num_bvars in len2; simpl in len2.
  applydup @alphaeqbt_numbvars in ap3 as len3; unfold num_bvars in len3; simpl in len3.
  applydup @alphaeqbt_numbvars in ap0 as len4; unfold num_bvars in len4; simpl in len4.

  apply alphaeq_bterm3_if with (lva := []) in ap5.
  apply alphaeq_bterm3_if with (lva := []) in ap4.
  apply alphaeq_bterm3_if with (lva := []) in ap3.
  apply alphaeq_bterm3_if with (lva := []) in ap0.

  allrw disjoint_app_r; repnd.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap5; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap5.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap4; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap4.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap3; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap3.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap0; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap0.

Abort.
*)

Lemma approx_star_sosub_cons {o} :
  forall lib op v1 v2 sk1 sk2 (sub1 sub2 : @SOSub o),
    approx_star_sosub lib op ((v1,sk1) :: sub1) ((v2,sk2) :: sub2)
    <=> (approx_star_sk lib op sk1 sk2 # approx_star_sosub lib op sub1 sub2).
Proof.
  introv.
  unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl.
  allrw @length_so_range.
  split; intro k; repnd; dands; auto; cpx.
  - pose proof (k 0) as h; autodimp h hyp; omega.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; omega.
  - introv i.
    destruct n; cpx.
Qed.

Lemma approx_star_sk_alphaeq_l {o} :
  forall lib op (sk1 sk2 sk3 : @sosub_kind o),
    approx_star_sk lib op sk1 sk2
    -> alphaeq_sk sk2 sk3
    -> approx_star_sk lib op sk1 sk3.
Proof.
  introv ap aeq.
  allunfold @approx_star_sk.
  allunfold @alphaeq_sk.
  allrw @alphaeqbt_eq.
  destruct sk1 as [l1 t1], sk2 as [l2 t2], sk3 as [l3 t3]; allsimpl.
  eapply approx_star_bterm_alpha_fun_r; eauto.
Qed.

Lemma approx_star_sk_alphaeq_r {o} :
  forall lib op (sk1 sk2 sk3 : @sosub_kind o),
    alphaeq_sk sk1 sk2
    -> approx_star_sk lib op sk2 sk3
    -> approx_star_sk lib op sk1 sk3.
Proof.
  introv aeq ap.
  allunfold @approx_star_sk.
  allunfold @alphaeq_sk.
  allrw @alphaeqbt_eq.
  destruct sk1 as [l1 t1], sk2 as [l2 t2], sk3 as [l3 t3]; allsimpl.
  eapply approx_star_bterm_alpha_fun_l; eauto.
Qed.

Lemma approx_star_sosub_alphaeq_l {o} :
  forall lib op (sub1 sub2 sub3 : @SOSub o),
    approx_star_sosub lib op sub1 sub2
    -> alphaeq_sosub sub2 sub3
    -> approx_star_sosub lib op sub1 sub3.
Proof.
  induction sub1; destruct sub2; destruct sub3; introv ap aeq; auto;
  try (complete (inversion ap; allsimpl; cpx));
  try (complete (inversion aeq)).

  destruct p; destruct p0; destruct a.
  inversion aeq; subst; clear aeq.
  apply @approx_star_sosub_cons in ap; repnd.
  apply @approx_star_sosub_cons.

  dands.

  - eapply approx_star_sk_alphaeq_l; eauto.

  - eapply IHsub1; eauto.
Qed.

Lemma approx_star_sosub_alphaeq_r {o} :
  forall lib op (sub1 sub2 sub3 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> approx_star_sosub lib op sub2 sub3
    -> approx_star_sosub lib op sub1 sub3.
Proof.
  induction sub1; destruct sub2; destruct sub3; introv aeq ap; auto;
  try (complete (inversion ap; allsimpl; cpx));
  try (complete (inversion aeq)).

  destruct p; destruct p0.
  inversion aeq; subst; clear aeq.
  allapply @approx_star_sosub_cons; repnd.
  apply @approx_star_sosub_cons; repnd.

  dands.

  - eapply approx_star_sk_alphaeq_r; eauto.

  - eapply IHsub1; eauto.
Qed.

Lemma so_alphaeq_vs_preserves_wf {o} :
  forall (t1 t2 : @SOTerm o) vs,
    so_alphaeq_vs vs t1 t2
    -> wf_soterm t1
    -> wf_soterm t2.
Proof.
  introv aeq wf.
  eapply wf_soterm_so_alphaeq; [|eauto].
  eapply so_alphaeq_exists; eauto.
Qed.

Lemma approx_starbts_implies_approx_star_sosub {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)) vars,
    approx_starbts lib op bs1 bs2
    -> approx_star_sosub lib op (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv ap; allsimpl; auto;
  try (complete (inversion ap; allsimpl; cpx)).
  - unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - destruct s; unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - rw @approx_starbts_cons in ap; repnd.
    destruct s; destruct a, b; simpl; boolvar; simpl; tcsp.
    + apply approx_star_sosub_cons; dands; auto.
    + inversion ap0 as [vs x]; exrepnd.
      inversion x2; subst.
      inversion x1; subst.
      provefalse.
      destruct n3; omega.
    + inversion ap0 as [vs x]; exrepnd.
      inversion x2; subst.
      inversion x1; subst.
      provefalse.
      destruct n3; omega.
    + unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
Qed.

Lemma sosub_aux_approx_star_congr_al {p} :
  forall lib (t1 t2 : @SOTerm p) (sub1 sub2 : SOSub) opr,
    wf_soterm t1
    -> wf_soterm t2
    -> so_alphaeq t1 t2
    -> sodom sub1 = sodom sub2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t1)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t2)
    (* These 2 disjoints we can always assume because they are ensured by sosub *)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t1)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t2)
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> opr <> NCan NFresh
    -> approx_star_sosub lib opr sub1 sub2
    -> approx_star lib (sosub_aux sub1 t1) (sosub_aux sub2 t2).
Proof.
  soterm_ind1s t1 as [v ts ind| |op lbt ind] Case; simpl;
  introv wf1 wf2 aeq eqdoms d1 d2 d3 d4 cov1 cov2; introv d ap.

  - Case "sovar".
    applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
    inversion aeq as [? ? ? len imp| |]; subst; clear aeq; allsimpl.
    remember (sosub_find sub1 (v, length ts)) as o;
      destruct o; symmetry in Heqo;
      remember (sosub_find sub2 (v, length ts2)) as q;
      destruct q; symmetry in Heqq;
      try (destruct s); try (destruct s0).

    + pose proof (apply_bterm_approx_star_congr
                    lib opr (bterm l n) (bterm l0 n0)
                    (map (sosub_aux sub1) ts)
                    (map (sosub_aux sub2) ts2)
                 ) as h.
      repeat (autodimp h hyp); try (complete (intro xxx; ginv)).

      * apply approx_star_sk_is_approx_star_bterm; simpl.
        rw <- len in Heqq.
        eapply approx_star_sk_if_approx_star_sosub_find2;
          [exact eqdoms'|exact ap|exact Heqo|exact Heqq].

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux sub1 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux sub2 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n1 ts default_soterm) as t1.
        pose proof (nth_in _ n1 ts default_soterm i) as j1.
        remember (nth n1 ts2 default_soterm) as t2.
        dup i as i'; rw len in i'.
        pose proof (nth_in _ n1 ts2 default_soterm i') as j2.
        pose proof (imp t1 t2) as a;
          autodimp a hyp;[subst; apply in_nth_combine; complete auto|].
        rw <- Heqt1 in j1; clear Heqt1.
        rw <- Heqt2 in j2; clear Heqt2.

        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub sub1) (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub sub2) (flat_map fovars ts2))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        eapply ind; eauto.

        { rw disjoint_flat_map_r in d1; apply d1; auto. }

        { rw disjoint_flat_map_r in d2; apply d2; auto. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

      * allrw map_length; unfold num_bvars; simpl; auto.
        allapply @sosub_find_some; sp.

      * allrw map_length; unfold num_bvars; simpl; auto.

      * unfold apply_bterm in h; simpl in h.
        applydup @sosub_find_some in Heqo; repnd.
        applydup @sosub_find_some in Heqq; repnd.
        allrw @cover_so_vars_sovar; repnd.
        revert h.
        change_to_lsubst_aux4; auto; clear h;
        try (complete (allrw disjoint_cons_r; repnd;
                       rw flat_map_map; unfold compose;
                       eapply disjoint_bound_vars_prop3; eauto)).

    + rw len in Heqo.
      eapply false_if_approx_star_sosub_find in Heqo; eauto; sp.

    + rw len in Heqo.
      eapply false_if_approx_star_sosub_find2 in Heqo; eauto; sp.

    + apply approx_star_apply_list; auto.

      * apply approx_star_refl; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux sub1 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux sub2 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n ts default_soterm) as t1.
        remember (nth n ts2 default_soterm) as t2.
        dup i as i'; rw len in i'.
        pose proof (nth_in _ n ts default_soterm i) as j1.
        pose proof (nth_in _ n ts2 default_soterm i') as j2.
        pose proof (imp t1 t2) as a;
          autodimp a hyp;[subst; apply in_nth_combine; complete auto|].
        rw <- Heqt1 in j1; clear Heqt1.
        rw <- Heqt2 in j2; clear Heqt2.

        rw disjoint_flat_map_r in d1.
        rw disjoint_flat_map_r in d2.
        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub sub1) (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub sub2) (flat_map fovars ts2))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        eapply ind; eauto.

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

  - Case "soseq".
    inversion aeq as [ | ? ? F | ]; clear aeq; subst; allsimpl; tcsp.
    eapply apss; try (apply approx_open_refl); eauto 3 with slow.
    introv.
    apply alpha_implies_approx_star; eauto 3 with slow.
    apply alphaeq_eq;apply F.

  - Case "soterm".
    applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
    inversion aeq as [| |? ? ? len imp]; subst; clear aeq; allsimpl.
    allrw disjoint_app_r; repnd.

    allrw @wf_soterm_iff; repnd.
    allrw @cover_so_vars_soterm.

    apply approx_star_congruence;
      [|rw map_map; unfold compose; rw <- wf0;
        apply eq_maps_combine; auto; introv i;
        apply in_combine_swap in i; auto;
        apply imp in i;
        rw @num_bvars_sosub_b_aux;
        apply so_alphaeq_vs_implies_eq_num_sobvars in i; auto].

    apply approx_starbts_map; auto.
    introv i.
    applydup imp in i as a.

    destruct a1 as [l1 t1].
    destruct a2 as [l2 t2].

    applydup in_combine in i; repnd.
    applydup wf1 in i1.
    applydup wf2 in i0.

    simpl.
    apply (so_alphaeqbt_vs_implies_more
            _ _ _ (free_vars_sosub sub1
                                   ++ so_dom sub1
                                   ++ so_dom sub2
                                   ++ free_vars_sosub sub2
                                   ++ bound_vars_sosub sub1
                                   ++ bound_vars_sosub sub2
                                   ++ allvars (sosub_aux (sosub_filter sub1 (vars2sovars l1)) t1)
                                   ++ allvars (sosub_aux (sosub_filter sub2 (vars2sovars l2)) t2)
          )) in a; auto.
    inversion a as [? ? ? u1 u2 len1 len2 disj norep ae]; subst; allsimpl; clear a.
    apply so_alphaeq_vs_iff in ae.
    allrw disjoint_app_r; repnd.

    unfold approx_star_bterm, blift_sub.

    exists vs
           (sosub_aux sub1 (so_swap (mk_swapping l1 vs) t1))
           (sosub_aux sub2 (so_swap (mk_swapping l2 vs) t2)).

    dands; auto.

    + pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
      rw @sosize_so_swap in h; auto.
      repeat (autodimp h hyp).
      pose proof (h (so_swap (mk_swapping l2 vs) t2) sub1 sub2 opr) as k; clear h.
      allrw <- @wf_soterm_so_swap.
      repeat (autodimp k hyp).

      { rw @fo_bound_var_so_swap.
        rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
        allrw disjoint_app_r; repnd.
        apply disjoint_swapbvars; eauto with slow. }

      { rw @fo_bound_var_so_swap.
        rw disjoint_flat_map_r in d2; applydup d2 in i0 as k; simpl in k.
        allrw disjoint_app_r; repnd.
        apply disjoint_swapbvars; eauto with slow. }

      { rw @fovars_so_swap.
        rw disjoint_app_r; dands; auto.
        apply disjoint_swapbvars; eauto 3 with slow.
        { rw disjoint_flat_map_r in d3; applydup d3 in i1 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
        { rw disjoint_flat_map_r in d3; applydup d3 in i1 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
      }

      { rw @fovars_so_swap.
        rw disjoint_app_r; dands; auto.
        apply disjoint_swapbvars; eauto 3 with slow.
        { rw disjoint_flat_map_r in d4; applydup d4 in i0 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
        { rw disjoint_flat_map_r in d4; applydup d4 in i0 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
      }

      { apply cover_so_vars_so_swap; eauto with slow. }

      { apply cover_so_vars_so_swap; eauto with slow. }

      destruct (dec_op_eq_fresh op) as [df|df]; tcsp.

      {
        right.
        pose proof (exists_nrut_sub
                      vs
                      ((get_utokens_lib lib (sosub_aux sub1 (so_swap (mk_swapping l1 vs) t1)))
                         ++
                         get_utokens_lib lib (sosub_aux sub2 (so_swap (mk_swapping l2 vs) t2))))
          as exnrut; exrepnd.
        exists sub; dands; auto.
        apply lsubst_approx_star_congr3; eauto with slow.
      }

    + rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
      rw disjoint_flat_map_r in d2; applydup d2 in i0 as j; simpl in j.
      rw disjoint_flat_map_r in d3; applydup d3 in i1 as m; simpl in m.
      rw disjoint_flat_map_r in d4; applydup d4 in i0 as n; simpl in n.
      allrw disjoint_app_r; repnd; auto.

      pose proof (subvars_swpbvars l1 l1 vs) as sv;
        repeat (autodimp sv hyp); eauto 3 with slow;[].

      pose proof (sosub_filter_if_not_in_dom
                    (so_swap (mk_swapping l1 vs) t1)
                    sub1
                    (vars2sovars (swapbvars (mk_swapping l1 vs) l1))) as h.
      autodimp h hyp;
        [apply if_disjoint_sovars2vars;
          rw sovars2vars_vars2sovars;
          rw @sovars2vars_sodom_is_so_dom; eauto with slow|].
      rw <- h; clear h.

      pose proof (sosub_aux_sosub_filter_so_swap
                    t1 sub1 l1 vs l1) as h;
        repeat (autodimp h hyp); eauto 3 with slow;[].
      rw h; clear h.

      pose proof (btchange_alpha_cswap
                    (sosub_aux (sosub_filter sub1 (vars2sovars l1)) t1)
                    l1 vs) as e; repeat (autodimp e hyp); eauto 3 with slow.

    + rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
      rw disjoint_flat_map_r in d2; applydup d2 in i0 as j; simpl in j.
      rw disjoint_flat_map_r in d3; applydup d3 in i1 as m; simpl in m.
      rw disjoint_flat_map_r in d4; applydup d4 in i0 as n; simpl in n.
      allrw disjoint_app_r; repnd; auto.

      pose proof (subvars_swpbvars l2 l2 vs) as sv;
        repeat (autodimp sv hyp); eauto 3 with slow;[].

      pose proof (sosub_filter_if_not_in_dom
                    (so_swap (mk_swapping l2 vs) t2)
                    sub2
                    (vars2sovars (swapbvars (mk_swapping l2 vs) l2))) as h.
      autodimp h hyp;
        [apply if_disjoint_sovars2vars;
          rw sovars2vars_vars2sovars;
          rw @sovars2vars_sodom_is_so_dom; eauto with slow|].
      rw <- h; clear h.

      pose proof (sosub_aux_sosub_filter_so_swap
                    t2 sub2 l2 vs l2) as h;
        repeat (autodimp h hyp); eauto 3 with slow;[].
      rw h; clear h.

      pose proof (btchange_alpha_cswap
                    (sosub_aux (sosub_filter sub2 (vars2sovars l2)) t2)
                    l2 vs) as e; repeat (autodimp e hyp); eauto 3 with slow.
Qed.

Lemma sosub_approx_star_congr {p} :
  forall (lib : library)
         (opr : Opid)
         (t : @SOTerm p)
         (sub1 sub2 : SOSub),
    wf_soterm t
    -> sodom sub1 = sodom sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> opr <> NCan NFresh
    -> approx_star_sosub lib opr sub1 sub2
    -> approx_star lib (sosub sub1 t) (sosub sub2 t).
Proof.
  introv wf len cov1 cov2 d ap.
  pose proof (fovars_subvars_all_fo_vars t) as sv.

  pose proof (unfold_sosub sub1 t) as h; exrepnd.
  rw h1; clear h1.

  pose proof (unfold_sosub sub2 t) as k; exrepnd.
  rw k1; clear k1.

  applydup @alphaeq_sosub_implies_eq_sodoms in h0 as eqdoms1.
  applydup @alphaeq_sosub_implies_eq_sodoms in k0 as eqdoms2.
  pose proof (fovars_subvars_all_fo_vars t') as sv1.
  pose proof (fovars_subvars_all_fo_vars t'0) as sv2.
  pose proof (cover_so_vars_if_so_alphaeq t t' sub1 cov1 h2) as cov3; auto.
  pose proof (cover_so_vars_if_alphaeq_sosub t' sub1 sub' cov3 h0) as cov4; auto.
  pose proof (cover_so_vars_if_so_alphaeq t t'0 sub2 cov2 k2) as cov5; auto.
  pose proof (cover_so_vars_if_alphaeq_sosub t'0 sub2 sub'0 cov5 k0) as cov6; auto.

  eapply sosub_aux_approx_star_congr_al; eauto 3 with slow.

  - apply so_alphaeq_vs_preserves_wf in h2; auto.

  - apply so_alphaeq_vs_preserves_wf in k2; auto.

  - allrw <-; auto.

  - rw disjoint_app_r; dands; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.

  - eapply approx_star_sosub_alphaeq_r;[apply alphaeq_sosub_sym;exact h0|].
    eapply approx_star_sosub_alphaeq_l;[|exact k0];auto.
Qed.

Lemma mk_instance_approx_star_congr {p} :
  forall (lib : library)
         (opr : @Opid p)
         (t : @SOTerm p)
         (vars : list sovar_sig)
         (bs1 bs2 : list BTerm),
    wf_soterm t
    -> socovered t vars
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> opr <> NCan NFresh
    -> approx_starbts lib opr bs1 bs2
    -> approx_star lib (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv wf cov m1 m2 d ap.
  unfold mk_instance.
  eapply sosub_approx_star_congr; eauto.

  - rw <- @mk_abs_subst_some_prop2; auto.
    rw <- @mk_abs_subst_some_prop2; auto.

  - apply socovered_implies_cover_so_vars; auto.

  - apply socovered_implies_cover_so_vars; auto.

  - apply approx_starbts_implies_approx_star_sosub; auto.
Qed.
