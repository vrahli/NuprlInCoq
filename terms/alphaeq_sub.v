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


Require Export alphaeq2.
Require Export swap.


Inductive alphaeq_sub {o} : @Sub o -> @Sub o -> Type :=
  | aeqsub_nil : alphaeq_sub [] []
  | aeqsub_cons :
      forall v t1 t2 sub1 sub2,
        alphaeq t1 t2
        -> alphaeq_sub sub1 sub2
        -> alphaeq_sub ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors alphaeq_sub.

Inductive alphaeq_sub_range {o} : @Sub o -> @Sub o -> Type :=
  | aeqrsub_nil : alphaeq_sub_range [] []
  | aeqrsub_cons :
      forall v1 v2 t1 t2 sub1 sub2,
        alphaeq t1 t2
        -> alphaeq_sub_range sub1 sub2
        -> alphaeq_sub_range ((v1,t1) :: sub1) ((v2,t2) :: sub2).
Hint Constructors alphaeq_sub_range.

Lemma alphaeq_sub_range_implies_eq_length {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub_range sub1 sub2 -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; auto;
  inversion aeq; subst; sp.
Qed.

Lemma alphaeq_sub_implies_alphaeq_sub_range {o} :
    forall (sub1 sub2 : @Sub o),
      alphaeq_sub sub1 sub2
      -> alphaeq_sub_range sub1 sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; auto;
  inversion aeq; subst.
  constructor; auto.
Qed.
Hint Resolve alphaeq_sub_implies_alphaeq_sub_range : slow.

Lemma alphaeq_sub_range_trans {o} :
  forall (sub1 sub2 sub3 : @Sub o),
    alphaeq_sub_range sub1 sub2
    -> alphaeq_sub_range sub2 sub3
    -> alphaeq_sub_range sub1 sub3.
Proof.
  induction sub1; destruct sub2, sub3; introv aeq1 aeq2; tcsp;
  inversion aeq1; inversion aeq2; subst; cpx; clear aeq1 aeq2.
  constructor; eauto.
  eapply alphaeq_trans; eauto.
Qed.
Hint Resolve alphaeq_sub_range_trans : slow.

Lemma alphaeq_sub_range_sym {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub_range sub1 sub2
    -> alphaeq_sub_range sub2 sub1.
Proof.
  induction sub1; destruct sub2; introv aeq; tcsp;
  inversion aeq; subst; cpx; clear aeq.
  constructor; eauto.
  eapply alphaeq_sym; eauto.
Qed.
Hint Resolve alphaeq_sub_range_sym : slow.

Lemma alphaeq_sub_range_refl {o} :
  forall (sub : @Sub o),
    alphaeq_sub_range sub sub.
Proof.
  induction sub; auto.
  destruct a.
  constructor; auto.
  apply alphaeq_refl.
Qed.
Hint Resolve alphaeq_sub_range_refl : slow.

Lemma length_dom {o} :
  forall (sub : @Sub o),
    length (dom_sub sub) = length sub.
Proof.
  induction sub; allsimpl; sp.
Qed.

Lemma length_range {o} :
  forall (sub : @Sub o),
    length (range sub) = length sub.
Proof.
  induction sub; allsimpl; sp.
Qed.

Lemma alphaeq_sub_implies_eq_doms {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2 -> dom_sub sub1 = dom_sub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp.
  - inversion aeq.
  - inversion aeq.
  - inversion aeq; subst; clear aeq; allsimpl.
    f_equal; apply IHsub1; auto.
Qed.

Lemma alphaeq_sub_implies_eq_lengths {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2 -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; inversion aeq; tcsp; cpx.
Qed.

Lemma bin_rel_nterm_cons {o} :
  forall (t1 t2 : @NTerm o) ts1 ts2,
    bin_rel_nterm alphaeq (t1 :: ts1) (t2 :: ts2)
    <=> (bin_rel_nterm alphaeq ts1 ts2 # alphaeq t1 t2).
Proof.
  introv; unfold bin_rel_nterm, binrel_list; simpl.
  split; intro k; repnd; cpx; dands; auto.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; omega.
  - pose proof (k 0) as h; autodimp h hyp; omega.
  - introv i.
    destruct n; cpx.
Qed.

Lemma alphaeq_sub_implies_alphaeq {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> bin_rel_nterm alphaeq (range sub1) (range sub2).
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp.
  - unfold bin_rel_nterm, binrel_list; simpl; sp.
  - inversion aeq.
  - inversion aeq.
  - inversion aeq; subst; clear aeq; simpl.
    simpl; apply bin_rel_nterm_cons; dands; sp.
Qed.

Lemma bin_rel_nterm_cons2 {o} :
  forall (t1 t2 : @NTerm o) ts1 ts2,
    bin_rel_nterm alpha_eq (t1 :: ts1) (t2 :: ts2)
    <=> (bin_rel_nterm alpha_eq ts1 ts2 # alpha_eq t1 t2).
Proof.
  introv; unfold bin_rel_nterm, binrel_list; simpl.
  split; intro k; repnd; cpx; dands; auto.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; omega.
  - pose proof (k 0) as h; autodimp h hyp; allsimpl; try omega.
  - introv i.
    destruct n; cpx.
Qed.

Lemma alphaeq_sub_implies_alpha_eq {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> bin_rel_nterm alpha_eq (range sub1) (range sub2).
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp.
  - unfold bin_rel_nterm, binrel_list; simpl; sp.
  - inversion aeq.
  - inversion aeq.
  - inversion aeq; subst; clear aeq; simpl.
    simpl; apply bin_rel_nterm_cons2; dands; sp.
    apply alphaeq_eq; auto.
Qed.

Definition sub_change_bvars_alpha {o} (vs : list NVar) (sub : @Sub o) : @Sub o :=
  map (fun x =>
         match x with
           | (v,t) => (v,change_bvars_alpha vs t)
         end)
      sub.

Fixpoint sub_bound_vars {p} (sub : @Sub p) : list NVar :=
  match sub with
  | nil => nil
  | (v, t) :: xs => bound_vars t ++ sub_bound_vars xs
  end.

Lemma sub_bound_vars_is_flat_map_bound_vars_range {o} :
  forall (sub : @Sub o),
    sub_bound_vars sub = flat_map bound_vars (range sub).
Proof.
  induction sub; simpl; auto.
  destruct a; simpl.
  rw IHsub; auto.
Qed.

Lemma subvars_app_lr :
  forall vs1 vs2 vs3 vs4,
    subvars vs1 vs2
    -> subvars vs3 vs4
    -> subvars (vs1 ++ vs3) (vs2 ++ vs4).
Proof.
  introv sv1 sv2.
  allrw subvars_prop; introv i.
  allrw in_app_iff; dorn i.
  - apply sv1 in i; sp.
  - apply sv2 in i; sp.
Qed.

Lemma subvars_sub_bound_vars_sub_filter {o} :
  forall (sub : @Sub o) l,
    subvars (sub_bound_vars (sub_filter sub l)) (sub_bound_vars sub).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; boolvar; simpl.
  - apply subvars_app_weak_r; auto.
  - apply subvars_app_lr; auto.
Qed.

Lemma sub_bound_vars_var_ren {o} :
  forall vs1 vs2,
    @sub_bound_vars o (var_ren vs1 vs2) = [].
Proof.
  induction vs1; destruct vs2; allsimpl; auto.
  apply IHvs1.
Qed.

Lemma sub_change_bvars_alpha_spec {o} :
  forall vars (sub : @Sub o),
    let sub' := sub_change_bvars_alpha vars sub in
    disjoint vars (sub_bound_vars sub')
    # alphaeq_sub sub sub'.
Proof.
  induction sub; introv; allsimpl; repnd; dands; allsimpl; auto.
  - rw disjoint_app_r; dands; auto.
    t_change u; auto.
  - constructor; auto.
    t_change u; auto.
    apply alphaeq_eq; auto.
Qed.

Lemma alphaeq_sub_preserves_free_vars {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> sub_free_vars sub1 = sub_free_vars sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; inversion aeq; allsimpl; auto;
  subst; clear aeq.
  f_equal;[|apply IHsub1;auto].
  apply alphaeq_preserves_free_vars; auto.
  apply alphaeq_eq; auto.
Qed.

Lemma alphaeq_sub_trans {o} :
  forall (sub1 sub2 sub3 : @Sub o),
    alphaeq_sub sub1 sub2
    -> alphaeq_sub sub2 sub3
    -> alphaeq_sub sub1 sub3.
Proof.
  induction sub1; destruct sub2, sub3; introv aeq1 aeq2; tcsp;
  inversion aeq1; inversion aeq2; subst; cpx; clear aeq1 aeq2.
  constructor; eauto.
  eapply alphaeq_trans; eauto.
Qed.
Hint Resolve alphaeq_sub_trans : slow.

Lemma alphaeq_sub_sym {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> alphaeq_sub sub2 sub1.
Proof.
  induction sub1; destruct sub2; introv aeq; tcsp;
  inversion aeq; subst; cpx; clear aeq.
  constructor; eauto.
  eapply alphaeq_sym; eauto.
Qed.
Hint Resolve alphaeq_sub_sym : slow.

Lemma alphaeq_sub_refl {o} :
  forall (sub : @Sub o), alphaeq_sub sub sub.
Proof.
  induction sub; auto.
  destruct a; constructor; auto.
  apply alphaeq_refl.
Qed.
Hint Resolve alphaeq_sub_refl : slow.

Lemma alphaeq_sub_range_implies_alphaeq_sub {o} :
  forall (sub1 sub2 : @Sub o) vs,
    alphaeq_sub_range sub1 sub2
    -> alphaeq_sub (combine vs (range sub1)) (combine vs (range sub2)).
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  allrw combine_nil; auto; inversion aeq; subst; allsimpl.
  destruct vs; simpl; auto.
Qed.
