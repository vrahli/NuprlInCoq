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


Require Export terms2.
Require Export terms_tacs.
Require Export tactics2.
Require Export list.



(* ------ binary and ------ *)


Definition mk_uand {p} (A B : @NTerm p) :=
  match newvars2 [A,B] with
    | (vx,vy) =>
      mk_isect mk_base vx
               (mk_isect (mk_halts (mk_var vx)) vy
                         (mk_isaxiom (mk_var vx) A B))
  end.

Lemma isprog_vars_uand {o} :
  forall (A B : @NTerm o) vs,
    isprog_vars vs (mk_uand A B) <=> (isprog_vars vs A # isprog_vars vs B).
Proof.
  introv.
  unfold mk_uand.
  remember (newvars2 [A,B]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp.
  allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
  repeat (rw <- @isprog_vars_isect_iff).
  rw @isprog_vars_isaxiom.
  rw @isprog_vars_halts.
  allrw <- @isprog_vars_var_iff; simpl; split; intro k; repnd; dands; auto.
  repeat (apply isprog_vars_cons_if2 in k3; auto).
  repeat (apply isprog_vars_cons_if2 in k; auto).
  repeat (apply isprog_vars_cons; auto).
  repeat (apply isprog_vars_cons; auto).
Qed.

Lemma wf_uand {o} :
  forall a b : @NTerm o, wf_term (mk_uand a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_uand.
  remember (newvars2 [a,b]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp.
  allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
  allrw <- @wf_isect_iff.
  rw <- @wf_halts_iff.
  rw @wf_isaxiom; split; sp.
Qed.


(* ------ free vars ------ *)

Lemma free_vars_lam {o} :
  forall v b, free_vars (@mk_lam o v b) = remove_nvars [v] (free_vars b).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_isect {o} :
  forall a v b, free_vars (@mk_isect o a v b) = free_vars a ++ (remove_nvars [v] (free_vars b)).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_function {o} :
  forall a v b, free_vars (@mk_function o a v b) = free_vars a ++ (remove_nvars [v] (free_vars b)).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_product {o} :
  forall a v b, free_vars (@mk_product o a v b) = free_vars a ++ (remove_nvars [v] (free_vars b)).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_tunion {o} :
  forall a v b, free_vars (@mk_tunion o a v b) = free_vars a ++ (remove_nvars [v] (free_vars b)).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_cbv {o} :
  forall a v b, free_vars (@mk_cbv o a v b) = free_vars a ++ (remove_nvars [v] (free_vars b)).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_base {o} :
  free_vars (@mk_base o) = [].
Proof.
  introv; simpl; sp.
Qed.

Lemma free_vars_axiom {o} :
  @free_vars o mk_axiom = [].
Proof.
  introv; simpl; sp.
Qed.

Lemma free_vars_approx {o} :
  forall a b, free_vars (@mk_approx o a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_isaxiom {o} :
  forall a b c, free_vars (@mk_isaxiom o a b c) = free_vars a ++ free_vars b ++ free_vars c.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_equality {o} :
  forall a b c, free_vars (@mk_equality o a b c) = free_vars a ++ free_vars b ++ free_vars c.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_tequality {o} :
  forall a b, free_vars (@mk_tequality o a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_apply {o} :
  forall a b, free_vars (@mk_apply o a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_union {o} :
  forall a b : @NTerm o, free_vars (mk_union a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_eunion {o} :
  forall a b : @NTerm o, free_vars (mk_eunion a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_halts {o} :
  forall a, free_vars (@mk_halts o a) = free_vars a.
Proof.
  introv.
  unfold mk_halts.
  rw @free_vars_approx.
  rw @free_vars_cbv.
  rw @free_vars_axiom.
  rw remove_nvars_nil_r; rw app_nil_r; simpl; sp.
Qed.

Lemma free_vars_uand {o} :
  forall A B, free_vars (@mk_uand o A B) = free_vars A ++ free_vars B.
Proof.
  introv.
  unfold mk_uand.

  remember (newvars2 [A,B]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp.
  repeat (rw app_nil_r in Heqp); repeat (rw in_app_iff in Heqp).
  repeat (rw not_over_or in Heqp); repnd.

  repeat rw @free_vars_isect.

  rw @free_vars_halts.
  rw @free_vars_base.
  rw @free_vars_isaxiom; simpl.
  repeat (rw remove_nvars_cons_r; boolvar; allrw not_over_or; repnd; spFalseHyp).
  rw remove_nvars_app_l; simpl.
  rw remove_nvars_app_r.
  repeat (rw remove_nvars_cons_l_weak; sp).
Qed.

Lemma free_vars_decide {o} :
  forall (a : @NTerm o) v1 b1 v2 b2,
    free_vars (mk_decide a v1 b1 v2 b2)
    = free_vars a
                ++ remove_nvars [v1] (free_vars b1)
                ++ remove_nvars [v2] (free_vars b2).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_spread {o} :
  forall (a : @NTerm o) v1 v2 b,
    free_vars (mk_spread a v1 v2 b)
    = free_vars a ++ remove_nvars [v1,v2] (free_vars b).
Proof.
  introv; simpl.
  rw app_nil_r; sp.
Qed.

Lemma free_vars_unit {o} :
  @free_vars o mk_unit = [].
Proof.
  unfold mk_unit, mk_true.
  rw @free_vars_approx; rw @free_vars_axiom; auto.
Qed.

Lemma free_vars_bool {o} :
  @free_vars o mk_bool = [].
Proof.
  unfold mk_bool.
  rw @free_vars_union.
  rw @free_vars_unit; auto.
Qed.
