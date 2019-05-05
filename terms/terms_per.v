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


Require Export terms_props.
Require Export List.
Require Export list. (* why? *)


Lemma isprog_vars_ufun_imp {p} :
  forall vs a b,
    isprog_vars vs a
    -> @isprog_vars p vs b
    -> isprog_vars vs (mk_ufun a b).
Proof.
  introv; rw <- @isprog_vars_ufun; sp.
Qed.

Hint Resolve isprog_vars_ufun_imp : isprog.
Hint Resolve isprog_unit : isprog.
Hint Resolve isprog_vars_cons : isprog.


(*
(* ------ erase ------ *)


Definition mk_erase T := mk_ufun T mk_unit.

Lemma isprog_vars_erase :
  forall vs a,
    isprog_vars vs a
    -> isprog_vars vs (mk_erase a).
Proof.
  unfold mk_erase; sp.
  apply isprog_vars_ufun_imp; sp.
  apply isprog_vars_if_isprog.
  apply isprog_unit.
Qed.

Lemma isprog_erase :
  forall a, isprog a -> isprog (mk_erase a).
Proof.
  unfold mk_erase; sp.
  apply isprog_ufun; sp.
Qed.

Hint Resolve isprog_vars_erase : isprog.
Hint Resolve isprog_erase : isprog.


Definition mkc_erase (T : CTerm) : CTerm :=
  let (t,x) := T in existT isprog (mk_erase t) (isprog_erase t x).

Lemma mkc_erase_eq :
  forall T, mkc_erase T = mkc_ufun T mkc_unit.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.
*)

(* ------ erase ------ *)

(**

  The following erasure operator is basically ``quotiented by true''.

*)

Definition erase_rel {p} A :=
  match @newvars2 p [A] with
    | (va,vb) => mk_lam va (mk_lam vb A)
  end.

Lemma isprog_erase_rel {p} :
  forall a, @isprog p a -> isprog (erase_rel a).
Proof.
  introv ipa.
  unfold erase_rel.
  destruct (newvars2 [a]); repnd.
  eauto 10 with isprog.
Qed.

Lemma isprog_vars_erase_rel {p} :
  forall vs a, @isprog_vars p vs a -> isprog_vars vs (erase_rel a).
Proof.
  introv ipa.
  unfold erase_rel.
  destruct (newvars2 [a]); repnd.
  eauto 10 with isprog.
Qed.

Lemma isprog_vars_erase_rel_iff {o} :
  forall vs a, @isprog_vars o vs a <=> isprog_vars vs (erase_rel a).
Proof.
  introv; split; intro k.
  apply isprog_vars_erase_rel; auto.
  unfold erase_rel in k.
  remember (newvars2 [a]); repnd.
  repeat (rw @isprog_vars_lam_iff in k).
  apply newvars2_prop2 in Heqp; allsimpl.
  allrw app_nil_r; repnd.
  allrw @isprog_vars_eq.
  repnd; dands; auto.
  provesv.
  allrw in_app_iff; allrw in_single_iff; repdors; auto; subst; sp.
Qed.

Definition erase {o} A := @mk_pertype o (erase_rel A).

Lemma isprog_erase {p} :
  forall a, @isprog p a -> isprog (erase a).
Proof.
  introv ipa.
  apply isprog_pertype.
  apply isprog_erase_rel; auto.
Qed.

Lemma isprog_vars_erase {p} :
  forall vs a, @isprog_vars p vs a -> isprog_vars vs (erase a).
Proof.
  introv ipa.
  apply isprog_vars_pertype.
  apply isprog_vars_erase_rel; auto.
Qed.

Lemma isprog_vars_erase_iff {p} :
  forall vs a, @isprog_vars p vs a <=> isprog_vars vs (erase a).
Proof.
  introv.
  rw @isprog_vars_pertype.
  apply isprog_vars_erase_rel_iff.
Qed.

Hint Resolve isprog_erase_rel : isprog.
Hint Resolve isprog_erase : isprog.
Hint Resolve isprog_vars_erase_rel : isprog.
Hint Resolve isprog_vars_erase : isprog.

Definition erasec_rel {p} (A : @CTerm p) : CTerm :=
  let (a,x) := A in mk_ct (erase_rel a) (isprog_erase_rel a x).

Definition erasec {p} (A : @CTerm p) : CTerm :=
  let (a,x) := A in mk_ct (erase a) (isprog_erase a x).

Lemma erasec_eq {p} :
  forall A, @erasec p A = mkc_pertype (erasec_rel A).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma wf_erase_rel {p} :
  forall a, @wf_term p a -> wf_term (erase_rel a).
Proof.
  unfold erase_rel; introv w.
  destruct (newvars2 [a]).
  repeat (apply wf_lam); auto.
Qed.

Lemma wf_erase {p} :
  forall a, @wf_term p a -> wf_term (erase a).
Proof.
  unfold erase; introv w.
  apply wf_pertype.
  apply wf_erase_rel; auto.
Qed.

Theorem wf_erase_rel_iff {p} :
  forall a, @wf_term p a <=> wf_term (erase_rel a).
Proof.
  introv; split; intro k.
  apply wf_erase_rel; auto.
  revert k.
  unfold erase_rel; destruct (newvars2 [a]); intro.
  repeat (rw <- @wf_lam_iff in k); auto.
Qed.

Theorem wf_erase_iff {p} :
  forall a, @wf_term p a <=> wf_term (erase a).
Proof.
  unfold erase; introv.
  rw <- @wf_pertype_iff.
  rw <- @wf_erase_rel_iff; sp.
Qed.



(* ------ Erased relation ------ *)


Definition sqper_rel {p} v1 v2 R := @mk_lam p v1 (mk_lam v2 (erase R)).
Definition sqper {p} v1 v2 R := @mk_pertype p (sqper_rel v1 v2 R).



(* ------ per-function ------ *)


Definition mk_per_function_base {o} va vb vf vg vx (A B : @NTerm o) :=
  let Ef := mk_equality
              (mk_apply (mk_var vf) (mk_var va))
              (mk_apply (mk_var vg) (mk_var vb))
              (mk_apply B (mk_var va)) in
  let Et := mk_tequality (mk_apply B (mk_var va)) (mk_apply B (mk_var vb)) in
  let Ea := mk_equality (mk_var va) (mk_var vb) A in
  let I := mk_isect Ea vx (mk_uand Ef Et) in
  mk_isect mk_base va (mk_isect mk_base vb I).

(* I should use sqper_rel here *)
Definition mk_per_function_rel {o} (A B : @NTerm o) :=
  match newvars5 [A,B] with
    | (va,vb,vf,vg,vx) =>
      mk_lam vf (mk_lam vg (erase (mk_per_function_base va vb vf vg vx A B)))
  end.

Definition mk_per_function {o} (A B : @NTerm o) :=
 mk_pertype (mk_per_function_rel A B).

Lemma wf_term_mk_per_function_rel {o} :
  forall A B,
    wf_term (@mk_per_function_rel o A B)
    <=> (wf_term A # wf_term B).
Proof.
  introv; unfold mk_per_function_rel.
  destruct (newvars5 [A,B]); repnd.
  allrw <- @wf_lam_iff.
  allrw <- @wf_erase_iff.
  rw <- @wf_isect_iff.
  rw <- @wf_isect_iff.
  rw <- @wf_isect_iff.
  rw @wf_uand.
  allrw <- @wf_equality_iff; repnd.
  allrw <- @wf_tequality_iff; repnd.
  allrw <- @wf_apply_iff.
  split; sp.
Qed.

Lemma wf_term_mk_per_function {o} :
  forall A B,
    wf_term (@mk_per_function o A B)
    <=> (wf_term A # wf_term B).
Proof.
  introv; unfold mk_per_function.
  rw <- @wf_pertype_iff.
  rw <- @wf_term_mk_per_function_rel; sp.
Qed.

Lemma isprog_vars_mk_per_function_rel_iff {o} :
  forall a b vs,
    (isprog_vars vs a # @isprog_vars o vs b)
      <=> isprog_vars vs (mk_per_function_rel a b).
Proof.
  introv.

  unfold mk_per_function_rel.

  remember (newvars5 [a,b]).
  repnd.
  apply newvars5_prop in Heqp; repnd; allsimpl.
  allrw app_nil_r.

  allrw @isprog_vars_lam_iff.
  allrw <- @isprog_vars_erase_iff.
  rw <- @isprog_vars_isect_iff.
  rw <- @isprog_vars_isect_iff.
  rw <- @isprog_vars_isect_iff.
  rw @isprog_vars_uand.
  allrw <- @isprog_vars_equality_iff.
  allrw <- @isprog_vars_tequality_iff.
  allrw @isprog_vars_apply; repnd.
  repeat (rw <- app_assoc); simpl.
  allrw @isprog_vars_base_iff.
  allrw <- @isprog_vars_var_iff; simpl.
  repeat (rw in_app_iff); simpl.
  allrw eq_var_iff.
  repeat (first [rw or_true_l | rw or_true_r | rw and_true_l | rw and_true_r]).

  split; intro k; repnd; dands.

  repeat (apply isprog_vars_cons).
  apply isprog_vars_app1; sp.

  repeat (apply isprog_vars_cons).
  apply isprog_vars_app1; sp.

  repeat (apply isprog_vars_cons).
  apply isprog_vars_app1; sp.

  repeat (apply isprog_vars_cons).
  apply isprog_vars_app1; sp.

  apply isprog_vars_cons_if2 in k0;
    try (complete (repeat (rw in_app_iff in Heqp1); repeat (rw not_over_or in Heqp1); sp)).
  apply isprog_vars_cons_if2 in k0;
    try (complete (repeat (rw in_app_iff in Heqp0); repeat (rw not_over_or in Heqp0); sp)).
  apply isprog_vars_cons_app1 in k0; try (complete sp).
  introv i; simpl in i; repdors; try (complete sp); subst.
  repeat (rw in_app_iff in Heqp2); repeat (rw not_over_or in Heqp2); sp.
  repeat (rw in_app_iff in Heqp3); repeat (rw not_over_or in Heqp3); sp.

  apply isprog_vars_cons_if2 in k;
    try (complete (repeat (rw in_app_iff in Heqp); repeat (rw not_over_or in Heqp); sp)).
  apply isprog_vars_cons_if2 in k;
    try (complete (repeat (rw in_app_iff in Heqp1); repeat (rw not_over_or in Heqp1); sp)).
  apply isprog_vars_cons_if2 in k;
    try (complete (repeat (rw in_app_iff in Heqp0); repeat (rw not_over_or in Heqp0); sp)).
  apply isprog_vars_cons_app1 in k; try (complete sp).
  introv i; simpl in i; repdors; try (complete sp); subst.
  repeat (rw in_app_iff in Heqp2); repeat (rw not_over_or in Heqp2); sp.
  repeat (rw in_app_iff in Heqp3); repeat (rw not_over_or in Heqp3); sp.
Qed.

Lemma isprog_vars_mk_per_function_iff {o} :
  forall a b vs,
    (isprog_vars vs a # @isprog_vars o vs b)
      <=> isprog_vars vs (mk_per_function a b).
Proof.
  introv.

  unfold mk_per_function.
  rw @isprog_vars_pertype.
  rw <- @isprog_vars_mk_per_function_rel_iff; sp.
Qed.

Lemma isprog_mk_per_function_rel_iff {o} :
  forall a b, (isprog a # @isprog o b) <=> isprog (mk_per_function_rel a b).
Proof.
  introv.
  repeat (rw @isprog_vars_nil_iff_isprog).
  apply isprog_vars_mk_per_function_rel_iff.
Qed.

Lemma isprog_mk_per_function_iff {o} :
  forall a b, (isprog a # @isprog o b) <=> isprog (mk_per_function a b).
Proof.
  introv.
  unfold mk_per_function.
  rw <- @isprog_pertype_iff.
  rw <- @isprog_mk_per_function_rel_iff; sp.
Qed.

Lemma isprog_mk_per_function_rel {o} :
  forall a b,
    isprog a
    -> @isprog o b
    -> isprog (mk_per_function_rel a b).
Proof.
  introv ipa ipb.
  rw <- @isprog_mk_per_function_rel_iff; sp.
Qed.

Definition mkc_per_function_rel {o} (A B : @CTerm o) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  mk_ct (mk_per_function_rel a b) (isprog_mk_per_function_rel a b x y).


(* ------ iper-function ------ *)


Definition mk_iper_function_rel {o} (A B : @NTerm o) :=
  match newvars5 [A,B] with
    | (va,vb,vf,vg,vx) =>
      mk_lam vf (mk_lam vg (mk_per_function_base va vb vf vg vx A B))
  end.

Definition mk_iper_function {o} (A B : @NTerm o) :=
  mk_ipertype (mk_iper_function_rel A B).

(*
Lemma fold_mk_iper_function_rel :
  forall v1 v2 v3 v4 v5 A B,
    (v1, v2, v3, v4, v5) = newvars5 [A, B]
    -> mk_lam
         v3
         (mk_lam
            v4
            (mk_isect
               mk_base
               v1
               (mk_isect
                  mk_base
                  v2
                  (mk_isect
                     (mk_equality (mk_var v1) (mk_var v2) A)
                     v5
                     (mk_equality (mk_apply (mk_var v3) (mk_var v1))
                                  (mk_apply (mk_var v4) (mk_var v2))
                                  (mk_apply B (mk_var v1)))))))
       = mk_iper_function_rel A B.
Proof.
  introv eq.
  unfold mk_iper_function_rel.
  rw <- eq; sp.
Qed.
*)

Lemma wf_term_mk_iper_function_rel {o} :
  forall A B : @NTerm o,
    wf_term (mk_iper_function_rel A B)
    <=> (wf_term A # wf_term B).
Proof.
  introv; unfold mk_iper_function_rel.
  destruct (newvars5 [A,B]); repnd.
  allrw <- @wf_lam_iff.
  rw <- @wf_isect_iff.
  rw <- @wf_isect_iff.
  rw <- @wf_isect_iff.
  rw @wf_uand.
  allrw <- @wf_equality_iff; repnd.
  allrw <- @wf_tequality_iff; repnd.
  allrw <- @wf_apply_iff.
  split; sp.
Qed.

Lemma wf_term_mk_iper_function {o} :
  forall A B,
    wf_term (@mk_iper_function o A B)
    <=> (wf_term A # wf_term B).
Proof.
  introv; unfold mk_iper_function.
  rw <- @wf_ipertype_iff.
  rw <- @wf_term_mk_iper_function_rel; sp.
Qed.

Lemma isprog_vars_mk_iper_function_rel_iff {o} :
  forall a b vs,
    (isprog_vars vs a # @isprog_vars o vs b)
      <=> isprog_vars vs (mk_iper_function_rel a b).
Proof.
  introv.

  unfold mk_iper_function_rel.

  remember (newvars5 [a,b]).
  repnd.
  apply newvars5_prop in Heqp; repnd; allsimpl.
  allrw app_nil_r.

  allrw @isprog_vars_lam_iff.
  rw <- @isprog_vars_isect_iff.
  rw <- @isprog_vars_isect_iff.
  rw <- @isprog_vars_isect_iff.
  rw @isprog_vars_uand.
  allrw <- @isprog_vars_equality_iff.
  allrw <- @isprog_vars_tequality_iff.
  allrw @isprog_vars_apply; repnd.
  repeat (rw <- app_assoc); simpl.
  allrw @isprog_vars_base_iff.
  allrw <- @isprog_vars_var_iff; simpl.
  repeat (rw in_app_iff); simpl.
  allrw eq_var_iff.
  repeat (first [rw or_true_l | rw or_true_r | rw and_true_l | rw and_true_r]).

  split; intro k; repnd; dands.

  {
    repeat (apply isprog_vars_cons).
    apply isprog_vars_app1; sp.
  }

  {
    repeat (apply isprog_vars_cons).
    apply isprog_vars_app1; sp.
  }

  {
    repeat (apply isprog_vars_cons).
    apply isprog_vars_app1; sp.
  }

  {
    repeat (apply isprog_vars_cons).
    apply isprog_vars_app1; sp.
  }

  {
    repeat (apply isprog_vars_cons_if2 in k0;
            [|allrw in_app_iff; allrw not_over_or; repnd;tcsp]).
    apply isprog_vars_cons_app1 in k0; auto.
    allrw in_app_iff; allrw not_over_or; repnd.
    simpl; introv xx; repndors; subst; tcsp.
  }

  {
    allrw in_app_iff; allrw not_over_or; repnd.
    apply isprog_vars_cons_if2 in k1; auto.
    repeat (apply isprog_vars_cons_if2 in k1;
            [|allrw in_app_iff; allrw not_over_or; repnd;tcsp]).
    apply isprog_vars_cons_app1 in k1; auto.
    simpl; introv xx; repndors; subst; tcsp.
  }
Qed.

Lemma isprog_vars_mk_iper_function_iff {o} :
  forall a b vs,
    (isprog_vars vs a # @isprog_vars o vs b)
      <=> isprog_vars vs (mk_iper_function a b).
Proof.
  introv.

  unfold mk_iper_function.
  rw @isprog_vars_ipertype.
  rw <- @isprog_vars_mk_iper_function_rel_iff; sp.
Qed.

Lemma isprog_mk_iper_function_rel_iff {o} :
  forall a b, (isprog a # @isprog o b) <=> isprog (mk_iper_function_rel a b).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_mk_iper_function_rel_iff.
Qed.

Lemma isprog_mk_iper_function_iff {o} :
  forall a b, (isprog a # @isprog o b) <=> isprog (mk_iper_function a b).
Proof.
  introv.
  unfold mk_iper_function.
  rw <- @isprog_ipertype_iff.
  rw <- @isprog_mk_iper_function_rel_iff; sp.
Qed.

Lemma isprog_mk_iper_function_rel {o} :
  forall a b,
    isprog a
    -> @isprog o b
    -> isprog (mk_iper_function_rel a b).
Proof.
  introv ipa ipb.
  rw <- @isprog_mk_iper_function_rel_iff; sp.
Qed.

Definition mkc_iper_function_rel {o} (A B : @CTerm o) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  mk_ct (mk_iper_function_rel a b) (isprog_mk_iper_function_rel a b x y).



(* ------ sper-function ------ *)


Definition mk_sper_function {o} (A B : @NTerm o) :=
  mk_spertype (mk_iper_function_rel A B).

Lemma wf_term_mk_sper_function {o} :
  forall A B,
    wf_term (@mk_sper_function o A B)
    <=> (wf_term A # wf_term B).
Proof.
  introv; unfold mk_sper_function.
  rw <- @wf_spertype_iff.
  rw <- @wf_term_mk_iper_function_rel; sp.
Qed.

Lemma isprog_vars_mk_sper_function_iff {o} :
  forall a b vs,
    (isprog_vars vs a # @isprog_vars o vs b)
      <=> isprog_vars vs (mk_sper_function a b).
Proof.
  introv.

  unfold mk_iper_function.
  rw @isprog_vars_spertype.
  rw <- @isprog_vars_mk_iper_function_rel_iff; sp.
Qed.

Lemma isprog_mk_sper_function_iff {o} :
  forall a b, (isprog a # @isprog o b) <=> isprog (mk_sper_function a b).
Proof.
  introv.
  unfold mk_sper_function.
  rw <- @isprog_spertype_iff.
  rw <- @isprog_mk_iper_function_rel_iff; sp.
Qed.



(* Some other stuff *)


Lemma free_vars_erase {o} :
  forall a, free_vars (@erase o a) = free_vars a.
Proof.
  introv.
  unfold erase, erase_rel.

  remember (newvars2 [a]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp.
  repeat (rw app_nil_r in Heqp); repnd.

  simpl.
  allrw app_nil_r.
  allrw remove_nvars_nil_l.
  rw remove_nvars_app_l; simpl.
  repeat (rw remove_nvars_cons_l_weak; sp).
Qed.

Lemma free_vars_per_function_rel_eq {o} :
  forall A B,
    free_vars (@mk_per_function_rel o A B)
    = free_vars A ++ free_vars B ++ free_vars B ++ free_vars B.
Proof.
  introv.
  unfold mk_per_function_rel.
  remember (newvars5 [A,B]); repnd.
  apply newvars5_prop2 in Heqp; simpl in Heqp.
  repeat (rw app_nil_r in Heqp); repeat (rw in_app_iff in Heqp).
  repeat (rw not_over_or in Heqp); repnd.
  repeat rw @free_vars_lam.
  rw @free_vars_erase.
  unfold mk_per_function_base.
  rw @free_vars_isect.
  rw @free_vars_isect.
  rw @free_vars_isect.
  rw @free_vars_uand.
  allrw @free_vars_equality.
  allrw @free_vars_tequality.
  allrw @free_vars_apply; simpl.
  repeat (first [ rw remove_nvars_app_r
                | rw remove_nvars_app_l; simpl
                | rw remove_nvars_nil_r
                | rw app_nil_r
                | rw remove_nvars_cons_r; boolvar; allrw not_over_or; repnd; spFalseHyp
         ]; GC).
  repeat (rw remove_nvars_cons_l_weak; auto); repeat (rw remove_nvars_nil_l).
Qed.

Lemma free_vars_per_function_rel {o} :
  forall A B,
    eqvars (free_vars (@mk_per_function_rel o A B))
           (free_vars A ++ free_vars B).
Proof.
  introv.
  rw @free_vars_per_function_rel_eq.
  rw eqvars_prop; introv.
  repeat (rw in_app_iff); split; sp.
Qed.

Lemma free_vars_per_function {o} :
  forall A B, eqvars (free_vars (@mk_per_function o A B)) (free_vars A ++ free_vars B).
Proof.
  introv.
  unfold mk_per_function.
  rewrite free_vars_mk_pertype.
  apply free_vars_per_function_rel; auto.
Qed.

Lemma free_vars_mk_per_function {o} :
  forall A B,
    free_vars (@mk_per_function o A B)
    = free_vars (mk_per_function_rel A B).
Proof.
  introv.
  unfold mk_per_function.
  rw @free_vars_mk_pertype; sp.
Qed.

Lemma free_vars_iper_function_rel_eq {o} :
  forall A B,
    free_vars (@mk_iper_function_rel o A B)
    = free_vars A ++ free_vars B ++ free_vars B ++ free_vars B.
Proof.
  introv.
  unfold mk_iper_function_rel.
  remember (newvars5 [A,B]); repnd.
  apply newvars5_prop2 in Heqp; simpl in Heqp.
  repeat (rw app_nil_r in Heqp); repeat (rw in_app_iff in Heqp).
  repeat (rw not_over_or in Heqp); repnd.
  repeat rw @free_vars_lam.
  unfold mk_per_function_base.
  rw @free_vars_isect.
  rw @free_vars_isect.
  rw @free_vars_isect.
  rw @free_vars_uand.
  allrw @free_vars_equality.
  allrw @free_vars_tequality.
  allrw @free_vars_apply; simpl.
  repeat (first [ rw remove_nvars_app_r
                | rw remove_nvars_app_l; simpl
                | rw remove_nvars_nil_r
                | rw app_nil_r
                | rw remove_nvars_cons_r; boolvar; allrw not_over_or; repnd; spFalseHyp
         ]; GC).
  repeat (rw remove_nvars_cons_l_weak; auto); repeat (rw remove_nvars_nil_l).
Qed.

Lemma free_vars_iper_function_rel {o} :
  forall A B,
    eqvars (free_vars (@mk_iper_function_rel o A B))
           (free_vars A ++ free_vars B).
Proof.
  introv.
  rw @free_vars_iper_function_rel_eq.
  rw eqvars_prop; introv.
  repeat (rw in_app_iff); split; sp.
Qed.

Lemma free_vars_iper_function {o} :
  forall A B, eqvars (free_vars (@mk_iper_function o A B)) (free_vars A ++ free_vars B).
Proof.
  introv.
  unfold mk_iper_function.
  rewrite free_vars_mk_ipertype.
  apply free_vars_iper_function_rel; auto.
Qed.

Lemma free_vars_mk_iper_function {o} :
  forall A B,
    free_vars (@mk_iper_function o A B)
    = free_vars (mk_iper_function_rel A B).
Proof.
  introv.
  unfold mk_iper_function.
  rw @free_vars_mk_ipertype; sp.
Qed.

Lemma free_vars_sper_function {o} :
  forall A B, eqvars (free_vars (@mk_sper_function o A B)) (free_vars A ++ free_vars B).
Proof.
  introv.
  unfold mk_sper_function.
  rewrite free_vars_mk_spertype.
  apply free_vars_iper_function_rel; auto.
Qed.

Lemma free_vars_mk_sper_function {o} :
  forall A B,
    free_vars (@mk_sper_function o A B)
    = free_vars (mk_iper_function_rel A B).
Proof.
  introv.
  unfold mk_sper_function.
  rw @free_vars_mk_spertype; sp.
Qed.




(* image type *)


Definition mk_per_image_rel {o} (T f : @NTerm o) :=
  match newvars4 [T,f] with
    | (va,vb,vx,vy) =>
        let C1 := mk_cequiv (mk_var vx) (mk_apply f (mk_var va)) in
        let C2 := mk_cequiv (mk_var vy) (mk_apply f (mk_var vb)) in
        let C3 := mk_equality (mk_var va) (mk_var vb) T in
        let U := mk_uand C1 (mk_uand C2 C3) in
        let E := mk_exists mk_base va (mk_exists mk_base vb U) in
          mk_lam vx (mk_lam vy E)
  end.

Definition mk_per_image {o} (T f : @NTerm o) :=
  mk_pertype (mk_per_image_rel T f).
