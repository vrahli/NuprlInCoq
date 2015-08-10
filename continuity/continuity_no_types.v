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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export continuity.
Require Export per_props.


Definition of_type_int {o} lib (t : @NTerm o) :=
  {z : Z & reduces_to lib t (mk_integer z)}.

Definition of_type_int_to_val {o} lib (f : @NTerm o) :=
  forall a,
    of_type_int lib a
    -> {v : NTerm
        & reduces_to lib (mk_apply f a) v
        # isvalue_like v}.

Definition of_type_int_to_val_TO_int {o} lib (F : @NTerm o) :=
  forall f,
    of_type_int_to_val lib f
    -> {z : Z & reduces_to lib (mk_apply F f) (mk_integer z)}.

Definition continuous {o} lib (F : @NTerm o) :=
  forall f,
    of_type_int_to_val lib f
    -> {b : nat
        & forall g,
            of_type_int_to_val lib g
            -> (forall i : Z,
                  Z.abs_nat i < b
                  -> {v : NTerm (* (isvalue_like v)? *)
                      & reduces_to lib (mk_apply f (mk_integer i)) v
                      # reduces_to lib (mk_apply g (mk_integer i)) v})
            -> {z : Z
                & reduces_to lib (mk_apply F f) (mk_integer z)
                # reduces_to lib (mk_apply F g) (mk_integer z)}}.

Lemma of_type_int_force_int {o} :
  forall lib (t : @NTerm o),
    of_type_int lib t
    -> of_type_int lib (force_int t).
Proof.
  introv h.
  allunfold @of_type_int; exrepnd.
  exists z.
  unfold reduces_to in h0; exrepnd.
  revert dependent t.
  induction k; introv r.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists 1.
    allrw @reduces_in_atmost_k_steps_S.
    exists (@mk_integer o z); dands; eauto with slow.
    + simpl.
      unfold compute_step_arith; simpl.
      rw <- Zplus_0_r_reverse; auto.
    + rw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply IHk in r0; exrepnd.
    apply (reduces_to_trans _ _ (force_int u)); auto.
    apply reduces_to_prinarg; eauto with slow.
Qed.
Hint Resolve of_type_int_force_int : slow.

Lemma alpha_eq_preserves_isvalue_like {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> isvalue_like a
    -> isvalue_like b.
Proof.
  introv aeq iv.
  unfold isvalue_like in iv.
  dorn iv;[|dorn iv].
  - apply iscan_implies in iv; exrepnd; subst.
    inversion aeq; subst; left; sp.
  - apply isexc_implies2 in iv; exrepnd; subst.
    inversion aeq; subst; right; left; sp.
  - apply ismrk_implies2 in iv; exrepnd; subst.
    inversion aeq; subst; right; right; sp.
Qed.

Lemma add_force_int {o} :
  forall lib (F f : @NTerm o) x z,
    of_type_int_to_val_TO_int lib F
    -> of_type_int_to_val lib f
    -> !LIn x (free_vars f)
    -> reduces_to
         lib
         (mk_apply F f)
         (mk_integer z)
    -> reduces_to
         lib
         (mk_apply F (mk_lam x (mk_apply f (force_int (mk_var x)))))
         (mk_integer z).
Proof.
  introv tF tf ni r.

  pose proof (tF (mk_lam x (mk_apply f (force_int (mk_var x))))) as h.
  autodimp h hyp.

  { introv ta.
    pose proof (tf (force_int a)) as h; exrepnd.

    autodimp h hyp; eauto with slow.
    exrepnd.

    destruct (dec_disjointv (bound_vars f) (free_vars a)) as [d|d].

    - exists v; dands; auto.

      apply (reduces_to_if_split2
               _ _
               (mk_apply f (force_int a))); auto.

      simpl; unfold apply_bterm, lsubst; simpl.
      allrw app_nil_r; boolvar; tcsp.
      rw @lsubst_aux_trivial_cl_term; simpl; auto.
      rw disjoint_singleton_r; auto.

    - pose proof (change_bvars_alpha_spec f (free_vars a)) as h.
      simpl in h; repnd.
      remember (change_bvars_alpha (free_vars a) f) as f'.

      assert (alpha_eq (mk_apply f (force_int a)) (mk_apply f' (force_int a))) as aeq.

      { prove_alpha_eq4; introv p.
        destruct n;[|destruct n]; cpx.
        apply alphaeqbt_nilv2; auto. }

      pose proof (reduces_to_steps_alpha
                    lib
                    (mk_apply f (force_int a))
                    (mk_apply f' (force_int a))
                    v) as q.
      repeat (autodimp q hyp).
      exrepnd.

      pose proof (alpha_eq_preserves_isvalue_like v u) as iv.
      repeat (autodimp iv hyp).

      applydup @alphaeq_preserves_free_vars in h.

      SearchAbout alpha_eq free_vars.

      exists u.
      dands; auto.

      apply (reduces_to_if_split2
               _ _
               (mk_apply f' (force_int a))); auto.

      simpl; unfold apply_bterm, lsubst; simpl.
      allrw app_nil_r; boolvar; tcsp.
      unfold var_ren; simpl.
      rw @lsubst_aux_nil.
      rw <- Heqf'.
      rw @lsubst_aux_trivial_cl_term; simpl; auto.
      allrw <-.
      rw disjoint_singleton_r; auto. }

  exrepnd.
Qed.

(*

  F f -> z
  => (* by typing *)
  F (\x.f(x+0)) -> z
  => (* by comp_force_int_app_F *)
  exists b. forall e.
    F (\x.f(let v:=x in if |v|<b then v else e)) -> z
    => (* if e cannot get caught, because the 2 functions agree upto b *)
    F (\x.g(let v:=x in if |v|<b then v else e)) -> z
    => (* because the exception e is not raised, the term computes to z *)
    F (\x.g(x+0)) -> z
    => (* by typing *)
    F g -> z

*)
Lemma continuity_axiom {o} :
  forall lib (F : @NTerm o),
    of_type_int_to_val_TO_int lib F
    -> continuous lib F.
Proof.
  introv type_of_F type_of_f.
  pose proof (type_of_F f type_of_f) as h; exrepnd.

Qed.