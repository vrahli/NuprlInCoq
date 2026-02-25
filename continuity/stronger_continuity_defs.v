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


Require Export csubst7.
Require Export continuity_type.
Require Export per_props_set.
Require Export per_props_union.
Require Export per_props_nat.
Require Export alphaeq3.


(* n:Nat -> (Nat_n -> Nat) -> (Nat + Unit) *)
Definition modulus_fun_type {o} : @CTerm o :=
  mkc_function
    mkc_tnat
    nvarx
    (mkcv_fun
       [nvarx]
       (mkcv_fun [nvarx] (mkcv_natk [nvarx] (mkc_var nvarx)) (mkcv_tnat [nvarx]))
       (mk_cv [nvarx] (mkc_union mkc_tnat mkc_unit))).

Definition strong_continuous {o} lib (F : @CTerm o) :=
  {M : CTerm
    & member lib M modulus_fun_type
    # forall (f : CTerm),
        member lib f nat2nat
        -> {n : nat
            & equality lib
                       (mkc_apply2 M (mkc_nat n) f)
                       (mkc_inl (mkc_apply F f))
                       (mkc_union mkc_tnat mkc_unit)
            # (forall (m : nat),
                 inhabited_type lib (mkc_assert (mkc_isl (mkc_apply2 M (mkc_nat m) f)))
                 -> m = n)}}.

(**

  [strong_continuous] should be derivable from [simple_strong_continuous]
  using [M' n f = primrec(n, M n f, \i.\r.if isl(M i f) then inr() else r)]
  to instantiate [strong_continuous] and
  where [M] comes from [simple_strong_continuous].

*)
Definition simple_strong_continuous {o} lib (F : @CTerm o) :=
  {M : CTerm
    & member lib M modulus_fun_type
    # forall (f : CTerm),
        member lib f nat2nat
        -> {n : nat
            & equality lib
                       (mkc_apply2 M (mkc_nat n) f)
                       (mkc_inl (mkc_apply F f))
                       (mkc_union mkc_tnat mkc_unit) }}.

Definition agree_upto_red_bc_nat {o} lib b (f g : @CTerm o) :=
  forall (t1 t2 : CTerm) (i : nat),
    reduces_toc lib t1 (mkc_nat i)
    -> reduces_toc lib t2 (mkc_nat i)
    -> i < b
    -> equality_of_int_tt lib (mkc_apply f t1) (mkc_apply g t2).

Lemma agree_upto_red_bc_nat_implies_equal_in_natk2nat {o} :
  forall lib b (f g : @CTerm o),
    member lib f nat2nat
    -> member lib g nat2nat
    -> agree_upto_red_bc_nat lib b f g
    -> equality lib f g (natk2nat (mkc_nat b)).
Proof.
  introv mf mg agree.
  unfold natk2nat.
  apply equality_in_fun; dands.
  - apply type_mkc_natk.
    exists (Z.of_nat b); spcast.
    rw @mkc_nat_eq.
    apply computes_to_valc_refl; eauto with slow.
  - intro inh; apply type_tnat.
  - introv e.
    apply equality_in_natk in e; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in e3; eauto with slow.
    rw @mkc_nat_eq in e3; ginv.
    assert (m < b) as l by lia; clear e1.
    apply equality_in_tnat.
    unfold equality_of_nat.

    unfold agree_upto_red_bc_nat in agree.
    pose proof (agree a a' m) as h; repeat (autodimp h hyp); eauto 3 with slow.
    unfold equality_of_int_tt in h; exrepnd.

    allrw @equality_in_fun; repnd; GC.
    pose proof (mf a a) as k1; autodimp k1 hyp.
    { apply equality_in_tnat; unfold equality_of_nat.
      exists m; dands; spcast; auto. }
    pose proof (mg a' a') as k2; autodimp k2 hyp.
    { apply equality_in_tnat; unfold equality_of_nat.
      exists m; dands; spcast; auto. }
    allrw @equality_in_tnat; allunfold @equality_of_nat; exrepnd; GC; spcast.
    allrw @mkc_nat_eq.
    computes_to_eqval.

    exists k0.
    allrw @mkc_nat_eq; dands; spcast; auto.
Qed.

Definition continuous_nat {o} lib (F : @CTerm o) :=
  forall f,
    member lib f nat2nat
    -> {b : nat
        & forall g,
            member lib g nat2nat
            -> agree_upto_red_bc_nat lib b f g
            -> equality_of_int_tt lib (mkc_apply F f) (mkc_apply F g)}.

Lemma strong_continuous_implies_continuous {o} :
  forall lib (F : @CTerm o),
    strong_continuous lib F -> continuous_nat lib F.
Proof.
  introv cont.
  unfold strong_continuous in cont.
  unfold continuous_nat.
  destruct cont as [M cont]; destruct cont as [mM cont].
  introv mf.
  applydup cont in mf; exrepnd.

  exists n.
  introv mg agree.

  applydup cont in mg; exrepnd.
  clear cont.

  pose proof (agree_upto_red_bc_nat_implies_equal_in_natk2nat lib n f g) as e.
  repeat (autodimp e hyp).
  unfold modulus_fun_type in mM.
  apply equality_in_function2 in mM; repnd; clear mM0.

  pose proof (mM (mkc_nat n) (mkc_nat n)) as ap.
  autodimp ap hyp.
  { apply equality_in_tnat; unfold equality_of_nat.
    exists n; dands; spcast; apply computes_to_valc_refl; eauto with slow. }
  eapply alphaeqc_preserving_equality in ap;[|apply mkcv_fun_substc].
  allrw @csubst_mk_cv.
  eapply alphaeqc_preserving_equality in ap;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply mkcv_fun_substc].
  allrw @mkcv_tnat_substc.
  eapply alphaeqc_preserving_equality in ap;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply mkcv_natk_substc].
  allrw @mkc_var_substc.
  fold (@natk2nat o (mkc_nat n)) in ap.

  apply equality_in_fun in ap; repnd.
  clear ap0 ap1.
  pose proof (ap f g e) as equn.

  allrw <- @mkc_apply2_eq.
  assert (equality
            lib
            (mkc_apply2 M (mkc_nat n) g)
            (mkc_inl (mkc_apply F f))
            (mkc_union mkc_tnat mkc_unit)) as e2.
  { eapply equality_trans;[apply equality_sym;exact equn|auto]. }

  apply implies_isl_in_bool in e2.
  eapply equality_respects_cequivc_right in e2;
    [|eapply computes_to_valc_inl_implies_cequivc_isl_tt;
       apply computes_to_valc_refl;
       apply iscvalue_mkc_inl].

  apply equality_tt_in_bool_implies_cequiv in e2; spcast.

  pose proof (mg1 n) as k.
  autodimp k hyp.
  { spcast.
    eapply inhabited_type_cequivc;
      [apply cequivc_mkc_assert;apply cequivc_sym; exact e2|].
    eapply inhabited_type_cequivc;
      [apply cequivc_sym;apply mkc_assert_tt|].
    apply inhabited_type_mkc_unit. }
  subst n0.

  assert (equality
            lib
            (mkc_inl (mkc_apply F f))
            (mkc_inl (mkc_apply F g))
            (mkc_union mkc_tnat mkc_unit)) as eap.
  { eapply equality_trans;[apply equality_sym; exact mf0|].
    eapply equality_trans;[exact equn|]; auto. }

  apply equality_mkc_inl_implies in eap.
  apply equality_in_tnat in eap.
  apply equality_of_nat_implies_equality_of_int in eap.
  apply equality_of_int_imp_tt in eap; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
