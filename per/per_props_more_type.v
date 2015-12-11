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


Require Export per_props.


Lemma mkc_pertype_equality_in_uni :
  forall R1 R2 i,
    equality (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
    <=> (forall x y, member (mkc_apply2 R1 x y) (mkc_uni i))
      # (forall x y, member (mkc_apply2 R2 x y) (mkc_uni i))
      # (forall x y,
           inhabited_type (mkc_apply2 R1 x y)
           <=>
           inhabited_type (mkc_apply2 R2 x y))
      # is_per_type R1.
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    dest_per.
    allfold nuprl; allfold (nuprli j0).
    computes_to_value_isvalue.

    dands; introv.

    generalize (typ1 x y); intro k.
    unfold member, equality.
    exists eq; sp.
    allrw.
    exists (eq1 x y); sp.

    generalize (typ2 x y); intro k.
    unfold member, equality.
    exists eq; sp.
    allrw.
    exists (eq2 x y); sp.

    generalize (typ1 x y); intro k1.
    generalize (typ2 x y); intro k2.
    allapply nuprli_implies_nuprl.

    generalize (inhabited_type_iff (mkc_apply2 R0 x y) (mkc_apply2 R3 x y) (eq1 x y) (eq2 x y)); intro iff; repeat (dest_imp iff hyp).
    rw <- iff; sp.

    generalize (is_per_type_iff_is_per R0 eq1); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (typ1 x y); intro k1.
    allapply nuprli_implies_nuprl; sp.
    rw <- iff; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per , close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; spcast; try computes_to_value_refl.

    fold (nuprli i).

    assert (forall x y : CTerm,
              {eq : per
               , nuprli i (mkc_apply2 R1 x y) (mkc_apply2 R1 x y) eq}) as f1.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (nuprli j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    assert (forall x y : CTerm,
              {eq : per
               , nuprli i (mkc_apply2 R2 x y) (mkc_apply2 R2 x y) eq}) as f2.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ1.
    generalize (equ1 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (nuprli j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    generalize (choice_spteqi i (mkc_apply2 R1) (mkc_apply2 R1)); intro fn1.
    generalize (choice_spteqi i (mkc_apply2 R2) (mkc_apply2 R2)); intro fn2.
    dest_imp fn1 hyp.
    dest_imp fn2 hyp.
    exrepnd.

    exists (fun t t' => inhabited (f0 t t')).
    apply CL_pertype.
    fold (nuprli i).
    unfold per_pertype.
    exists R1 R2
           (fun t t' => f0 t t')
           (fun t t' => f t t');
      sp; try (spcast; computes_to_value_refl); try (fold nuprl).

    generalize (fn0 x y); intro n1.
    generalize (fn2 x y); intro n2.
    allapply nuprli_implies_nuprl.
    generalize (inhabited_type_iff (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (f0 x y) (f x y)); intro iff; repeat (dest_imp iff hyp).
    rw iff; sp.

    generalize (is_per_type_iff_is_per R1 f0); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (fn2 x y); intro k1.
    allapply nuprli_implies_nuprl; sp.
    rw iff; sp.
(*Error: Universe inconsistency.*)
[Admitted.]

(*
Lemma mkc_uni_in_nuprl :
  forall i : nat,
    nuprl (mkc_uni i)
          (mkc_uni i)
          (fun A A' => {eqa : per , close (univi i) A A' eqa}).
Proof.
  intro.
  apply CL_init.
  exists (S i); simpl.
  left; sp; spcast; apply computes_to_valc_refl; sp.
Qed.

Lemma nuprl_mkc_uni :
  forall i : nat,
    {eq : per , nuprl (mkc_uni i) (mkc_uni i) eq}.
Proof.
  intros.
  exists (fun A A' => {eqa : per , close (univi i) A A' eqa}).
  apply mkc_uni_in_nuprl.
Qed.
*)

Lemma tequality_mkc_uni :
  forall i : nat, tequality (mkc_uni i) (mkc_uni i).
Proof.
(*
  generalize nuprl_mkc_uni; sp.
(*Error: Universe inconsistency.*)
*)
[Admitted.]

Lemma mkc_sqequal_equality_in_uni :
  forall a b c d i,
    equality (mkc_sqequal a b) (mkc_sqequal c d) (mkc_uni i)
    <=>
    (ccequivc a b <=> ccequivc c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    allunfold nuprl.
    inversion e1; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per , close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' => ccomputes_to_valc t mkc_axiom
                      # ccomputes_to_valc t' mkc_axiom
                      # ccequivc a b).
    apply CL_sqeq; unfold per_sqequal.
    exists a b c d; sp; spcast; try computes_to_value_refl.
(*Error: Universe inconsistency.*)
[Admitted.]

Lemma mkc_sqle_equality_in_uni :
  forall a b c d i,
    equality (mkc_sqle a b) (mkc_sqle c d) (mkc_uni i)
    <=>
    (capproxc a b <=> capproxc c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per , close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' => ccomputes_to_valc t mkc_axiom
                      # ccomputes_to_valc t' mkc_axiom
                      # capproxc a b).
    apply CL_sqle; unfold per_sqle.
    exists a b c d; sp; spcast; try computes_to_value_refl.
(*Error: Universe inconsistency.*)
[Admitted.]

(*
Lemma tequality_in_uni_iff_tequality :
  forall T1 T2 i,
    tequality (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    <=> equorsq T1 T2 (mkc_uni i).
Proof.
  introv.
  allrw <- fold_mkc_member.
  rw tequality_mkc_equality.
  split; intro k; repnd; try (complete sp).

  dands; try (complete sp).
  apply tequality_mkc_uni.
  split; intro e.
  generalize (cequorsq_equality_trans2 T1 T1 T2 (mkc_uni i)); intro e1.
  repeat (dest_imp e1 hyp).
  apply equality_sym in e1.
  apply equality_refl in e1; sp.
  generalize (cequorsq_equality_trans1 T1 T2 T2 (mkc_uni i)); intro e1.
  repeat (dest_imp e1 hyp).
  apply equality_refl in e1; sp.
Qed.
*)

Lemma equality_in_uni_mkc_halts :
  forall i a b,
    equality (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    (chaltsc a <=> chaltsc b).
Proof.
  intros; repeat (rewrite <- fold_mkc_halts).
  rw mkc_sqle_equality_in_uni.
  allrw chasvaluec_as_capproxc; sp.
Qed.

Lemma cequorsq_mkc_halts_implies :
  forall i a b,
    equorsq (mkc_halts a) (mkc_halts b) (mkc_uni i)
    -> (chaltsc a <=> chaltsc b).
Proof.
  unfold equorsq; intros; sp;
  allrw equality_in_uni_mkc_halts; sp.
  uncast; allrw cequivc_decomp_halts; sp;
  split; sp; spcast; discover; sp.
Qed.

Lemma cequorsq_mkc_halts :
  forall i a b,
    equorsq (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    (chaltsc a <=> chaltsc b).
Proof.
  unfold equorsq; intros; split; sp; try right;
  allrw equality_in_uni_mkc_halts; sp; uncast;
  allrw cequivc_decomp_halts; try split; sp; spcast;
  discover; sp.
Abort.
(* This is not true in Prop with Cast around hasvalue *)
(*Qed.*)
