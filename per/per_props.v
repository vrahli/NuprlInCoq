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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)

(* begin hide *)


(* =============== Some general properties ================= *)

(*
(* This is not provable, because in general we can't find the type level
 * of a type family. *)
Lemma equality_in_uni_iff {p} :
  forall lib a b,
    {i : nat , @equality p lib a b (mkc_uni i)}
    <=> tequality lib a b.
Proof.
  sp; split; introv e; exrepnd.

  { apply equality_in_uni in e0; sp. }

  allunfold @tequality; allunfold @equality; exrepnd.
  unfold nuprl in e0; sp.
  remember (univ lib) as T.
  generalize HeqT; clear HeqT.
  close_cases (induction e0 using @close_ind') Case; intros HeqT; subst.

  - Case "CL_init".
    duniv i h.
    exists i (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    unfold nuprl.
    apply CL_init; unfold univ.
    exists (S i); simpl; left; sp; try (spcast; computes_to_value_refl).
    exists eq; sp.

  - Case "CL_int".
    exists 1 (fun A A' => {eqa : per(p) , close lib (univi lib 1) A A' eqa}); sp.
    unfold nuprl, univ.
    apply CL_init.
    exists 2; left; sp; try (spcast; computes_to_value_refl).
    exists eq; apply CL_int.
    allunfold @per_int; sp.

  - Case "CL_atom".
    admit.

  - Case "CL_uatom".
    admit.

  - Case "CL_base".
    admit.

  - Case "CL_approx".
    admit.

  - Case "CL_cequiv".
    admit.

  - Case "CL_aeq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_eq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_teq".
    admit.

  - Case "CL_isect".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_func".
    admit.

  - Case "CL_disect".
    admit.

  - Case "CL_pertype".
    admit.
(*Error: Universe inconsistency.*)
Abort.
*)


(* =============== More specific properties ================= *)

(* end hide *)

(* begin hide *)

(* end hide *)

(**

  As we proved a relation between the [equality] relation and the
  [mkc_equality] type, we can prove the followig result that relates
  the computational equality relation to the [mkc_cequiv] type.

 *)

(* begin hide *)



(*
Lemma equality_in_mkc_esquash :
  forall T a b,
    equality lib a b (mkc_esquash T)
    <=> (computes_to_valc a mkc_axiom
         # computes_to_valc b mkc_axiom
         # inhabited_type lib T).
Proof.
  introv; split; intro i.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl.
    computes_to_value_isvalue.
    rw X1 in i0; exrepnd; sp.
    apply inhabited_type_if_inhabited with (U := A1) (eq := eq1); sp.

  - repnd.
    unfold inhabited_type in i; exrepnd.
    unfold member, equality, nuprl in i2; exrepnd.
    allfold nuprl.
    unfold equality, nuprl.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited eq); sp.
    apply CL_esquash.
    unfold per_esquash.
    exists T T eq eq; sp; computes_to_value_refl.
    unfold inhabited; exists t; sp.
Qed.
*)

(*
Lemma tequality_mkc_esquash :
  forall T1 T2,
    tequality lib (mkc_esquash T1) (mkc_esquash T2)
    <=> (type T1
         # type T2
         # (inhabited_type lib T1 <=> inhabited_type lib T2)).
Proof.
  introv; split; intro i; repnd.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl.
    computes_to_value_isvalue; sp.

    unfold type, tequality.
    exists eq1; sp.

    unfold type, tequality.
    exists eq2; sp.

    allapply inhabited_type_iff_inhabited.
    rw <- X3; rw <- X4; sp.

  - unfold tequality, nuprl.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited (projT1 i0)).
    apply CL_esquash; unfold per_esquash.
    fold nuprl.
    exists T1 T2 (projT1 i0) (projT1 i1).
    unfold type, tequality in i0, i1; exrepnd; simpl.
    sp; try computes_to_value_refl.
    allapply inhabited_type_iff_inhabited.
    allrw; sp.
Qed.
*)

(*
Lemma mkc_esquash_equality_in_uni :
  forall T1 T2 i,
    equality lib (mkc_esquash T1) (mkc_esquash T2) (mkc_uni i)
    <=> member T1 (mkc_uni i)
      # member T2 (mkc_uni i)
      # (inhabited_type lib T1
         <=>
         inhabited_type lib T2).
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    inversion X; exrepd.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl; allfold (nuprli j).
    computes_to_value_isvalue.

    dands; intros.

    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists eq1; sp.

    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists eq2; sp.

    split; intro l.

    apply inhabited_type_if_inhabited with (U := A2) (eq := eq2); sp.
    apply nuprli_implies_nuprl in X6; sp.
    rw <- X7.
    apply inhabited_if_inhabited_type with (U := A1) (T := A1); sp.
    apply nuprli_implies_nuprl in X5; sp.

    apply inhabited_type_if_inhabited with (U := A1) (eq := eq1); sp.
    apply nuprli_implies_nuprl in X5; sp.
    rw X7.
    apply inhabited_if_inhabited_type with (U := A2) (T := A2); sp.
    apply nuprli_implies_nuprl in X6; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per & close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; try computes_to_value_refl.

    fold (nuprli i).

    assert {eq : per & nuprli i T1 T1 eq} as f1.
    intros.
    unfold member, equality in equ0; exrepnd.
    inversion equ0; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ2; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    assert {eq : per & nuprli i T2 T2 eq} as f2.
    intros.
    unfold member, equality in equ1; exrepnd.
    inversion equ1; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ2; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    exrepnd.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited eq0).
    apply CL_esquash.
    fold (nuprli i).
    unfold per_esquash.
    exists T1 T2 eq0 eq;
      sp; try (computes_to_value_refl); try (fold nuprl).

    split; intro p.

    apply inhabited_if_inhabited_type with (U := T2) (T := T2); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
    rw <- equ.
    apply inhabited_type_if_inhabited with (U := T1) (eq := eq0); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).

    apply inhabited_if_inhabited_type with (U := T1) (T := T1); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
    rw equ.
    apply inhabited_type_if_inhabited with (U := T2) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
(*Error: Universe inconsistency.*)
[Admitted.]
*)

(*
Lemma tequality_esquash_apply2_if_tequality_pertype :
  forall R1 R2 t1 t2 t3 t4,
    tequality
      (mkc_equality t1 t2 (mkc_pertype R1))
      (mkc_equality t3 t4 (mkc_pertype R2))
    -> tequality
         (mkc_esquash (mkc_apply2 R1 t1 t2))
         (mkc_esquash (mkc_apply2 R2 t3 t4)).
Proof.
  introv teq.
  allrw tequality_mkc_equality; repnd.
  allrw tequality_mkc_pertype; repnd.
  allrw equality_in_mkc_pertype; repnd.
  rw tequality_mkc_esquash; dands; try (complete sp).
  destruct teq1.
  split; intro i.

  dest_imp p hyp.

  dest_imp p0 hyp.
  dands; try (complete sp).
  apply is_per_type_iff with (R1 := R1); sp.
Qed.
*)

(*
Lemma member_in_mkc_esquash :
  forall a T,
    member a (mkc_esquash T)
    <=> (computes_to_valc a mkc_axiom
         # inhabited_type lib T).
Proof.
  intros.
  unfold member.
  rw equality_in_mkc_esquash; split; sp.
Qed.
*)

(*
Lemma member_esquash_iff :
  forall T,
    inhabited_type lib T <=> member lib mkc_axiom (mkc_esquash T).
Proof.
  intros.
  rw member_in_mkc_esquash; split; sp.
  computes_to_value_refl.
Qed.
*)

(* end hide *)
