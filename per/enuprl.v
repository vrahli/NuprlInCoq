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

  Authors: Vincent Rahli

*)


Require Export nuprl.


(* extensional Nuprl *)

Definition eunivi_eq {o} lib ts (A A' : @CTerm o) :=
  { eqa , eqa' : per(o)
  , close lib ts A A eqa
  # close lib ts A' A' eqa'
  # eqa <=2=> eqa' }.

Fixpoint eunivi {o} lib (i : nat) (T T' : @CTerm o) (eq : per(o)) : [U] :=
  match i with
  | 0 => False
  | S n =>
    (
      T ===>(lib) (mkc_uni n)
      # T' ===>(lib) (mkc_uni n)
      # eq <=2=> (eunivi_eq lib (eunivi lib n))
    )
    {+}
    eunivi lib n T T' eq
  end.

Lemma eunivi_mkc_uni {o} :
  forall lib (i : nat),
    @eunivi
      o
      lib
      (S i)
      (mkc_uni i)
      (mkc_uni i)
      (eunivi_eq lib (eunivi lib i)).
Proof.
  introv.
  simpl.
  left.
  dands; try (spcast; apply computes_to_valc_refl; sp); tcsp.
Qed.

Lemma eunivi_exists {p} :
  forall lib i (T T' : @CTerm p) eq,
    eunivi lib i T T' eq
    -> {j : nat
        , j < i
        # T ===>(lib) (mkc_uni j)
        # T' ===>(lib) (mkc_uni j)
        # eq <=2=> (eunivi_eq lib (eunivi lib j)) }.
Proof.
  induction i; simpl; sp.
  - exists i; sp; omega.
  - discover; sp.
    exists j; sp; omega.
Qed.

Lemma eunivi_exists_iff {p} :
  forall lib i (T T' : @CTerm p) eq,
    eunivi lib i T T' eq
    <=> {j : nat
         , j < i
         # T ===>(lib) (mkc_uni j)
         # T' ===>(lib) (mkc_uni j)
         # eq <=2=> (eunivi_eq lib (eunivi lib j)) }.
Proof.
  sp; split; intro k.
  { apply eunivi_exists; auto. }
  revert T T' eq k.
  induction i; simpl; sp.
  destruct (eq_nat_dec j i); subst; sp.
  right.
  apply IHi with (T := T) (T' := T') (eq := eq); sp.
  exists j; sp; omega.
Qed.

Definition enuprli {p} lib (i : nat) := @close p lib (eunivi lib i).

Lemma fold_enuprli {p} :
  forall lib i, close lib (eunivi lib i) = @enuprli p lib i.
Proof.
  sp.
Qed.

Definition euniv {p} lib (T T' : @CTerm p) (eq : per) :=
  {i : nat , eunivi lib i T T' eq}.

Lemma eunivi_iff_euniv {p} :
  forall lib (a b : @CTerm p) eq,
    euniv lib a b eq <=> {i : nat , eunivi lib i a b eq}.
Proof.
  sp; split; sp.
Qed.

Definition enuprl {p} lib := @close p lib (euniv lib).

Lemma etypable_in_higher_univ {o} :
  forall lib i (T T' : @CTerm o) eq,
    enuprli lib i T T' eq
    -> forall k, enuprli lib (k + i) T T' eq.
Proof.
  unfold enuprli; introv cl; induction k; simpl; sp.

  remember (univi lib (k + i)) as u; revert Hequ.
  clear cl.
  close_cases (induction IHk using @close_ind') Case; sp; subst.

  - Case "CL_eq".
    apply CL_eq; unfold per_eq; sp.
    exists A B a1 a2 b1 b2 eqa; sp.

  - Case "CL_teq".
    apply CL_teq; unfold per_teq; sp.
    exists a1 a2 b1 b2 eqa; sp.

  - Case "CL_isect".
    apply CL_isect; unfold per_isect; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_func".
    apply CL_func; unfold per_func; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_disect".
    apply CL_disect; unfold per_disect; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_pertype".
    apply CL_pertype; unfold per_pertype; sp.
    exists R1 R2 eq1 eq2; sp.

  - Case "CL_ipertype".
    apply CL_ipertype; unfold per_ipertype; sp.
    exists R1 R2 eq1; sp.

  - Case "CL_spertype".
    apply CL_spertype; unfold per_spertype; sp.
    exists R1 R2 eq1; sp.

  - Case "CL_w".
    apply CL_w; unfold per_w; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_m".
    apply CL_m; unfold per_m; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_pw".
    apply CL_pw; unfold per_pw; sp.
    exists eqp eqa eqb p p' cp cp' ca ca'.
    exists cb cb' C C'; sp.
    unfold type_pfamily.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.

  - Case "CL_pm".
    apply CL_pm; unfold per_pm; sp.
    exists eqp eqa eqb p p' cp cp' ca ca'.
    exists cb cb' C C'; sp.
    unfold type_pfamily.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.

  - Case "CL_texc".
    apply CL_texc; unfold per_texc; sp.
    exists eqn eqe N N' E E'; sp.

  - Case "CL_union".
    apply CL_union; unfold per_union; sp.
    exists eqa eqb A A' B B'; sp.

    (*
  - Case "CL_eunion".
    apply CL_eunion; unfold per_eunion; sp.
    exists eqa1 eqa2 eqb1 eqb2 A A' B B'; sp.
     *)

  - Case "CL_image".
    apply CL_image; unfold per_image; sp.
    exists eqa A A' f f'; sp.

(*
  - Case "CL_eisect".
    apply CL_eisect; unfold per_eisect; sp.
    exists eqa eqa' eqb; sp.
    exists A A' v v' B B'.
    exists f g f' g'; sp.
*)

  - Case "CL_partial".
    apply CL_partial; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

  - Case "CL_admiss".
    apply CL_admiss; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

  - Case "CL_mono".
    apply CL_mono; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

  - Case "CL_ffatom".
    apply CL_ffatom; unfold per_ffatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa u0; sp.

  - Case "CL_effatom".
    apply CL_effatom; unfold per_effatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa; sp.

  - Case "CL_ffatoms".
    apply CL_ffatoms; unfold per_ffatoms; sp.
    exists A1 A2 x1 x2 eqa; sp.

  - Case "CL_set".
    apply CL_set; unfold per_set; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_tunion".
    apply CL_tunion; unfold per_tunion; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_product".
    apply CL_product; unfold per_product; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.
Qed.

Lemma etypable_in_higher_univ_r {p} :
  forall lib i (T T' : @CTerm p) eq,
    enuprli lib i T T' eq
    -> forall k, enuprli lib (i + k) T T' eq.
Proof.
  unfold enuprli; introv n; sp.
  generalize (etypable_in_higher_univ lib i T T' eq n k); sp.
  assert (k + i = i + k) as e by omega.
  rww e; sp.
Qed.

Lemma etypable_in_higher_univ_max {p} :
  forall lib i1 i2 (A1 B1 A2 B2 : @CTerm p) eq1 eq2,
    enuprli lib i1 A1 B1 eq1
    -> enuprli lib i2 A2 B2 eq2
    -> enuprli lib (Peano.max i1 i2) A1 B1 eq1
       # enuprli lib (Peano.max i1 i2) A2 B2 eq2.
Proof.
  introv n1 n2.
  generalize (etypable_in_higher_univ
                lib i1 A1 B1 eq1 n1 ((Peano.max i1 i2) - i1));
    intro k1.
  generalize (etypable_in_higher_univ
                lib i2 A2 B2 eq2 n2 ((Peano.max i1 i2) - i2));
    intro k2.
  assert (((Peano.max i1 i2) - i1) + i1 = Peano.max i1 i2) as max1.
  apply minus_plus_n; sp.
  apply max_prop1.
  assert (((Peano.max i1 i2) - i2) + i2 = Peano.max i1 i2) as max2.
  apply minus_plus_n; sp.
  apply max_prop2.
  rw max1 in k1.
  rw max2 in k2.
  sp.
Qed.

Lemma euni_in_higher_univ {p} :
  forall lib i (T T' : @CTerm p) eq,
    eunivi lib i T T' eq
    -> forall k, eunivi lib (k + i) T T' eq.
Proof.
  induction k; simpl; sp.
Qed.

Lemma euni_in_higher_univ_r {p} :
  forall lib i (T T' : @CTerm p) eq,
    eunivi lib i T T' eq
    -> forall k, eunivi lib (i + k) T T' eq.
Proof.
  introv u; sp.
  generalize (euni_in_higher_univ lib i T T' eq u k); sp.
  assert (k + i = i + k) as e by omega.
  rww e; sp.
Qed.

Lemma enuprli_implies_nuprl {pp} :
  forall lib (a b : @CTerm pp) i eq,
    enuprli lib i a b eq
    -> enuprl lib a b eq.
Proof.
  unfold enuprli, enuprl; introv n.
  remember (eunivi lib i) as k.
  revert i Heqk.
  close_cases (induction n using @close_ind') Case; sp; subst.

  - Case "CL_init".
    apply CL_init.
    exists i; sp.

  - Case "CL_eq".
    apply CL_eq.
    unfold per_eq; sp.
    exists A B a1 a2 b1 b2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_teq".
    apply CL_teq.
    unfold per_teq; sp.
    exists a1 a2 b1 b2 eqa; sp.
    apply IHn1 with (i0 := i); sp.
    apply IHn2 with (i0 := i); sp.
    apply IHn3 with (i0 := i); sp.

  - Case "CL_isect".
    apply CL_isect.
    unfold per_isect, type_family; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_func".
    apply CL_func.
    unfold per_func, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_disect".
    apply CL_disect.
    unfold per_disect, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pertype".
    apply CL_pertype.
    unfold per_pertype; sp.
    exists R1 R2 eq1 eq2; sp.
    apply rec1 with (i0 := i); sp.
    apply rec2 with (i0 := i); sp.

  - Case "CL_ipertype".
    apply CL_ipertype.
    unfold per_ipertype; sp.
    exists R1 R2 eq1; sp.
    apply rec1 with (i0 := i); sp.

  - Case "CL_spertype".
    apply CL_spertype.
    unfold per_spertype; sp.
    exists R1 R2 eq1; sp.
    apply rec1 with (i0 := i); sp.
    apply rec2 with (i0 := i); sp.
    apply rec3 with (i0 := i); sp.

  - Case "CL_w".
    apply CL_w.
    unfold per_w, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_m".
    apply CL_m.
    unfold per_m, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pw".
    apply CL_pw.
    unfold per_pw, type_pfamily; sp.
    exists eqp eqa eqb.
    exists p p' cp cp' ca ca' cb cb'.
    exists C C'; sp.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply reca with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pm".
    apply CL_pm.
    unfold per_pm, type_pfamily; sp.
    exists eqp eqa eqb.
    exists p p' cp cp' ca ca' cb cb'.
    exists C C'; sp.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply reca with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_texc".
    apply CL_texc.
    unfold per_texc; sp.
    exists eqn eqe N N' E E'; sp.
    { apply IHn1 with (i0 := i); sp. }
    { apply IHn2 with (i0 := i); sp. }

  - Case "CL_union".
    apply CL_union.
    unfold per_union; sp.
    exists eqa eqb A A' B B'; sp.
    + apply IHn1 with (i0 := i); sp.
    + apply IHn2 with (i0 := i); sp.

      (*
  - Case "CL_eunion".
    apply CL_eunion.
    unfold per_eunion; sp.
    exists eqa1 eqa2 eqb1 eqb2 A A' B B'; sp.
    + apply IHn1 with (i0 := i); sp.
    + apply IHn2 with (i0 := i); sp.
    + apply IHn3 with (i0 := i); sp.
    + apply IHn4 with (i0 := i); sp.*)

  - Case "CL_image".
    apply CL_image.
    unfold per_image; sp.
    exists eqa A A' f f'; sp.
    apply IHn with (i0 := i); sp.

(*
  - Case "CL_eisect".
    apply CL_eisect.
    unfold per_eisect, etype_family; sp.
    exists eqa eqa' eqb; sp.
    exists A A' v v' B B'.
    exists f g f' g'; sp.
    apply IHn1 with (i0 := i); sp.
    apply IHn2 with (i0 := i); sp.
    apply recb with (i0 := i); sp.
    apply recb' with (i0 := i); sp.
*)

  - Case "CL_partial".
    apply CL_partial.
    unfold per_partial; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_admiss".
    apply CL_admiss.
    unfold per_admiss; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_mono".
    apply CL_mono.
    unfold per_mono; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_ffatom".
    apply CL_ffatom.
    unfold per_ffatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa u; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_effatom".
    apply CL_effatom.
    unfold per_effatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_ffatoms".
    apply CL_ffatoms.
    unfold per_ffatoms; sp.
    exists A1 A2 x1 x2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_set".
    apply CL_set.
    unfold per_set, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_tunion".
    apply CL_tunion.
    unfold per_tunion, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_product".
    apply CL_product.
    unfold per_product, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.
Qed.

Definition etequality {p} lib (T1 T2 : @CTerm p) :=
  { eq : per , enuprl lib T1 T2 eq }.

Definition etype {p} lib (T : @CTerm p) := etequality lib T T.

Definition eequality {p} lib (t1 t2 T : @CTerm p) :=
  { eq : per , enuprl lib T T eq # eq t1 t2 }.

Definition emember {p} lib (t T : @CTerm p) := eequality lib t t T.

Definition etequalityi {p} lib i (T1 T2 : @CTerm p) := eequality lib T1 T2 (mkc_uni i).

Definition etypei {p} lib i (T : @CTerm p) := etequalityi lib i T T.

Definition eequorsq {p} lib (t1 t2 T : @CTerm p) := eequality lib t1 t2 T {+} ccequivc lib t1 t2.
Definition eequorsq2 {p} lib (t1 t2 t3 t4 T : @CTerm p) := eequorsq lib t1 t2 T # eequorsq lib t3 t4 T.

Lemma fold_eequorsq {p} :
  forall lib (t1 t2 T : @CTerm p),
    (eequality lib t1 t2 T {+} ccequivc lib t1 t2) = eequorsq lib t1 t2 T.
Proof. sp. Qed.

Lemma fold_eequorsq2 {p} :
  forall lib (t1 t2 t3 t4 T : @CTerm p),
    (eequorsq lib t1 t2 T # eequorsq lib t3 t4 T) = eequorsq2 lib t1 t2 t3 t4 T.
Proof. sp. Qed.

Definition eeqtypes {p} lib lvl (T1 T2 : @CTerm p) :=
  match lvl with
    | nolvl => etequality lib T1 T2
    | atlvl l => etequalityi lib l T1 T2
  end.

Definition eltype {p} lib l (T : @CTerm p) := eeqtypes lib l T T.
