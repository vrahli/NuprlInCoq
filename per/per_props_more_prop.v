(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export per_props.


Lemma mkc_pertype_equality_in_uni {p} :
  forall lib (R1 R2 : @CTerm p) i,
    equality lib (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
    <=> (forall x y, member lib (mkc_apply2 R1 x y) (mkc_uni i))
      # (forall x y, member lib (mkc_apply2 R2 x y) (mkc_uni i))
      # (forall x y,
           inhabited_type lib (mkc_apply2 R1 x y)
           <=>
           inhabited_type lib (mkc_apply2 R2 x y))
      # is_per_type lib R1.
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    dest_per.
    allfold (@nuprl p); allfold (@nuprli p lib j0).
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
    allapply @nuprli_implies_nuprl.

    generalize (inhabited_type_iff lib (mkc_apply2 R0 x y) (mkc_apply2 R3 x y) (eq1 x y) (eq2 x y)); intro iff; repeat (dest_imp iff hyp).
    rw <- iff; sp.

    generalize (is_per_type_iff_is_per lib R0 eq1); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (typ1 x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    rw <- iff; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; spcast; try computes_to_value_refl.

    fold (@nuprli p lib i).

    assert (forall x y : CTerm,
              {eq : per
               , nuprli lib i (mkc_apply2 R1 x y) (mkc_apply2 R1 x y) eq}) as f1.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (@nuprli p lib j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    assert (forall x y : CTerm,
              {eq : per
               , nuprli lib i (mkc_apply2 R2 x y) (mkc_apply2 R2 x y) eq}) as f2.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ1.
    generalize (equ1 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (@nuprli p lib j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    generalize (choice_spteqi lib i (mkc_apply2 R1) (mkc_apply2 R1)); intro fn1.
    generalize (choice_spteqi lib i (mkc_apply2 R2) (mkc_apply2 R2)); intro fn2.
    dest_imp fn1 hyp.
    dest_imp fn2 hyp.
    exrepnd.

    exists (fun t t' => inhabited (f0 t t')).
    apply CL_pertype.
    fold (@nuprli p lib i).
    unfold per_pertype.
    exists R1 R2
           (fun t t' => f0 t t')
           (fun t t' => f t t');
      sp; try (spcast; computes_to_value_refl); try (fold nuprl).

    generalize (fn0 x y); intro n1.
    generalize (fn2 x y); intro n2.
    allapply @nuprli_implies_nuprl.
    generalize (inhabited_type_iff lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (f0 x y) (f x y)); intro iff; repeat (dest_imp iff hyp).
    rw iff; sp.

    generalize (is_per_type_iff_is_per lib R1 f0); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (fn2 x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    rw iff; sp.
Qed.

Lemma mkc_ipertype_equality_in_uni {p} :
  forall lib (R1 R2 : @CTerm p) i,
    equality lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
    <=> (forall x y, equality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (mkc_uni i))
        # is_per_type lib R1.
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib); allfold (@nuprli p lib j0).
    computes_to_value_isvalue.

    dands; introv.

    generalize (eqtyps x y); intro k.
    exists eq; sp; allrw.
    exists (eq1 x y); sp.

    generalize (is_per_type_iff_is_per lib R0 eq1); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (eqtyps x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    apply nuprl_refl in k1; sp.
    rw <- iff; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; spcast; try computes_to_value_refl.

    fold (@nuprli p lib i).

    assert (forall x y : CTerm,
              {eq : term-equality
               , nuprli lib i (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) eq}) as f1.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (@nuprli p lib j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    generalize (choice_spteqi lib i (mkc_apply2 R1) (mkc_apply2 R2)); intro fn1.
    dest_imp fn1 hyp.
    exrepnd.

    exists (pertype_eq f).
    apply CL_ipertype.
    fold (@nuprli p lib i).
    unfold per_ipertype.
    exists R1 R2 f;
      sp; try (spcast; computes_to_value_refl); try (fold nuprl).

    generalize (is_per_type_iff_is_per lib R1 f); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (fn0 x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    apply nuprl_refl in k1; sp.
    rw iff; sp.
Qed.

Lemma equality_nuprli {p} :
  forall lib (A B C : @CTerm p) i eq,
    equality lib A B (mkc_uni i)
    -> nuprli lib i A C eq
    -> nuprli lib i A B eq.
Proof.
  introv e n.
  unfold equality, nuprl in e; exrepnd.
  inversion e1; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepnd.
  computes_to_value_isvalue; GC.
  discover; exrepnd.
  allfold (@nuprli p lib j0).
  generalize (nuprli_uniquely_valued lib j0 j0 A A eqa eq); intro k.
  repeat (autodimp k hyp).
  apply nuprli_refl in h2; auto.
  apply nuprli_refl in n; auto.
  apply (nuprli_ext lib j0 A B eqa eq); auto.
Qed.

Lemma mkc_spertype_equality_in_uni {p} :
  forall lib (R1 R2 : @CTerm p) i,
    equality lib (mkc_spertype R1) (mkc_spertype R2) (mkc_uni i)
    <=> (forall x y, equality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (mkc_uni i))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 x z)
             -> equality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (mkc_uni i))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 y z)
             -> equality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (mkc_uni i))
        # is_per_type lib R1.
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    dest_per.
    allfold (@nuprl p); allfold (@nuprli p lib j0).
    computes_to_value_isvalue.

    dands; introv.

    generalize (eqtyps1 x y); intro k.
    exists eq; sp; allrw.
    exists (eq1 x y); sp.

    intro inh.
    generalize (eqtyps1 x z); intro n.
    apply inhabited_if_inhabited_type_i in n; auto.
    generalize (eqtyps2 x y z n); intro ni.
    exists eq; sp.
    allrw; exists (eq1 x y); sp.

    intro inh.
    generalize (eqtyps1 y z); intro n.
    apply inhabited_if_inhabited_type_i in n; auto.
    generalize (eqtyps3 x y z n); intro ni.
    exists eq; sp.
    allrw; exists (eq1 x y); sp.

    generalize (is_per_type_iff_is_per lib R0 eq1); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (eqtyps1 x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    apply nuprl_refl in k1; sp.
    rw <- iff; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; spcast; try computes_to_value_refl.

    fold (@nuprli p lib i).

    assert (forall x y : CTerm,
              {eq : term-equality
               , nuprli lib i (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) eq}) as f1.
    (* begin proof of the assert *)
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in k0; exrepnd.
    allfold (@nuprli p lib j0).
    exists eqa; sp.
    (* end of proof of the assert *)

    generalize (choice_spteqi lib i (mkc_apply2 R1) (mkc_apply2 R2)); intro fn1.
    dest_imp fn1 hyp.
    exrepnd.

    exists (pertype_eq f).
    apply CL_spertype.
    fold (@nuprli p lib i).
    unfold per_spertype.
    exists R1 R2 f;
      dands; introv;
      try (spcast; computes_to_value_refl);
      try (fold nuprl);
      try (complete sp).

    intro inh.
    generalize (fn0 x z); intro ni.
    apply inhabited_type_if_inhabited_i in ni; auto.
    generalize (equ1 x y z ni); intro e.
    generalize (fn0 x y); intro n.
    apply equality_nuprli with (C := mkc_apply2 R2 x y); auto.

    intro inh.
    generalize (fn0 y z); intro ni.
    apply inhabited_type_if_inhabited_i in ni; auto.
    generalize (equ2 x y z ni); intro e.
    generalize (fn0 x y); intro n.
    apply equality_nuprli with (C := mkc_apply2 R2 x y); auto.

    generalize (is_per_type_iff_is_per lib R1 f); introv iff.
    dest_imp iff hyp.
    intros.
    generalize (fn0 x y); intro k1.
    allapply @nuprli_implies_nuprl; sp.
    apply nuprl_refl in k1; sp.
    rw iff; sp.
Qed.

Lemma mkc_uni_in_nuprl {p} :
  forall lib (i : nat),
    nuprl lib (mkc_uni i)
          (mkc_uni i)
          (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}).
Proof.
  introv.
  apply CL_init.
  exists (S i); simpl.
  left; sp; spcast; apply computes_to_valc_refl; sp.
Qed.

Lemma nuprl_mkc_uni {p} :
  forall lib (i : nat),
    {eq : per(p) , nuprl lib (mkc_uni i) (mkc_uni i) eq}.
Proof.
  intros.
  exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}).
  apply mkc_uni_in_nuprl.
Qed.

Lemma tequality_mkc_uni {p} :
  forall lib (i : nat), @tequality p lib (mkc_uni i) (mkc_uni i).
Proof.
  generalize (@nuprl_mkc_uni p); sp.
Qed.

Lemma mkc_cequiv_equality_in_uni {p} :
  forall lib (a b c d : @CTerm p) i,
    equality lib (mkc_cequiv a b) (mkc_cequiv c d) (mkc_uni i)
    <=>
    (ccequivc lib a b <=> ccequivc lib c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    allunfold @nuprl.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' : @CTerm p => t ===>(lib) mkc_axiom
                      # t' ===>(lib) mkc_axiom
                      # ccequivc lib a b).
    apply CL_cequiv; unfold per_cequiv.
    exists a b c d; sp; spcast; try computes_to_value_refl.
Qed.

Lemma mkc_approx_equality_in_uni {p} :
  forall lib (a b c d : @CTerm p) i,
    equality lib (mkc_approx a b) (mkc_approx c d) (mkc_uni i)
    <=>
    (capproxc lib a b <=> capproxc lib c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' : @CTerm p => t ===>(lib) mkc_axiom
                      # t' ===>(lib) mkc_axiom
                      # capproxc lib a b).
    apply CL_approx; unfold per_approx.
    exists a b c d; sp; spcast; try computes_to_value_refl.
Qed.

(*
Lemma tequality_in_uni_iff_tequality {p} :
  forall (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    <=> equorsq T1 T2 (mkc_uni i).
Proof.
  introv.
  allrw <- @fold_mkc_member.
  rw @tequality_mkc_equality.
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

