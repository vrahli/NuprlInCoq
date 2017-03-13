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


Ltac dest_per :=
  match goal with
      [ H : per_pertype ?lib ?ts ?T ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let eq1    := fresh "eq1"    in
      let c1     := fresh "c1"     in
      let typ1   := fresh "typ1"   in
      let inhiff := fresh "inhiff" in
      let isper  := fresh "isper"  in
      let pereq  := fresh "pereq"  in
      unfold per_pertype in H;
        destruct H as [ R1     H ];
        destruct H as [ eq1    H ];
        destruct H as [ c1     H ];
        destruct H as [ typ1   H ];
        destruct H as [ inhiff H ];
        destruct H as [ isper  pereq ]
(*    | [ H : per_ipertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let R2     := fresh "R2"     in
      let eq1    := fresh "eq1"    in
      let c1     := fresh "c1"     in
      let c2     := fresh "c2"     in
      let typ1   := fresh "eqtyps" in
      let pereq  := fresh "pereq"  in
      unfold per_ipertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ isper pereq ]
    | [ H : per_spertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"      in
      let R2     := fresh "R2"      in
      let eq1    := fresh "eq1"     in
      let c1     := fresh "c1"      in
      let c2     := fresh "c2"      in
      let typ1   := fresh "eqtyps1" in
      let typ2   := fresh "eqtyps2" in
      let typ3   := fresh "eqtyps3" in
      let pereq  := fresh "pereq"   in
      unfold per_spertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ typ2  H ];
        destruct H as [ typ3  H ];
        destruct H as [ isper pereq ]*)
  end.

Hint Resolve iscvalue_mkc_pertype : slow.

Lemma equality_in_mkc_pertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_pertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # is_per_type lib R
         # (forall x y, type lib (mkc_apply2 R x y))).
Proof.
  intros; unfold inhabited_type; split; intro i; exrepnd.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    match goal with
    | [ H : per_pertype _ _ _ _ |- _ ] => rename H into q
    end.
    unfold per_pertype in q; exrepnd; computes_to_value_isvalue.
    allfold (@nuprl p lib).
    apply q1 in i0.
    unfold per_pertype_eq, inhabited in i0; exrepnd.

    dands.

    + exists t; unfold member, equality; exists (eqr t1 t2); sp.

    + pose proof (is_per_type_iff_is_per lib R0 eqr) as iff.
      dest_imp iff hyp.
      rw <- iff; sp.

    + introv.
      unfold type, tequality.
      exists (eqr x y); sp.

  - unfold member, equality in i2; exrepnd.
    pose proof (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R)) as fn.
    dest_imp fn hyp; exrepnd; eauto 2 with slow;[].
    pose proof (fn0 t1 t2) as n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (autodimp eqt hyp); eauto 3 with slow;[].

    exists (fun a b => inhabited (f a b)); sp;
      try (complete (rw eqt in i0; exists t; sp)).

    apply CL_pertype; unfold per_pertype.
    allfold (@nuprl p lib).
    exists R f; dands; spcast; eauto 3 with slow.

    pose proof (is_per_type_iff_is_per lib R f) as iff.
    autodimp iff hyp; eauto 3 with slow.
    rw iff; sp.
Qed.

Lemma tequality_mkc_pertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_pertype R1) (mkc_pertype R2)
    <=> (forall x y, type lib (mkc_apply2 R1 x y))
      # (forall x y, type lib (mkc_apply2 R2 x y))
      # (forall x y,
           inhabited_type lib (mkc_apply2 R1 x y)
           <=>
           inhabited_type lib (mkc_apply2 R2 x y))
      # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    unfold type, tequality; exists (eq1 x y); sp.
    unfold type, tequality; exists (eq2 x y); sp.

    generalize (inhabited_type_iff lib (mkc_apply2 R0 x y) (mkc_apply2 R3 x y) (eq1 x y) (eq2 x y)); intro iff; repeat (dest_imp iff hyp).
    rw <- iff; sp.

    generalize (is_per_type_iff_is_per lib R0 eq1); introv iff.
    dest_imp iff hyp.
    rw <- iff; sp.

  - repnd.
    unfold tequality, nuprl.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R1)); intro fn1.
    generalize (choice_spteq lib (mkc_apply2 R2) (mkc_apply2 R2)); intro fn2.
    dest_imp fn1 hyp; exrepnd.
    dest_imp fn2 hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_pertype.
    unfold per_pertype.
    exists R1 R2 f f0; sp;
    try (spcast; computes_to_value_refl);
    try (fold nuprl).

    generalize (inhabited_type_iff lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (f x y) (f0 x y)); intro iff; repeat (dest_imp iff hyp).
    rw iff; sp.

    generalize (is_per_type_iff_is_per lib R1 f); introv iff.
    dest_imp iff hyp.
    rw iff; sp.
Qed.

(*
Lemma tequality_mkc_ipertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_ipertype R1) (mkc_ipertype R2)
    <=> (forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y))
        # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    generalize (eqtyps x y); intro i.
    apply tequality_if_nuprl in i; sp.

    generalize (is_per_type_iff_is_per1 lib R0 R3 eq1 eqtyps); intro k; apply k; auto.

  - repnd.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R2)); intro fn.
    dest_imp fn hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_ipertype.
    unfold per_ipertype.
    exists R1 R2 f; sp;
    try (spcast; computes_to_value_refl);
    try (fold nuprl).

    generalize (is_per_type_iff_is_per1 lib R1 R2 f fn0); introv iff.
    rw iff; sp.
Qed.
*)

(*
Lemma tequality_mkc_spertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_spertype R1) (mkc_spertype R2)
    <=> (forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 x z)
             -> tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 y z)
             -> tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z))
        # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    generalize (eqtyps1 x y); intro i.
    apply tequality_if_nuprl in i; sp.

    generalize (eqtyps2 x y z); intro i; autodimp i hyp.
    eapply inhabited_if_inhabited_type with (T := mkc_apply2 R0 x z) (U := mkc_apply2 R3 x z); eauto.
    apply tequality_if_nuprl in i; sp.

    generalize (eqtyps3 x y z); intro i; autodimp i hyp.
    eapply inhabited_if_inhabited_type with (T := mkc_apply2 R0 y z) (U := mkc_apply2 R3 y z); eauto.
    apply tequality_if_nuprl in i; sp.

    generalize (is_per_type_iff_is_per1 lib R0 R3 eq1 eqtyps1); intro k; apply k; auto.

  - repnd.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R2)); intro fn.
    dest_imp fn hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_spertype.
    unfold per_spertype.
    exists R1 R2 f; dands; spcast; introv;
    try (spcast; computes_to_value_refl);
    try (fold (@nuprl p lib)); try (complete sp).

    introv inh.
    generalize (fn0 x z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i1 with (y := y) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro n.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R1 x y) eq (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_refl in n; auto.
    apply nuprl_ext with (eq1 := eq); auto.

    introv inh.
    generalize (fn0 y z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i2 with (x := x) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro n.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R1 x y) eq (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_refl in n; auto.
    apply nuprl_ext with (eq1 := eq); auto.

    generalize (is_per_type_iff_is_per1 lib R1 R2 f fn0); introv iff.
    rw iff; sp.
Qed.
*)

(*
Lemma mkc_ipertype_equality_in_uni :
  forall R1 R2 i,
    equality lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
    <=> (forall x y, equality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (mkc_uni i))
      # is_per_type lib R1.
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
    allunfold per_ipertype; exrepnd.
    allfold nuprl; allfold (nuprli j).
    computes_to_value_isvalue.

    dands; intros.

    generalize (X5 x y); intro k.
    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists (eq1 x y); sp.

    allunfold is_per; repnd; allunfold is_per_type; dands.

    unfold sym_type; introv inh.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R0 y x) (eq := eq1 y x); sp.
    generalize (X5 y x); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply X2.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 x y) (T := mkc_apply2 R0 x y); sp.
    generalize (X5 x y); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.

    unfold trans_type; introv inh1 inh2.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R0 x z) (eq := eq1 x z); sp.
    generalize (X5 x z); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply X6 with (y := y).
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 x y) (T := mkc_apply2 R0 x y); sp.
    generalize (X5 x y); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 y z) (T := mkc_apply2 R0 y z); sp.
    generalize (X5 y z); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : per & close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; try computes_to_value_refl.

    fold (nuprli i).

    assert (forall x y : CTerm,
              {eq : per
               & nuprli i (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) eq}) as f1.
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x0 into i.
    rw X1 in k0; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    exists (fun t t' => inhabited (projT1 (f1 t t'))).
    apply CL_ipertype.
    fold (nuprli i).
    unfold per_ipertype.
    exists R1 R2
           (fun t t' => projT1 (f1 t t'));
      sp; try (computes_to_value_refl); try (fold nuprl).

    generalize (f1 x y); intro h; exrepnd; allsimpl; sp.

    unfold is_per_type in equ; unfold sym_type, trans_type in equ; repnd.
    unfold is_per; dands; introv.

    generalize (f1 x y); generalize (f1 y x); intros h1 h2 inh; exrepnd; allsimpl.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R1 y x) (T := mkc_apply2 R1 y x); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply equ1.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 x y) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).

    generalize (f1 x y); generalize (f1 y z); generalize (f1 x z); intros h1 h2 h3 inh1 inh2; exrepnd; allsimpl.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R1 x z) (T := mkc_apply2 R1 x z); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply equ with (y := y).
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 x y) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 y z) (eq := eq0); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
(*Error: Universe inconsistency.*)
[Admitted.]
*)

Lemma type_mkc_pertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_pertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
      # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_pertype; split; sp.
  rw @fold_type; sp.
  unfold type; sp.
  unfold type; sp.
Qed.

(*
Lemma type_mkc_ipertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_ipertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
      # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_ipertype; split; sp.
Qed.
*)

(*
Lemma type_mkc_spertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_spertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R x z)
             -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R z y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R y z)
             -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R x z))
        # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_spertype; split; sp.
Qed.
*)

Lemma iff_inhabited_type_if_pertype_eq_or_ceq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (equality lib (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
     [+] cequivc lib (mkc_pertype R1) (mkc_pertype R2))
    -> forall x y,
         inhabited_type lib (mkc_apply2 R1 x y)
          <=> inhabited_type lib (mkc_apply2 R2 x y).
Proof.
  introv or.
  introv.
  split; intro inh; repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw <- or3; sp.

  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 R1 x y); sp.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw or3; sp.

  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 b x y); sp.
  apply cequivc_sym; sp.
Qed.

(*
Lemma tequality_mkc_apply2_if_pertype_eq_or_ceq :
  forall R1 R2 i,
    (equality lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
     [+] cequivc (mkc_ipertype R1) (mkc_ipertype R2))
    -> forall x y : CTerm,
         (type lib (mkc_apply2 R1 x y) [+] type lib (mkc_apply2 R2 x y))
         -> tequality lib (mkc_apply2 R1 x y)
                      (mkc_apply2 R2 x y).
Proof.
  introv eq.
  introv typ.
  destruct eq.

  apply equality_in_uni in e.
  rw tequality_mkc_ipertype in e; sp.

  generalize (cequivc_mkc_ipertype lib (mkc_ipertype R1) (mkc_ipertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  destruct typ.
  apply type_respects_cequivc_right; sp.
  apply type_respects_cequivc_left; sp.
  apply cequivc_sym; sp.
Qed.
*)


Lemma equality_in_mkc_pertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_pertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2) # type lib (mkc_pertype R)).
Proof.
  introv.
  rw @equality_in_mkc_pertype.
  rw @type_mkc_pertype; split; sp.
Qed.

(*
Lemma equality_in_mkc_ipertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_ipertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # is_per_type lib R
         # (forall x y, type lib (mkc_apply2 R x y))).
Proof.
  intros; unfold inhabited_type; split; intro i; exrepnd.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    rw pereq in i0.
    unfold pertype_eq, inhabited in i0; exrepnd.
    dands.

    exists t; unfold member, equality; exists (eq1 t1 t2); sp.

    generalize (is_per_type_iff_is_per lib R1 eq1 eqtyps); introv iff.
    apply iff; auto.

    introv; exists (eq1 x y); sp.

  - unfold member, equality, nuprl in i2; exrepnd.
    allfold (@nuprl p lib).
    generalize (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R) i); intro fn; exrepnd.
    generalize (fn0 t1 t2); intro n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (autodimp eqt hyp).

    exists (fun a b => inhabited (f a b)); sp;
    try (complete (rw eqt in i0; exists t; sp)).

    apply CL_ipertype; unfold per_ipertype.
    allfold (@nuprl p lib).
    exists R R f; sp;
    try (spcast; complete computes_to_value_refl).

    generalize (is_per_type_iff_is_per lib R f fn0); introv iff.
    rw iff; sp.
Qed.
*)

(*
Lemma equality_in_mkc_ipertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_ipertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2) # type lib (mkc_ipertype R)).
Proof.
  introv.
  rw @equality_in_mkc_ipertype.
  rw @type_mkc_ipertype; split; sp.
Qed.
*)

(*
Lemma equality_in_mkc_spertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_spertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # (forall x y, type lib (mkc_apply2 R x y))
         # (forall x y z,
              inhabited_type lib (mkc_apply2 R x z)
              -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R z y))
         # (forall x y z,
              inhabited_type lib (mkc_apply2 R y z)
              -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R x z))
         # is_per_type lib R).
Proof.
  intros.
  rw <- @type_mkc_spertype.
  split; intro i; exrepnd.

  - applydup @inhabited_implies_tequality in i as ty; dands; auto.
    unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    rw pereq in i0.
    unfold pertype_eq, inhabited in i0; exrepnd.

    exists t; unfold member, equality; exists (eq1 t1 t2); sp.

  - rw @type_mkc_spertype in i; repnd.
    unfold inhabited_type in i0; exrepnd.
    unfold member, equality, nuprl in i4; exrepnd.
    allfold (@nuprl p lib).
    generalize (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R) i1); intro fn; exrepnd.
    generalize (fn0 t1 t2); intro n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (autodimp eqt hyp).

    exists (fun a b => inhabited (f a b)); sp;
    try (complete (rw eqt in i0; exists t; sp)).

    apply CL_spertype; unfold per_spertype.
    allfold (@nuprl p lib).
    exists R R f; dands; introv;
    try (spcast; complete computes_to_value_refl);
    try (complete sp).

    introv inh.
    generalize (fn0 x z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i2 with (y := y) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro nu.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R x y) eq0 (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_ext with (eq1 := eq0); auto.

    introv inh.
    generalize (fn0 y z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i3 with (x := x) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro nu.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R x y) eq0 (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_ext with (eq1 := eq0); auto.

    generalize (is_per_type_iff_is_per lib R f fn0); introv iff.
    rw iff; sp.
Qed.
*)

(*
Lemma equality_in_mkc_spertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_spertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # type lib (mkc_spertype R)).
Proof.
  intros.
  rw @equality_in_mkc_spertype.
  rw @type_mkc_spertype; sp.
Qed.
*)

Lemma iff_inhabited_type_if_pertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    equorsq lib (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
    -> forall x y,
         inhabited_type lib (mkc_apply2 R1 x y)
          <=> inhabited_type lib (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv or.
  introv.
  split; intro inh; repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw <- or3; sp.

  spcast.
  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 R1 x y); sp.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw or3; sp.

  spcast.
  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 b x y); sp.
  apply cequivc_sym; sp.
Qed.

(*
Lemma iff_inhabited_type_if_ipertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (forall x y : CTerm, type lib (mkc_apply2 R1 x y))
    -> equorsq lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
    -> forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv istype or; introv.
  repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_ipertype in or0; repnd; sp.

  spcast.
  generalize (cequivc_mkc_ipertype lib (mkc_ipertype R1) (mkc_ipertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  generalize (istype x y); intro t.
  apply cequivc_sym in ceq; rwg ceq; sp.
Qed.
*)

(*
Lemma iff_inhabited_type_if_spertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (forall x y : CTerm, type lib (mkc_apply2 R1 x y))
    -> equorsq lib (mkc_spertype R1) (mkc_spertype R2) (mkc_uni i)
    -> forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv istype or; introv.
  repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_spertype in or0; repnd; sp.

  spcast.
  generalize (cequivc_mkc_spertype lib (mkc_spertype R1) (mkc_spertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  generalize (istype x y); intro t.
  apply cequivc_sym in ceq; rwg ceq; sp.
Qed.
*)

Lemma is_per_type_sqper_rel_change_subst {o} :
  forall lib v1 v2 R s1 s2 w c1 c2,
    (forall x y : @CTerm o,
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s1 c1) x y)
       <=>
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s2 c2) x y))
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s1 c1)
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s2 c2).
Proof.
  introv iff isper.
  allunfold @is_per_type.
  destruct isper as [sym trans].
  allunfold @sqper_rel; lsubst_tac.
  dands.

  - clear trans.
    allunfold @sym_type; introv inh.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (sym x y); clear sym; intro sym.
    autodimp sym hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y x); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

  - clear sym.
    allunfold @trans_type; introv inh1 inh2.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (trans x y z); clear trans; intro trans.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
Qed.

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

(*
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
*)

(*
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
*)

(*
Lemma tequality_equality_in_mkc_spertype_implies_tequality_apply {p} :
  forall lib (a b c d R1 R2 : @CTerm p),
    tequality lib
      (mkc_equality a b (mkc_spertype R1))
      (mkc_equality c d (mkc_spertype R2))
    -> tequality lib
         (mkc_apply2 R1 a b)
         (mkc_apply2 R2 c d).
Proof.
  introv teq.
  rw @tequality_mkc_equality_sp in teq; repnd.
  rw @tequality_mkc_spertype in teq0; repnd.
  destruct teq1 as [e1 | ceq1]; destruct teq as [e2 | ceq2];
  try (rw @equality_in_mkc_spertype2 in e1);
  try (rw @equality_in_mkc_spertype2 in e2); repnd; spcast.

  - generalize (teq3 a b c e3); intro h1.
    apply tequality_trans with (t2 := mkc_apply2 R1 c b); auto.
    generalize (teq4 c b d e0); intro h2.
    apply tequality_trans with (t2 := mkc_apply2 R1 c d); auto.

  - generalize (teq3 a b c e0); intro h1.
    apply tequality_trans with (t2 := mkc_apply2 R1 c b); auto.
    apply tequality_respects_cequivc_left with (T1 := mkc_apply2 R1 c d); auto.
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.

  - apply tequality_respects_cequivc_left with (T1 := mkc_apply2 R1 c b); auto.
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
    generalize (teq4 c b d e0); intro h1.
    apply tequality_trans with (t2 := mkc_apply2 R1 c d); auto.

  - apply tequality_respects_cequivc_left with (T1 := mkc_apply2 R1 c d); auto.
    apply implies_cequivc_apply2; auto.
    apply cequivc_sym; auto.
    apply cequivc_sym; auto.
Qed.
*)