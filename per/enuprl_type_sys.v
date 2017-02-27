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


Require Export enuprl.
Require Export close_type_sys.
Require Export Peano.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ *)
(** printing ~=~  $\sim$ *)
(** printing ===>  $\Downarrow$ *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(* begin hide *)


Lemma defines_only_universes_eunivi {o} :
  forall lib i, @defines_only_universes o lib (eunivi lib i).
Proof.
  unfold defines_only_universes; sp.
  allrw @eunivi_exists_iff; sp.
  exists j; sp.
Qed.
Hint Resolve defines_only_universes_eunivi : slow.

Lemma defines_only_universes_euniv {o} :
  forall lib, @defines_only_universes o lib (euniv lib).
Proof.
  unfold defines_only_universes, euniv; sp.
  induction i; allsimpl; sp.
  exists i; sp.
Qed.
Hint Resolve defines_only_universes_euniv : slow.

Lemma type_system_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_system lib (eclose lib ts).
Proof.
  introv tsym dou.
  pose proof (close_type_system lib ts) as q; repeat (autodimp q hyp).
  unfold type_system in *; repnd; dands; auto.

  - introv e1 e2.
    inversion e1 as [a1 a2]; clear e1.
    inversion e2 as [b1 b2]; clear e2.
    eapply q0; eauto.

  - introv e eqiff.
    inversion e as [e1 e2]; clear e.
    split; eapply q1; eauto.

  - introv e.
    inversion e as [e1 e2]; clear e.
    split; eapply q2; eauto.

  - introv e1 e2.
    inversion e1 as [a1 a2]; clear e1.
    inversion e2 as [b1 b2]; clear e2.
    split; eapply q3; eauto.

  - introv e ceq.
    inversion e as [e1 e2]; clear e.
    split;[eapply q4; eauto|].
    apply (q3 _ T);[apply q2|]; apply q4; auto.

  - introv e.
    inversion e as [e1 e2]; clear e.
    eapply q5; eauto.

  - introv e.
    inversion e as [e1 e2]; clear e.
    eapply q6; eauto.

  - introv e.
    inversion e as [e1 e2]; clear e.
    eapply q; eauto.
Qed.

Lemma type_symmetric_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_symmetric (eclose lib ts).
Proof.
  introv tsym dou.
  apply type_system_eclose in tsym; auto.
  unfold type_system in tsym; tcsp.
Qed.

Lemma type_transitive_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_transitive (eclose lib ts).
Proof.
  introv tsym dou.
  apply type_system_eclose in tsym; auto.
  unfold type_system in tsym; tcsp.
Qed.

Lemma type_value_respecting_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_value_respecting lib (eclose lib ts).
Proof.
  introv tsym dou.
  apply type_system_eclose in tsym; auto.
  unfold type_system in tsym; tcsp.
Qed.

Lemma uniquely_valued_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> uniquely_valued (eclose lib ts).
Proof.
  introv tsym dou.
  apply type_system_eclose in tsym; auto.
  unfold type_system in tsym; tcsp.
Qed.

Lemma type_extensionality_eclose {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_extensionality (eclose lib ts).
Proof.
  introv tsym dou.
  apply type_system_eclose in tsym; auto.
  unfold type_system in tsym; tcsp.
Qed.

Lemma eclose_refl_l {o} :
  forall lib ts (A B : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> eclose lib ts A B eq
    -> eclose lib ts A A eq.
Proof.
  introv tsys dou e.
  eapply type_transitive_eclose; try (exact e); auto.
  apply type_symmetric_eclose; auto.
Qed.

Lemma eclose_refl_r {o} :
  forall lib ts (A B : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> eclose lib ts A B eq
    -> eclose lib ts B B eq.
Proof.
  introv tsys dou e.
  eapply type_transitive_eclose; try (exact e); auto.
  apply type_symmetric_eclose; auto.
Qed.

(* end hide *)

(**

  We prove that all the Nuprl universes satisfy the type system
  properties.

*)

Lemma eunivi_type_system {o} :
  forall lib (i : nat), @type_system o lib (eunivi lib i).
Proof.
  induction i using comp_ind_type.
  unfold type_system; sp.

  - unfold uniquely_valued, eq_term_equals; sp.
    allrw @eunivi_exists_iff; sp.
    spcast; computes_to_eqval.
    allrw; sp.

  - introv q h.
    allrw @eunivi_exists_iff; exrepnd.
    exists j; sp.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - unfold type_symmetric; sp.
    allrw @eunivi_exists_iff; sp.
    exists j; sp.

  - unfold type_transitive; sp.
    allrw @eunivi_exists_iff; sp.
    spcast; computes_to_eqval.
    eexists; dands; eauto; spcast; tcsp.

  - unfold type_value_respecting; sp.
    allrw @eunivi_exists_iff; sp.
    exists j; sp; thin_trivials.
    spcast; apply cequivc_uni with (t := T); auto.

  - unfold term_symmetric, term_equality_symmetric; sp.
    allrw @eunivi_exists_iff; sp; spcast.
    discover; sp.
    match goal with
    | [ K : ?x _ _ , H : ?x <=2=> _ |- _ ] => apply H in K; apply H; clear H
    end.
    unfold eunivi_eq in *; exrepnd.
    exists eqa; dands; auto.
    apply type_symmetric_eclose; auto; eauto 2 with slow.

  - unfold term_transitive, term_equality_transitive; introv u e1 e2.
    allrw @eunivi_exists_iff; exrepnd.
    apply u0 in e1; apply u0 in e2; apply u0.
    unfold eunivi_eq in *; exrepnd.
    pose proof (@close_type_system o lib (eunivi lib j)) as k.
    repeat (dest_imp k hyp); eauto 2 with slow;[].
    unfold type_system in k; repnd.
    exists eqa; dands; auto.

    eapply type_transitive_eclose;try (exact e0); eauto 2 with slow.
    eapply type_extensionality_eclose; try (exact e2); eauto 2 with slow.
    apply eclose_refl_r in e2; eauto 2 with slow.
    apply eclose_refl_l in e0; eauto 2 with slow.
    eapply uniquely_valued_eclose; try (exact e0); eauto 2 with slow.

  - unfold term_value_respecting, term_equality_respecting; introv u e c; spcast.
    allrw @eunivi_exists_iff; exrepnd; GC; spcast.
    apply u0 in e; apply u0; clear u0.
    unfold eunivi_eq in *; exrepnd.
    exists eqa; dands; tcsp.
    apply type_value_respecting_eclose; eauto 2 with slow.
Qed.
Hint Resolve eunivi_type_system : slow.

(* begin hide *)

Lemma enuprli_type_system {o} :
  forall lib (i : nat), @type_system o lib (enuprli lib i).
Proof.
  unfold enuprli; sp.
  apply type_system_eclose; eauto 3 with slow.
Qed.

Lemma enuprli_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    enuprli lib i1 T T' eq
    -> enuprli lib i2 T T' eq'
    -> eq_term_equals eq eq'.
Proof.
  sp.
  assert (enuprli lib (i2 + i1) T T' eq) as c1 by (apply etypable_in_higher_univ; auto).
  assert (enuprli lib (i1 + i2) T T' eq') as c2 by (apply etypable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@enuprli_type_system o lib (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  apply u with (T := T) (T' := T'); auto.
Qed.

Lemma enuprli_type_transitive {o} :
  forall lib i1 i2 (T1 T2 T3 : @CTerm o) eq,
    enuprli lib i1 T1 T2 eq
    -> enuprli lib i2 T2 T3 eq
    -> {i : nat & enuprli lib i T1 T3 eq # i1 <= i # i2 <= i}.
Proof.
  sp.
  assert (enuprli lib (i1 + i2) T1 T2 eq) as c1 by (apply etypable_in_higher_univ_r; auto).
  assert (enuprli lib (i1 + i2) T2 T3 eq) as c2 by (apply etypable_in_higher_univ; auto).
  exists (i1 + i2); sp; try omega.
  pose proof (@enuprli_type_system o lib (i1 + i2)) as nts.
  destruct nts; sp.
  apply p2 with (T2 := T2); sp.
Qed.

Lemma eunivi_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    eunivi lib i1 T T' eq
    -> eunivi lib i2 T T' eq'
    -> eq_term_equals eq eq'.
Proof.
  sp.
  assert (eunivi lib (i2 + i1) T T' eq) as c1 by (apply euni_in_higher_univ; auto).
  assert (eunivi lib (i1 + i2) T T' eq') as c2 by (apply euni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  pose proof (@eunivi_type_system o lib (i2 + i1)) as uts.
  destruct uts; sp.
  unfold uniquely_valued in u.
  apply u with (T := T) (T' := T'); auto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

*)

Lemma euniv_type_system {o} : forall lib, @type_system o lib (euniv lib).
Proof.
  unfold euniv, type_system; sp.

  - unfold uniquely_valued; sp.
    apply (eunivi_uniquely_valued lib) with (i1 := i0) (i2 := i) (T := T) (T' := T'); auto.

  - unfold type_extensionality; sp.
    exists i.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts.
    unfold type_extensionality in ts_ext.
    apply ts_ext with (eq := eq); auto.

  - unfold type_symmetric; sp.
    exists i.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts; auto.

  - unfold type_transitive; introv u1 u2; exrepnd.
    apply euni_in_higher_univ with (k := i0) in u0.
    apply euni_in_higher_univ_r with (k := i) in u2.
    exists (i0 + i).
    generalize (@eunivi_type_system o lib (i0 + i)); intro uts.
    dest_ts uts; auto.
    apply ts_tyt with (T2 := T2); auto.

  - unfold type_value_respecting; sp.
    exists i.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts; sp.

  - unfold term_symmetric, term_equality_symmetric; introv u e1; exrepnd.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tes in u0.
    apply u0; auto.

  - unfold term_transitive, term_equality_transitive; introv u e1 e2; exrepnd.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tet in u0.
    apply u0 with (t2 := t2); auto.

  - unfold term_value_respecting, term_equality_respecting; introv u e1 c1; exrepnd.
    generalize (@eunivi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tev in u0.
    apply u0; auto.
Qed.
Hint Resolve euniv_type_system : slow.

(**

  Finally, we prove that that [nuprl] satisfies the type system properties.

*)

Lemma enuprl_type_system {p} : forall lib, @type_system p lib (enuprl lib).
Proof.
  introv.
  apply type_system_eclose; eauto 2 with slow.
Qed.

(* begin hide *)

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac ents :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@enuprl_type_system p lib) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma enuprl_refl {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    enuprl lib t1 t2 eq -> enuprl lib t1 t1 eq.
Proof.
  intros.
  ents.
  assert (enuprl lib t2 t1 eq); sp.
  use_trans t2; sp.
Qed.

Lemma enuprl_sym {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    enuprl lib t1 t2 eq -> enuprl lib t2 t1 eq.
Proof.
  intros; ents; sp.
Qed.

Lemma enuprl_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq1 eq2,
    enuprl lib t1 t2 eq1 -> enuprl lib t2 t3 eq2 -> enuprl lib t1 t3 eq1.
Proof.
  introv n1 n2; ents.
  use_trans t2; sp.
  use_ext eq2; sp.
  apply uniquely_valued_eq with (ts := enuprl lib) (T := t2) (T1 := t3) (T2 := t1); sp.
Qed.

Lemma enuprl_uniquely_valued {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    enuprl lib t t eq1
    -> enuprl lib t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  introv n1 n2; ents.
  apply nts_uv with (T := t) (T' := t); sp.
Qed.

Lemma enuprl_value_respecting_left {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq,
    enuprl lib t1 t2 eq
    -> cequivc lib t1 t3
    -> enuprl lib t3 t2 eq.
Proof.
  intros.
  ents.
  assert (enuprl lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t2); auto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma enuprl_value_respecting_right {p} :
  forall lib t1 t2 t3 eq,
    @enuprl p lib t1 t2 eq
    -> cequivc lib t2 t3
    -> enuprl lib t1 t3 eq.
Proof.
  intros.
  ents.
  assert (enuprl lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Lemma enuprl_eq_implies_eqorceq_refl {p} :
  forall lib T1 T2 eq t1 t2,
    @enuprl p lib T1 T2 eq
    -> eq t1 t2
    -> eqorceq lib eq t1 t1 # eqorceq lib eq t2 t2.
Proof.
  introv n e.
  ents; sp; left.
  { unfold term_transitive, term_equality_transitive in nts_tet.
    apply nts_tet with (t2 := t2) (T := T1) (T' := T2); sp.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    apply nts_tes with (T := T1) (T' := T2); sp. }
  { unfold term_transitive, term_equality_transitive in nts_tet.
    apply nts_tet with (t2 := t1) (T := T1) (T' := T2); sp.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    apply nts_tes with (T := T1) (T' := T2); sp. }
Qed.

(* end hide *)
