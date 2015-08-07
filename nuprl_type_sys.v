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


Add LoadPath "close".

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


Lemma defines_only_universes_univi {o} :
  forall lib i, @defines_only_universes o lib (univi lib i).
Proof.
  unfold defines_only_universes; sp.
  allrw @univi_exists_iff; sp.
  exists j; sp.
Qed.

Lemma defines_only_universes_univ {o} :
  forall lib, @defines_only_universes o lib (univ lib).
Proof.
  unfold defines_only_universes, univ; sp.
  induction i; allsimpl; sp.
  exists i; sp.
Qed.


(* end hide *)

(**

  We prove that all the Nuprl universes satisfy the type system
  properties.

*)

Lemma univi_type_system {o} :
  forall lib (i : nat), @type_system o lib (univi lib i).
Proof.
  induction i using comp_ind_type.
  unfold type_system; sp.

  - unfold uniquely_valued, eq_term_equals; sp.
    allrw @univi_exists_iff; sp.
    spcast; computes_to_eqval.
    allrw; sp.

  - introv q h.
    allrw @univi_exists_iff; exrepnd.
    exists j; sp.
    rw <- h; auto.

  - unfold type_symmetric; sp.
    allrw @univi_exists_iff; sp.
    exists j; sp.

  - unfold type_transitive; sp.
    allrw @univi_exists_iff; sp.
    spcast; computes_to_eqval.
    eexists; sp; spcast; sp.

  - unfold type_value_respecting; sp.
    allrw @univi_exists_iff; sp.
    exists j; sp; thin_trivials.
    spcast; apply cequivc_uni with (t := T); auto.

  - unfold term_symmetric, term_equality_symmetric; sp.
    allrw @univi_exists_iff; sp; spcast.
    discover; sp.
    allrw.
    exists eqa; auto.
    generalize (@close_type_system o lib (univi lib j)); intro k.
    repeat (dest_imp k hyp).
    apply defines_only_universes_univi.
    inversion k; sp.

  - unfold term_transitive, term_equality_transitive; sp.
    allrw @univi_exists_iff; sp.
    discover; sp; spcast.
    allrw.
    generalize (@close_type_system o lib (univi lib j)); intro k.
    repeat (dest_imp k hyp).
    apply defines_only_universes_univi.
    inversion k; sp.
    exists eqa0.
    apply uniquely_valued_trans4 with (T2 := t2) (eq1 := eqa); sp.

  - unfold term_value_respecting, term_equality_respecting; sp.
    allrw @univi_exists_iff; sp.
    discover; sp; spcast; GC.
    allrw.
    exists eqa.
    generalize (@close_type_system o lib (univi lib j)); intro k.
    repeat (dest_imp k hyp).
    apply defines_only_universes_univi.
    inversion k; sp.
Qed.

(* begin hide *)

Lemma nuprli_type_system {o} :
  forall lib (i : nat), @type_system o lib (nuprli lib i).
Proof.
  unfold nuprli; sp.
  apply close_type_system.
  apply univi_type_system.
  apply defines_only_universes_univi.
Qed.

Lemma nuprli_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    nuprli lib i1 T T' eq
    -> nuprli lib i2 T T' eq'
    -> eq_term_equals eq eq'.
Proof.
  sp.
  assert (nuprli lib (i2 + i1) T T' eq) as c1 by (apply typable_in_higher_univ; auto).
  assert (nuprli lib (i1 + i2) T T' eq') as c2 by (apply typable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@nuprli_type_system o lib (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  apply u with (T := T) (T' := T'); auto.
Qed.

Lemma nuprli_type_transitive {o} :
  forall lib i1 i2 (T1 T2 T3 : @CTerm o) eq,
    nuprli lib i1 T1 T2 eq
    -> nuprli lib i2 T2 T3 eq
    -> {i : nat & nuprli lib i T1 T3 eq # i1 <= i # i2 <= i}.
Proof.
  sp.
  assert (nuprli lib (i1 + i2) T1 T2 eq) as c1 by (apply typable_in_higher_univ_r; auto).
  assert (nuprli lib (i1 + i2) T2 T3 eq) as c2 by (apply typable_in_higher_univ; auto).
  exists (i1 + i2); sp; try omega.
  generalize (@nuprli_type_system o lib (i1 + i2)); intro nts.
  destruct nts; sp.
  apply p2 with (T2 := T2); sp.
Qed.

Lemma univi_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    univi lib i1 T T' eq
    -> univi lib i2 T T' eq'
    -> eq_term_equals eq eq'.
Proof.
  sp.
  assert (univi lib (i2 + i1) T T' eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi lib (i1 + i2) T T' eq') as c2 by (apply uni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@univi_type_system o lib (i2 + i1)); intro uts.
  destruct uts; sp.
  unfold uniquely_valued in u.
  apply u with (T := T) (T' := T'); auto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

*)

Lemma univ_type_system {o} : forall lib, @type_system o lib (univ lib).
Proof.
  unfold univ, type_system; sp.

  - unfold uniquely_valued; sp.
    apply (univi_uniquely_valued lib) with (i1 := i0) (i2 := i) (T := T) (T' := T'); auto.

  - unfold type_extensionality; sp.
    exists i.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts.
    unfold type_extensionality in ts_ext.
    apply ts_ext with (eq := eq); auto.

  - unfold type_symmetric; sp.
    exists i.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts; auto.

  - unfold type_transitive; introv u1 u2; exrepnd.
    apply uni_in_higher_univ with (k := i0) in u0.
    apply uni_in_higher_univ_r with (k := i) in u2.
    exists (i0 + i).
    generalize (@univi_type_system o lib (i0 + i)); intro uts.
    dest_ts uts; auto.
    apply ts_tyt with (T2 := T2); auto.

  - unfold type_value_respecting; sp.
    exists i.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts; sp.

  - unfold term_symmetric, term_equality_symmetric; introv u e1; exrepnd.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tes in u0.
    apply u0; auto.

  - unfold term_transitive, term_equality_transitive; introv u e1 e2; exrepnd.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tet in u0.
    apply u0 with (t2 := t2); auto.

  - unfold term_value_respecting, term_equality_respecting; introv u e1 c1; exrepnd.
    generalize (@univi_type_system o lib i); intro uts.
    dest_ts uts; sp.
    apply ts_tev in u0.
    apply u0; auto.
Qed.

(**

  Finally, we prove that that [nuprl] satisfies the type system properties.

*)

Lemma nuprl_type_system {p} : forall lib, @type_system p lib (nuprl lib).
Proof.
  introv.
  apply close_type_system.
  apply univ_type_system.
  apply defines_only_universes_univ.
Qed.

(* begin hide *)

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac nts :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@nuprl_type_system p lib) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprl_refl {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t1 t1 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t2 t1 eq); sp.
  use_trans t2; sp.
Qed.

Lemma nuprl_sym {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t2 t1 eq.
Proof.
  intros; nts; sp.
Qed.

Lemma nuprl_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq1 eq2,
    nuprl lib t1 t2 eq1 -> nuprl lib t2 t3 eq2 -> nuprl lib t1 t3 eq1.
Proof.
  introv n1 n2; nts.
  use_trans t2; sp.
  use_ext eq2; sp.
  apply uniquely_valued_eq with (ts := nuprl lib) (T := t2) (T1 := t3) (T2 := t1); sp.
Qed.

Lemma nuprl_uniquely_valued {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    nuprl lib t t eq1
    -> nuprl lib t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  introv n1 n2; nts.
  apply nts_uv with (T := t) (T' := t); sp.
Qed.

Lemma nuprl_value_respecting_left {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq,
    nuprl lib t1 t2 eq
    -> cequivc lib t1 t3
    -> nuprl lib t3 t2 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t2); auto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprl_value_respecting_right {p} :
  forall lib t1 t2 t3 eq,
    @nuprl p lib t1 t2 eq
    -> cequivc lib t2 t3
    -> nuprl lib t1 t3 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Lemma nuprl_eq_implies_eqorceq_refl {p} :
  forall lib T1 T2 eq t1 t2,
    @nuprl p lib T1 T2 eq
    -> eq t1 t2
    -> eqorceq lib eq t1 t1 # eqorceq lib eq t2 t2.
Proof.
  introv n e.
  nts; sp; left.
  unfold term_transitive, term_equality_transitive in nts_tet.
  apply nts_tet with (t2 := t2) (T := T1) (T' := T2); sp.
  unfold term_symmetric, term_equality_symmetric in nts_tes.
  apply nts_tes with (T := T1) (T' := T2); sp.
  unfold term_transitive, term_equality_transitive in nts_tet.
  apply nts_tet with (t2 := t1) (T := T1) (T' := T2); sp.
  unfold term_symmetric, term_equality_symmetric in nts_tes.
  apply nts_tes with (T := T1) (T' := T2); sp.
Qed.

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
