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

Lemma type_system_implies_etype_system {o} :
  forall lib (ts : cts(o)),
    type_system lib ts -> etype_system lib (fun A A' eq => ts A eq # ts A' eq).
Proof.
  introv tys.
  dest_ts tys.

  prove_etype_system Case; tcsp.

  - Case "uniquely_valued".
    introv n e.
    destruct n as [n1 n2].
    destruct e as [e1 e2].
    eapply ts_uv; eauto.

  - Case "type_extensionality".
    introv n e.
    destruct n as [n1 n2].
    split; eapply ts_ext; eauto.

  - Case "type_symmetric".
    introv n.
    destruct n as [n1 n2].
    split; tcsp.

  - Case "type_transitive".
    introv n m.
    destruct n as [n1 n2].
    destruct m as [m1 m2].
    split; tcsp.

  - Case "type_value_respecting".
    introv n c.
    destruct n as [n1 n2].
    split; auto.
    eapply ts_tyv; eauto.

  - Case "term_symmetric".
    introv n.
    destruct n as [n1 n2].
    eapply ts_tes; eauto.

  - Case "term_transitive".
    introv n.
    destruct n as [n1 n2].
    eapply ts_tet; eauto.

  - Case "term_value_respecting".
    introv n.
    destruct n as [n1 n2].
    eapply ts_tev; eauto.
Qed.

Lemma nuprl_type_system_implies_Nuprl_etype_system {o} :
  forall (lib : @library o),
    type_system lib (nuprl lib) -> etype_system lib (Nuprl lib).
Proof.
  introv ts.
  apply type_system_implies_etype_system; auto.
Qed.

Lemma nuprli_type_system_implies_Nuprli_etype_system {o} :
  forall (lib : @library o) i,
    type_system lib (nuprli lib i) -> etype_system lib (Nuprli lib i).
Proof.
  introv ts.
  apply type_system_implies_etype_system; auto.
Qed.

Lemma defines_only_universes_univi {o} :
  forall lib i, @defines_only_universes o lib (univi lib i).
Proof.
  unfold defines_only_universes; sp.
  allrw @univi_exists_iff; sp.
  exists j; sp.
Qed.
Hint Resolve defines_only_universes_univi : slow.

Lemma defines_only_universes_univ {o} :
  forall lib, @defines_only_universes o lib (univ lib).
Proof.
  unfold defines_only_universes, univ; sp.
  induction i; allsimpl; sp.
  exists i; sp.
Qed.
Hint Resolve defines_only_universes_univ : slow.


(* end hide *)

(**

  We prove that all the Nuprl universes satisfy the type system
  properties.

 *)

Hint Resolve eq_term_equals_trans : slow.
Hint Resolve eq_term_equals_sym : slow.

Lemma univi_type_system {o} :
  forall lib (i : nat), @type_system o lib (univi lib i).
Proof.
  induction i as [? IH] using comp_ind_type.
  prove_type_system Case; tcsp.

  - Case "uniquely_valued".
    introv u1 u2.
    allrw @univi_exists_iff; sp.
    spcast; computes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym; auto.

  - Case "type_extensionality".
    introv n e.
    allrw @univi_exists_iff; exrepnd.
    exists j; sp.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "type_value_respecting".
    introv n c.
    allrw @univi_exists_iff; sp.
    exists j; sp.
    spcast.
    eapply cequivc_uni; eauto.

  - Case "term_symmetric".
    introv n e.
    allrw @univi_exists_iff; exrepnd.
    apply n0 in e.
    apply n0.
    unfold univi_eq in *; exrepnd.
    exists eqa; tcsp.

  - Case "term_transitive".
    introv u e1 e2.
    allrw @univi_exists_iff; exrepnd.
    apply u0 in e1.
    apply u0 in e2.
    apply u0; clear u0.
    unfold univi_eq in *; exrepnd.
    exists eqa; dands; auto.
    pose proof (close_type_system lib (univi lib j)) as k.
    repeat (autodimp k hyp); eauto 2 with slow.
    dts_props k uv tv te tes tet tev.

    eapply uv in e3; autodimp e3 hyp;[exact e2|].
    eapply tv; eauto.

  - Case "term_value_respecting".
    introv u e c; spcast.
    allrw @univi_exists_iff; exrepnd; spcast.
    apply u0 in e.
    apply u0; clear u0.
    unfold univi_eq in *; exrepnd.
    exists eqa; dands; auto.
    pose proof (close_type_system lib (univi lib j)) as k.
    repeat (autodimp k hyp); eauto 2 with slow.
    dts_props k uv tv te tes tet tev.
    eapply te; eauto.
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
  forall lib i1 i2 (T : @CTerm o) eq eq',
    nuprli lib i1 T eq
    -> nuprli lib i2 T eq'
    -> eq <=2=> eq'.
Proof.
  sp.
  assert (nuprli lib (i2 + i1) T eq) as c1 by (apply typable_in_higher_univ; auto).
  assert (nuprli lib (i1 + i2) T eq') as c2 by (apply typable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@nuprli_type_system o lib (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  eapply u; eauto.
Qed.

(*
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
*)

Lemma univi_uniquely_valued {o} :
  forall lib i1 i2 (T : @CTerm o) eq eq',
    univi lib i1 T eq
    -> univi lib i2 T eq'
    -> eq <=2=> eq'.
Proof.
  sp.
  assert (univi lib (i2 + i1) T eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi lib (i1 + i2) T eq') as c2 by (apply uni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@univi_type_system o lib (i2 + i1)); intro uts.
  destruct uts; sp.
  unfold uniquely_valued in u.
  eapply u; eauto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

*)

Lemma univ_type_system {o} : forall lib, @type_system o lib (univ lib).
Proof.
  unfold univ; introv.

  prove_type_system Case.

  - Case "uniquely_valued".
    introv h q; exrepnd.
    eapply univi_uniquely_valued; eauto.

  - Case "type_extensionality".
    introv h q; exrepnd.
    exists i.
    pose proof (univi_type_system lib i) as uts.
    dest_ts uts.
    eapply ts_ext; eauto.

  - Case "type_value_respecting".
    introv h q; exrepnd.
    exists i.
    pose proof (univi_type_system lib i) as uts.
    dest_ts uts.
    eapply ts_tyv; eauto.

  - Case "term_symmetric".
    introv u e; exrepnd.
    pose proof (univi_type_system lib i) as uts.
    dest_ts uts; sp.
    eapply ts_tes; eauto.

  - Case "term_transitive".
    introv u e1 e2; exrepnd.
    pose proof (univi_type_system lib i) as uts.
    dest_ts uts; sp.
    eapply ts_tet; eauto.

  - Case "term_value_respecting".
    introv u e c; exrepnd.
    pose proof (univi_type_system lib i) as uts.
    dest_ts uts; sp.
    eapply ts_tev; eauto.
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

Lemma Nuprl_etype_system {o} :
  forall (lib : @library o), etype_system lib (Nuprl lib).
Proof.
  introv.
  apply nuprl_type_system_implies_Nuprl_etype_system.
  apply nuprl_type_system.
Qed.

Lemma Nuprli_etype_system {o} :
  forall lib (i : nat), @etype_system o lib (Nuprli lib i).
Proof.
  introv.
  apply nuprli_type_system_implies_Nuprli_etype_system.
  apply nuprli_type_system.
Qed.

(* begin hide *)

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac nts :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@nuprl_type_system p lib) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Ltac ents :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@Nuprl_etype_system p lib) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma Nuprl_refl {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    Nuprl lib t1 t2 eq -> Nuprl lib t1 t1 eq.
Proof.
  intros.
  ents.
  eapply nts_tyt; eauto.
Qed.

Lemma Nuprl_sym {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    Nuprl lib t1 t2 eq -> Nuprl lib t2 t1 eq.
Proof.
  intros; ents; sp.
Qed.

Lemma Nuprl_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq1 eq2,
    Nuprl lib t1 t2 eq1 -> Nuprl lib t2 t3 eq2 -> Nuprl lib t1 t3 eq1.
Proof.
  introv n1 n2; ents.
  eapply nts_tyt; eauto.
  eapply nts_ext;[eauto|].
  apply Nuprl_sym in n1.
  apply Nuprl_refl in n1.
  apply Nuprl_refl in n2.
  eapply nts_uv; eauto.
Qed.

Lemma nuprl_uniquely_valued {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    nuprl lib t eq1
    -> nuprl lib t eq2
    -> eq1 <=2=> eq2.
Proof.
  introv n1 n2; nts.
  eapply nts_uv; eauto.
Qed.

Lemma nuprl_value_respecting {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 eq
    -> cequivc lib t1 t2
    -> nuprl lib t2 eq.
Proof.
  intros.
  nts.
  eapply nts_tyv; eauto.
Qed.
Hint Resolve nuprl_value_respecting : slow.

Lemma Nuprl_value_respecting_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    Nuprl lib t1 t2 eq
    -> cequivc lib t1 t3
    -> Nuprl lib t3 t2 eq.
Proof.
  introv n c.
  destruct n as [n1 n2]; split; eauto 2 with slow.
Qed.
Hint Resolve Nuprl_value_respecting_left : slow.

Lemma Nuprl_value_respecting_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    Nuprl lib t1 t2 eq
    -> cequivc lib t2 t3
    -> Nuprl lib t1 t3 eq.
Proof.
  introv n c.
  destruct n as [n1 n2]; split; eauto 2 with slow.
Qed.
Hint Resolve Nuprl_value_respecting_right : slow.

Lemma nuprl_eq_implies_eqorceq_refl {o} :
  forall lib (T : @CTerm o) eq t1 t2,
    nuprl lib T eq
    -> eq t1 t2
    -> eqorceq lib eq t1 t1 # eqorceq lib eq t2 t2.
Proof.
  introv n e.
  nts; sp; left;
    eapply nts_tet; eauto;
      eapply nts_tes; eauto.
Qed.

(* end hide *)
