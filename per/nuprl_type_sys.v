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

Definition computes_to_refl {o} lib (x y : @CTerm o) :=
  { t , u : CTerm , x ===>(lib) (mkc_refl t) # y ===>(lib) (mkc_refl u) }.

(*
Notation "a =2=> b" := (forall x y, a x y -> b x y) (at level 0).

Definition refl_inhabit_equality_types {o} lib (ts : cts(o)) :=
  forall T eq a b A,
    ts T eq
    -> T ===>(lib) (mkc_equality a b A)
    -> eq =2=> (computes_to_refl lib).

Lemma close_satisfies_refl_inhabit_equality_types {o} :
  forall lib (ts : cts(o)),
    defines_only_universes lib ts
    -> refl_inhabit_equality_types lib (close lib ts).
Proof.
  introv dou cl.
  revert a b A.

  close_cases (destruct cl using @close_ind') Case; introv compeq exy;
    try (complete (allunfold_per; ccomputes_to_eqval)).

  - Case "CL_init".
    use_dou; ccomputes_to_eqval.

  - Case "CL_eq".
    clear per IHcl.
    ccomputes_to_eqval.
    apply eqiff in exy; unfold per_eq_eq in exy; exrepnd.
    exists x1 x2; dands; auto.
Qed.
*)

(*
Lemma close_ext_equality_types {o} :
  forall lib (ts : cts(o)) (T1 T2 : @CTerm o) eq a1 a2 A,
    defines_only_universes lib ts
    -> close lib ts T1 eq
    -> close lib ts T2 eq
    -> (T1 ===>(lib) (mkc_equality a1 a2 A))
    -> { b1 , b2 , B : CTerm , T2 ===>(lib) (mkc_equality b1 b2 B) }.
Proof.
  introv dou cl.
  revert a1 a2 A T2.

  close_cases (destruct cl using @close_ind') Case; introv clt2 compt1;
    try (complete (allunfold_per; ccomputes_to_eqval)).

  - Case "CL_init".
    use_dou; ccomputes_to_eqval.

  - Case "CL_eq".
    autodimp IHcl hyp.
    ccomputes_to_eqval.
    clear per.

    close_cases (destruct clt2 using @close_ind') SCase.

    Focus 2.
    allunfold_per.
Qed.
*)

Ltac dextts H ts1 ts2 := destruct H as [ts1 ts2].
(*Ltac iextts H ts1 ts2 imp := induction H as [ts1 ts2 imp] using extts_ind'.*)

Lemma either_computes_to_equality_sym {o} :
  forall lib (T1 T2 : @CTerm o),
    either_computes_to_equality lib T1 T2
    -> either_computes_to_equality lib T2 T1.
Proof.
  introv e.
  destruct e as [e|e];[right|left]; auto.
Qed.
Hint Resolve either_computes_to_equality_sym : slow.

Lemma implies_computes_to_equality {o} :
  forall lib (T : @CTerm o) a b A,
    T ===>(lib) (mkc_equality a b A)
    -> computes_to_equality lib T.
Proof.
  introv comp.
  exists a b A; auto.
Qed.
Hint Resolve implies_computes_to_equality : slow.

Lemma computes_to_equality_implies_either_left {o} :
  forall lib (T1 T2 : @CTerm o),
    computes_to_equality lib T1
    -> either_computes_to_equality lib T1 T2.
Proof.
  tcsp.
Qed.
Hint Resolve computes_to_equality_implies_either_left : slow.

Lemma computes_to_equality_implies_either_right {o} :
  forall lib (T1 T2 : @CTerm o),
    computes_to_equality lib T2
    -> either_computes_to_equality lib T1 T2.
Proof.
  tcsp.
Qed.
Hint Resolve computes_to_equality_implies_either_right : slow.

Lemma either_computes_to_equality_same_implies {o} :
  forall lib (T : @CTerm o),
    either_computes_to_equality lib T T
    -> exists a b A, T ===>(lib) (mkc_equality a b A).
Proof.
  introv e; destruct e as [e|e]; auto.
Qed.

Lemma extts_close_refl {o} :
  forall lib (ts : cts(o)) (T : @CTerm o) eq,
    defines_only_universes lib ts
    -> close lib ts T eq
    -> extts (close lib ts) T T eq.
Proof.
  introv dou c.
  split; auto.
Qed.

Lemma extts_extensional {o} :
  forall ts (A B C : @CTerm o) eq eq',
    uniquely_valued ts
    -> type_extensionality ts
    -> extts ts A B eq
    -> extts ts B C eq'
    -> extts ts B C eq.
Proof.
  introv u ext e1 e2.
  dextts e1 ts1 ts2.
  dextts e2 ts3 ts4.
  constructor; auto.
  eapply ext;[eauto|].
  eapply u; eauto.
Qed.

Lemma extts_trans_and {o} :
  forall ts (A B C : @CTerm o) eq eq',
    uniquely_valued ts
    -> type_extensionality ts
    -> extts ts A B eq
    -> extts ts B C eq'
    -> (extts ts A C eq # extts ts A C eq').
Proof.
  introv u ext e1 e2.
  dextts e1 ts1 ts2.
  dextts e2 ts3 ts4.
  dands; split; auto.

  - eapply ext;[eauto|].
    eapply u; eauto.

  - eapply ext;[eauto|].
    eapply u; eauto.
Qed.

Lemma extts_sym {o} :
  forall ts (T T' : @CTerm o) eq,
    extts ts T T' eq
    -> extts ts T' T eq.
Proof.
  introv n.
  destruct n; split; auto.
Qed.

Lemma extts_trans_left {o} :
  forall ts (A B C : @CTerm o) eq eq',
    uniquely_valued ts
    -> type_extensionality ts
    -> extts ts A B eq
    -> extts ts B C eq'
    -> extts ts A C eq.
Proof.
  introv u e e1 e2.
  pose proof (extts_trans_and ts A B C eq eq') as h; repeat (autodimp h hyp); tcsp.
Qed.

Lemma extts_trans_right {o} :
  forall ts (A B C : @CTerm o) eq eq',
    uniquely_valued ts
    -> type_extensionality ts
    -> extts ts A B eq
    -> extts ts B C eq'
    -> extts ts A C eq'.
Proof.
  introv u e e1 e2.
  pose proof (extts_trans_and ts A B C eq eq') as h; repeat (autodimp h hyp); tcsp.
Qed.

Lemma either_computes_to_equality_if_cequivc_left {o} :
  forall lib (T1 T2 T : @CTerm o),
    cequivc lib T1 T2
    -> either_computes_to_equality lib T1 T2
    -> either_computes_to_equality lib T1 T.
Proof.
  introv ceq e.
  destruct e as [e|e]; tcsp.
  left.
  unfold computes_to_equality in *; exrepnd; spcast.
  eapply cequivc_mkc_equality in e0;[|apply cequivc_sym;eauto]; exrepnd.
  eexists; eexists; eexists; spcast; eauto.
Qed.
Hint Resolve either_computes_to_equality_if_cequivc_left : slow.

Lemma extts_respect_cequivc_left {o} :
  forall lib (ts : cts(o)) (T1 T2 T : @CTerm o) eq,
    type_value_respecting lib ts
    -> extts ts T1 T2 eq
    -> cequivc lib T1 T
    -> extts ts T1 T eq.
Proof.
  introv resp n ceq.
  destruct n as [ts1 ts2].
  split; auto.
  eapply resp;[|eauto]; auto.
Qed.

Lemma extts_ext {o} :
  forall ts (T T' : @CTerm o) eq eq',
    type_extensionality ts
    -> extts ts T T' eq
    -> (eq <=2=> eq')
    -> extts ts T T' eq'.
Proof.
  introv ext n eqiff.
  dextts n ts1 ts2.
  constructor; auto; try (complete (eapply ext; eauto)).
Qed.

Lemma extts_uniquely_valued {o} :
  forall ts (T T' : @CTerm o) eq eq',
    uniquely_valued ts
    -> extts ts T T' eq
    -> extts ts T T' eq'
    -> (eq <=2=> eq').
Proof.
  introv uv n m.
  destruct n as [n1 n2].
  destruct m as [e1 e2].
  eapply uv; eauto.
Qed.

Lemma type_system_implies_etype_system_extts {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> etype_system lib (extts ts).
Proof.
  introv tys.
  dest_ts tys.

  prove_etype_system Case; tcsp.

  - Case "uniquely_valued".
    introv n e.
    eapply extts_uniquely_valued; eauto.

  - Case "type_extensionality".
    introv n e.
    eapply extts_ext; eauto.

  - Case "type_symmetric".
    introv n.
    eapply extts_sym; eauto.

  - Case "type_transitive".
    introv n m.
    eapply extts_trans_left; eauto.

  - Case "type_value_respecting".
    introv n c.
    eapply extts_respect_cequivc_left; eauto.

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
  apply type_system_implies_etype_system_extts; auto.
Qed.

Lemma nuprli_type_system_implies_Nuprli_etype_system {o} :
  forall (lib : @library o) i,
    type_system lib (nuprli lib i) -> etype_system lib (Nuprli lib i).
Proof.
  introv ts.
  apply type_system_implies_etype_system_extts; auto.
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

Lemma extts_nuprl_refl {o} :
  forall lib (T : @CTerm o) eq,
    nuprl lib T eq
    -> extts (nuprl lib) T T eq.
Proof.
  introv n.
  apply extts_close_refl; eauto 2 with slow.
Qed.
Hint Resolve extts_nuprl_refl : slow.


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
    clear dependent eq.

    unfold univi_eq in *; exrepnd.
    exists eqa.
    apply extts_sym; auto.

  - Case "term_transitive".
    introv u e1 e2.
    allrw @univi_exists_iff; exrepnd.
    apply u0 in e1.
    apply u0 in e2.
    apply u0.
    clear dependent eq.

    pose proof (close_type_system lib (univi lib j)) as k.
    repeat (autodimp k hyp); eauto 2 with slow.

    unfold univi_eq in *; exrepnd.
    exists eqa.

    eapply extts_trans_right; eauto;
      dts_props k uv tv te tes tet tev; tcsp.

  - Case "term_value_respecting".
    introv u e c; spcast.
    allrw @univi_exists_iff; exrepnd; spcast.
    apply u0 in e.
    apply u0.
    clear dependent eq.

    pose proof (close_type_system lib (univi lib j)) as k.
    repeat (autodimp k hyp); eauto 2 with slow.

    unfold univi_eq in *; exrepnd.
    exists eqa.

    eapply extts_respect_cequivc_left; eauto;
      dts_props k uv tv te tes tet tev; tcsp.
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

Lemma type_value_respecting_nuprl {o} :
  forall lib, @type_value_respecting o lib (nuprl lib).
Proof.
  introv; nts; auto.
Qed.
Hint Resolve type_value_respecting_nuprl : slow.

Lemma uniquely_valued_nuprl {o} :
  forall lib, @uniquely_valued o (nuprl lib).
  introv; nts; auto.
Qed.
Hint Resolve uniquely_valued_nuprl : slow.

Lemma type_extensionality_nuprl {o} :
  forall lib, @type_extensionality o (nuprl lib).
Proof.
  introv; nts; auto.
Qed.
Hint Resolve type_extensionality_nuprl : slow.

Lemma Nuprl_value_respecting_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    Nuprl lib t1 t2 eq
    -> cequivc lib t1 t3
    -> Nuprl lib t3 t2 eq.
Proof.
  introv n c.
  unfold Nuprl in *.
  eapply extts_respect_cequivc_left in c;[| |eauto]; eauto 2 with slow.
  apply extts_sym in c.
  eapply extts_trans_left in n;[| | |eauto]; eauto 2 with slow.
Qed.
Hint Resolve Nuprl_value_respecting_left : slow.

Lemma Nuprl_value_respecting_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    Nuprl lib t1 t2 eq
    -> cequivc lib t2 t3
    -> Nuprl lib t1 t3 eq.
Proof.
  introv n c.
  unfold Nuprl in *.
  eapply extts_respect_cequivc_left in c;
    [| |apply extts_sym;eauto]; eauto 2 with slow.
  eapply extts_trans_left in c;[| | |eauto]; eauto 2 with slow.
Qed.
Hint Resolve Nuprl_value_respecting_right : slow.

(*
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
*)

(* end hide *)
