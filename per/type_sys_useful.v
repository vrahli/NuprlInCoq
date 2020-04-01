(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export type_sys.
Require Export decompose_alphaeq.


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

Ltac pd t :=
  let h := fresh "h" in
  let xxx := fresh "xxx" in
  pose proof t as h; repeat (autodimp h xxx); tcsp.


Lemma eq_term_equals_sym_tsp {p} :
  forall (ts : cts(p)) uk lib eqa (eqb : per-fam(eqa))
         a1 a2
         (e : eqa a1 a1) (e1 : eqa a1 a2) (e2 : eqa a2 a1)
         v1 B1 v2 B2,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
       type_sys_props ts uk lib
                      (substc a1 v1 B1)
                      (substc a2 v2 B2)
                      (eqb a1 a2 e))
    -> eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e)
       # eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e)
       # eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2).
Proof.
  introv ftspb.
  (* 1 *)
  assert (eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e)) as eqt1.

  generalize (ftspb a1 a1 e); intro i.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  generalize (ftspb a1 a2 e1); intro i.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  implies_ts_or (substc a2 v2 B2) tygt.
  apply uv2 in tygt; sp.

  (* 2 *)
  assert (eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e)) as eqt2.

  generalize (ftspb a1 a1 e); intro i.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  generalize (ftspb a2 a1 e2); intro i.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  generalize (tygs (substc a1 v1 B1) (substc a1 v2 B2) (eqb a1 a1 e)); intro i.
  repeat (dest_imp i h); repnd.
  rw i in tygt.
  rev_implies_ts_or (substc a2 v1 B1) tygt.
  apply uv2 in tygt; sp.

  (* 3 *)
  assert (eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2)) as eqt3.
  apply eq_term_equals_trans with (eq2 := eqb a1 a1 e); sp.
  apply eq_term_equals_sym; sp.

  sp.
Qed.

Lemma eq_term_equals_sym_tsp2 {p} :
  forall (ts  : cts(p))
         (uk  : ukind)
         (lib : library)
         (eqa : per)
         (eqb : per-fam(eqa))
         v1 B1 v2 B2,
    term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e))
     # (forall a1 a2 (e2 : eqa a2 a1) (e : eqa a1 a1),
          eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e))
     # (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa a2 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2)).
Proof.
  introv teta ftspb.

  (* 1 *)
  assert (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
            eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e)) as eqt1.
  intros.
  generalize (ftspb a1 a1 e); intro i.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  generalize (ftspb a1 a2 e1); intro i.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  implies_ts_or (substc a2 v2 B2) tygt.
  apply uv2 in tygt; sp.

  (* 2 *)
  assert (forall a1 a2 (e2 : eqa a2 a1) (e : eqa a1 a1),
            eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e)) as eqt2.
  intros.
  generalize (ftspb a1 a1 e); intro i.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  generalize (ftspb a2 a1 e2); intro i.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

  generalize (tygs (substc a1 v1 B1) (substc a1 v2 B2) (eqb a1 a1 e)); intro i.
  repeat (dest_imp i h); repnd.
  rw i in tygt.
  rev_implies_ts_or (substc a2 v1 B1) tygt.
  apply uv2 in tygt; sp.

  (* 3 *)
  assert (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa a2 a1),
            eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2)) as eqt3.
  intros.
  assert (eqa a1 a1) as e by (apply teta with (t2 := a2); sp).
  apply eq_term_equals_trans with (eq2 := eqb a1 a1 e); sp.
  apply eq_term_equals_sym; sp.

  sp.
Qed.

Lemma type_sys_props_eqb_comm {p} :
  forall (ts : cts(p)) uk lib eqa (eqb : per-fam(eqa))
         a1 a2
         (e : eqa a1 a2) (e1 : eqa a2 a1) (e2 : eqa a1 a1) (e3 : eqa a2 a2)
         v1 B1 v2 B2,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
       type_sys_props ts uk lib (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e))
    -> type_sys_props ts uk lib (substc a2 v1 B1) (substc a1 v2 B2) (eqb a1 a2 e).
Proof.
  introv e1 e2 e3 ftspb.

  generalize (eq_term_equals_sym_tsp ts uk lib eqa eqb a2 a1 e3 e1 e
                                     v1 B1 v2 B2); intro i.
  dest_imp i h.
  destruct i as [eqtb2 i].
  destruct i as [eqtb1 eqtb3].

  prove_type_sys_props Case; intros; try (complete sp).

  - Case "uniquely_valued".
    repdors.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    implies_ts_or_eq (substc a2 v1 B1) T3 (substc a1 v2 B2) h.
    apply uv2 in h.
    apply eq_term_equals_trans with (eq2 := eqb a2 a1 e1); sp.
    apply eq_term_equals_sym; sp.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    rev_implies_ts_or_eq (substc a1 v2 B2) T3 (substc a2 v1 B1) h.
    apply uv2 in h.
    apply eq_term_equals_trans with (eq2 := eqb a2 a1 e1); sp.
    apply eq_term_equals_sym; sp.

  - Case "type_symmetric".
    repdors; subst.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyst2 T3 (eqb a1 a2 e)); intro i.
    dest_imp i h; repnd.
    generalize (tyt2 T3 (eqb a1 a2 e)); intro j.
    dest_imp j h; repnd.
    generalize (tys2 (substc a2 v1 B1) T3 eq'); intro k.
    repeat (dest_imp k h).
    apply eq_term_equals_trans with (eq2 := eqb a1 a2 e); sp.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyt2 T3 (eqb a1 a2 e)); intro i.
    dest_imp i h; repnd.
    generalize (tyst2 T3 (eqb a1 a2 e)); intro j.
    dest_imp j h; repnd.
    generalize (tys2 (substc a1 v2 B2) T3 eq'); intro k.
    repeat (dest_imp k h).
    apply eq_term_equals_trans with (eq2 := eqb a1 a2 e); sp.

  - Case "type_transitive".
    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyt2 T3 eq'); intro k.
    dest_imp k h; repnd; sp.

  - Case "type_stransitive".
    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyst2 T3 eq'); intro k.
    dest_imp k h; repnd; sp.

  - Case "type_value_respecting".

    repdors; subst.

    (* 1 *)
    generalize (ftspb a2 a2 e3); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyvr2 (substc a2 v1 B1) T3); intro i.
    dest_imp i h.
    dest_imp i h.

    generalize (ftspb a1 a2 e); intro j.
    onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
    generalize (tygs3 (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro k.
    repeat (dest_imp k h); repnd.
    rw k in tygt3.
    rev_implies_ts_or (substc a2 v1 B1) tygt3.
    apply uv2 in tygt3.
    generalize (tys2 (substc a2 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro l.
    dest_imp l h.

    (* 2 *)
    generalize (ftspb a1 a1 e2); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyvr2 (substc a1 v2 B2) T3); intro i.
    dest_imp i h.
    dest_imp i h.

    generalize (ftspb a1 a2 e); intro j.
    onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
    implies_ts_or (substc a1 v2 B2) tygt3.
    apply uv2 in tygt3.
    generalize (tys2 (substc a1 v1 B1) T3 (eqb a1 a2 e)); intro l.
    dest_imp l h.

  - Case "term_symmetric".
    generalize (ftspb a1 a2 e); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "term_transitive".
    generalize (ftspb a1 a2 e); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "term_value_respecting".
    generalize (ftspb a1 a2 e); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "type_gsymmetric".
    repdors; subst.
    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.
    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "type_gtransitive".

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tys2 (substc a2 v1 B1) (substc a1 v2 B2) (eqb a2 a1 e1)); sp.

(*
  - Case "type_gtransitive".
    repdors; subst.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tygt2 (substc a2 v1 B1) T3 T4 eq1 eq2); sp.

    generalize (ftspb a2 a1 e1); intro i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tygt2 (substc a1 v2 B2) T3 T4 eq1 eq2); sp.
*)

  - Case "type_mtransitive".
    repdors; subst.

    { generalize (ftspb a2 a1 e1); intro i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      pose proof (tymt2 (substc a2 v1 B1) T3 T4 eq1 eq2) as q; repeat (autodimp q hyp); tcsp. }

    { generalize (ftspb a2 a1 e1); intro i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      pose proof (tymt2 (substc a1 v2 B2) T3 T4 eq1 eq2) as q; repeat (autodimp q hyp); tcsp. }
Qed.

(*Lemma eq_term_equals_type_family {p} :
  forall lib (T1 T2 : @CTerm p) eqa1 eqa2 eqb1 eqb2 ts A v B A' v' B'
         (C : CTerm -> forall v : NVar, CVTerm [v] -> CTerm),
    (forall x y z a b c, cequivc lib (C x y z) (C a b c)-> cequivc lib x a # bcequivc lib [y] z [b] c)
    -> type_family C ts uk lib T1 T2 eqa1 eqb1
    -> ccomputes_to_valc_ext lib T1 (C A v B)
    -> type_sys_props ts uk lib A A' eqa2
    -> (forall (a a' : CTerm) (e : eqa2 a a'),
          type_sys_props ts uk lib
                         (substc a v B)
                         (substc a' v' B')
                         (eqb2 a a' e))
    -> eq_term_equals eqa2 eqa1
       # (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a1 a2 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a2 a1 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a2) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a2 e1) (eqb2 a2 a1 e2))
       # type_family C ts uk lib T1 T2 eqa2 eqb2
       # type_family C ts uk lib T2 T1 eqa2 eqb2.
Proof.
  introv c1 tf co1 tspa ftspb; introv.
  unfold type_family in tf; exrepd.
  ccomputes_to_eqval.
  apply c1 in eqt; repnd; subst.

  (* First clause *)
  assert (eq_term_equals eqa2 eqa1) as eqta.
  {
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    apply uv with (T3 := A'0); sp.
    pose proof (tyvr A A0) as q; repeat (autodimp q hyp).
    Focus 2.

  }

  (* Second clause *)
  assert (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
             eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2)) as feqtb.
  intros.
  generalize (t0 a1 a2 e1); intro ts1.
  assert (ts lib (substc a1 v0 B0) (substc a2 v' B') (eqb2 a1 a2 e2))
         as ts2
         by (generalize (ftspb a1 a2 e2); intro i;
             onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  generalize (ftspb a1 a2 e2); intro tsp.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  implies_ts_or (substc a2 v' B') ts1.
  apply uv in ts1.
  apply eq_term_equals_sym; auto.

  (* Third clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a1 a2 e2)) as feqtb1.
  intros.
  generalize (ftspb a1 a1 e1); intro tsp1.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  assert (ts lib (substc a1 v0 B0) (substc a2 v' B') (eqb2 a1 a2 e2))
         as ts1
         by (generalize (ftspb a1 a2 e2); intro i;
             onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp).
  implies_ts_or (substc a1 v' B') ts1.
  apply uv in ts1; sp.

  (* Fourth clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a2 a1 e2)) as feqtb2.
  intros.
  generalize (ftspb a1 a1 e1); intro tsp1.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (ftspb a2 a1 e2); intro tsp2.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  assert (ts lib (substc a2 v0 B0) (substc a1 v' B') (eqb2 a2 a1 e2))
         as ts1
         by (generalize (ftspb a2 a1 e2); intro i;
             onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp).
  apply tygs2 in ts1; sp.
  rev_implies_ts_or (substc a1 v0 B0) ts1.
  apply uv in ts1; sp.

  (* Fifth clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a2) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a2 e1) (eqb2 a2 a1 e2)) as feqtb3.
  intros.
  assert (eqa2 a1 a1)
         as e11
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tet with (t2 := a2); sp).
  generalize (feqtb1 a1 a2 e11 e1); intro tsp1.
  generalize (feqtb2 a1 a2 e11 e2); intro tsp2.
  apply eq_term_equals_trans with (eq2 := eqb2 a1 a1 e11); sp.
  apply eq_term_equals_sym; auto.

  (* this gets the first non type_family clauses *)
  sp.

  (* we prove the first type_family *)
  unfold type_family.
  exists A0 A'0 v0 v'0 B0 B'0; sp; spcast; sp.

  apply (type_sys_props_ts_uv2 ts lib) with (C := A') (eq1 := eqa1); sp.

  assert (eqa1 a a') as e' by (rw <- eqta; auto).
  generalize (feqtb a a' e' e); intro eqtb.
  generalize (ftspb a a' e); intro tspb.
  apply (type_sys_props_ts_uv2 ts lib) with (C := substc a' v' B') (eq1 := eqb1 a a' e'); sp.

  (* we prove the second type_family *)
  unfold type_family.
  exists A'0 A0 v'0 v0 B'0 B0; sp; spcast; sp.

  assert (ts lib A0 A'0 eqa2)
         as i by (apply (type_sys_props_ts_uv2 ts lib) with (C := A') (eq1 := eqa1); sp).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tygs A0 A'0 eqa2); intro j; dest_imp j h.
  rw <- j; sp.

  assert (eqa1 a' a)
         as e1
         by (rw <- eqta;
             onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             auto).
  assert (eqa2 a' a) as e2 by (rw eqta; auto).
  generalize (t0 a' a e1); intro tsb1.
  generalize (feqtb a' a e1 e2); intro eqtb.
  generalize (ftspb a' a e2); intro tspb.

  assert (ts lib (substc a' v0 B0) (substc a v'0 B'0) (eqb2 a a' e))
         as i
         by (apply (type_sys_props_ts_uv3 ts lib) with (C := substc a v' B') (eq1 := eqb1 a' a e1) (eq2 := eqb2 a' a e2); sp).
  apply (type_sys_props_ts_sym3 ts) with (C := substc a v' B') (eq1 := eqb2 a' a e2); sp.
Qed.*)

(*Lemma eq_term_equals_type_family2 {p} :
  forall lib (T1 T2 : @CTerm p) eqa1 eqa2 eqb1 eqb2 ts A v B A' v' B'
         (C : CTerm -> forall v : NVar, CVTerm [v] -> CTerm),
    (forall x y z a b c, C x y z = C a b c -> x = a # y = b)
    -> (forall x y z c, C x y z = C x y c -> z = c)
    -> type_family C ts uk lib T1 T2 eqa1 eqb1
    -> ccomputes_to_valc_ext lib T2 (C A v B)
    -> type_sys_props ts uk lib A A' eqa2
    -> (forall (a a' : CTerm) (e : eqa2 a a'),
          type_sys_props ts uk lib
                         (substc a v B)
                         (substc a' v' B')
                         (eqb2 a a' e))
    -> eq_term_equals eqa2 eqa1
       # (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a1 a2 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a2 a1 e2))
       # (forall a1 a2 (e1 : eqa2 a1 a2) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a2 e1) (eqb2 a2 a1 e2))
       # type_family C ts uk lib T1 T2 eqa2 eqb2
       # type_family C ts uk lib T2 T1 eqa2 eqb2.
Proof.
  introv c1 c2 tf co1 tspa ftspb; introv.
  unfold type_family in tf; exrepd.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  generalize (type_sys_props_ts_refl ts uk lib A'0 A' eqa2); intro k; dest_imp k h; repnd.

  (* First clause *)
  assert (eq_term_equals eqa2 eqa1) as eqta.
  apply (type_sys_props_eq_term_equals ts lib) with (A := A0) (B := A'0) (C := A'); sp.

  (* Second clause *)
  assert (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
             eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2)) as feqtb.
  intros.
  assert (eqa1 a1 a1)
         as e3
         by (rw <- eqta;
             onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tet with (t2 := a2); sp).
  assert (eqa2 a1 a1)
         as e4
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tet with (t2 := a2); sp).
  assert (eqa2 a2 a1)
         as e5 by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  generalize (t0 a1 a2 e1); intro ts1.
  generalize (ftspb a2 a1 e5); intro i.
  generalize (eq_term_equals_sym_tsp ts uk lib eqa2 eqb2 a1 a2 e4 e2 e5 v'0 B'0 v' B' ftspb); intro l; repnd.
  apply eq_term_equals_trans with (eq2 := eqb2 a2 a1 e5).
  apply eq_term_equals_sym.
  apply (type_sys_props_eq_term_equals ts lib)
        with (A := substc a1 v0 B0) (B := substc a2 v'0 B'0) (C := substc a1 v' B'); sp.
  apply eq_term_equals_trans with (eq2 := eqb2 a1 a1 e4); sp.
  apply eq_term_equals_sym; sp.

  (* Third clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a1 a2 e2)) as feqtb1.
  intros.
  generalize (ftspb a1 a1 e1); intro tsp1.
  generalize (ftspb a1 a2 e2); intro tsp2.
  apply type_sys_props_ts_refl in tsp1; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  implies_ts_or (substc a2 v' B') tsp0.
  apply uv in tsp0; sp.
  apply eq_term_equals_sym; sp.

  (* Fourth clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a1) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a1 e1) (eqb2 a2 a1 e2)) as feqtb2.
  intros.
  generalize (ftspb a1 a1 e1); intro tsp1.
  generalize (ftspb a2 a1 e2); intro tsp2.
  apply type_sys_props_ts_refl in tsp1; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  rev_implies_ts_or (substc a2 v'0 B'0) tsp1.
  apply uv in tsp1; sp.
  apply eq_term_equals_sym; sp.

  (* Fifth clause *)
  assert (forall a1 a2 (e1 : eqa2 a1 a2) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb2 a1 a2 e1) (eqb2 a2 a1 e2)) as feqtb3.
  intros.
  assert (eqa2 a1 a1)
         as e11
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tet with (t2 := a2); sp).
  generalize (feqtb1 a1 a2 e11 e1); intro tsp1.
  generalize (feqtb2 a1 a2 e11 e2); intro tsp2.
  apply eq_term_equals_trans with (eq2 := eqb2 a1 a1 e11); sp.
  apply eq_term_equals_sym; auto.

  (* this gets the first non type_family clauses *)
  sp.

  (* we prove the first type_family *)
  unfold type_family.
  exists A0 A'0 v0 v'0 B0 B'0; sp; spcast; sp.

  apply (type_sys_props_ts_uv ts lib) with (C := A') (eq1 := eqa1); sp.

  assert (eqa1 a a') as e1 by (rw <- eqta; auto).
  assert (eqa2 a' a)
         as e2
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  generalize (ftspb a' a e2); intro i.

  generalize (t0 a a' e1); intro j.
  apply (type_sys_props_ts_uv4 ts lib) with (C := substc a v' B') (eq1 := eqb1 a a' e1) (eq2 := eqb2 a' a e2); sp.

  (* we prove the second type_family *)
  unfold type_family.
  exists A'0 A0 v'0 v0 B'0 B0; sp; spcast; sp.

  assert (ts lib A0 A'0 eqa2)
         as i by (apply (type_sys_props_ts_uv ts lib) with (C := A') (eq1 := eqa1); sp).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tygs A'0 A0 eqa2); intro j; dest_imp j h.
  rw j; sp.

  assert (eqa1 a' a)
         as e1
         by (rw <- eqta;
             onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             auto).
  assert (eqa2 a' a) as e2 by (rw eqta; auto).
  generalize (t0 a' a e1); intro tsb1.
  generalize (ftspb a a' e); intro tspb.

  assert (ts lib (substc a' v0 B0) (substc a v'0 B'0) (eqb2 a a' e))
         as i
         by (apply (type_sys_props_ts_uv4 ts lib) with (C := substc a' v' B') (eq1 := eqb1 a' a e1) (eq2 := eqb2 a a' e); sp).
  apply (type_sys_props_ts_sym2 ts) with (C := substc a' v' B') (eq1 := eqb2 a a' e); sp.
Qed.*)

(*Lemma type_family_trans {p} :
  forall C (ts : cts(p)) uk lib T1 T2 T3 eqa eqb eqa1 eqb1 eqa2 eqb2 A v B A' v' B',
    (forall x y z a b c, C x y z = C a b c -> x = a # y = b)
    -> (forall x y z c, C x y z = C x y c -> z = c)
    -> ccomputes_to_valc_ext lib T1 (C A v B)
    -> ccomputes_to_valc_ext lib T2 (C A' v' B')
    -> type_sys_props ts uk lib A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_sys_props ts uk lib
                         (substc a v B)
                         (substc a' v' B')
                         (eqb a a' e))
    -> type_family C ts uk lib T1 T2 eqa1 eqb1
    -> type_family C ts uk lib T2 T3 eqa2 eqb2
    -> eq_term_equals eqa eqa1
       # eq_term_equals eqa1 eqa2
       # (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa1 a1 a2),
            eq_term_equals (eqb a1 a2 e1) (eqb1 a1 a2 e2))
       # (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
       # type_family C ts uk lib T1 T3 eqa eqb.
Proof.
  introv c1 c2 co1 co2 tspa ftspb tf1 tf2.
  allunfold @type_family; exrepnd.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  (* We prove the first clause *)
  assert (eq_term_equals eqa eqa1)
         as eqta1
         by (generalize (uv A' eqa1); sp).

  (*  *)
  assert (eq_term_equals eqa eqa2)
         as eqta2 by (generalize (uv A'0 eqa2); sp).

  (* We prove the second clause *)
  assert (eq_term_equals eqa1 eqa2)
         as eqta3
         by (apply eq_term_equals_trans with (eq2 := eqa); sp;
             apply eq_term_equals_sym; sp).

  (* We prove the third clause *)
  assert (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa1 a1 a2),
            eq_term_equals (eqb a1 a2 e1) (eqb1 a1 a2 e2)) as eqtb1.
  intros.
  generalize (tf1 a1 a2 e2); intro ts1.
  generalize (ftspb a1 a2 e1); intro tsp.
  apply (type_sys_props_eq_term_equals2 ts lib)
        with (A := substc a1 v B) (B := substc a2 v' B') (C := substc a1 v B); sp.

  (* *)
  assert (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa2 a2 a1),
            eq_term_equals (eqb a1 a2 e1) (eqb2 a2 a1 e2)) as eqtb2.
  intros.
  generalize (tf2 a2 a1 e2); intro ts1.
  generalize (ftspb a1 a2 e1); intro tsp.
  apply (type_sys_props_eq_term_equals3 ts lib)
        with (A := substc a1 v'0 B'0) (B := substc a2 v' B') (C := substc a1 v B); sp.

  (* *)
  generalize (eq_term_equals_sym_tsp2 ts uk lib eqa eqb v B v' B' tet ftspb); intro i; repnd.

  (* We prove the fourth clause *)
  assert (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2)) as eqtb3.
  intros.
  assert (eqa a1 a2) as e3 by (rw eqta1; auto).
  assert (eqa a2 a1) as e4 by sp.
  generalize (eqtb1 a1 a2 e3 e1); intro k.
  generalize (eqtb2 a2 a1 e4 e2); intro l.
  apply eq_term_equals_trans with (eq2 := eqb a1 a2 e3); sp.
  apply eq_term_equals_sym; sp.
  apply eq_term_equals_trans with (eq2 := eqb a2 a1 e4); sp.

  (* We prove the third clause *)
  sp.

  exists A A'0 v v'0 B B'0; sp; spcast; sp.
  generalize (tyt A'0 eqa2); sp.

  assert (eqa a' a') as e1 by (apply tet with (t2 := a); auto).
  assert (eqa2 a' a') as e3 by (rw <- eqta2; auto).
  assert (eqa1 a a') as e4 by (rw <- eqta1; auto).

  generalize (tf1 a a' e4); intro ts1.
  generalize (tf2 a' a' e3); intro ts2.
  generalize (ftspb a a' e); intro tspb.

  apply (type_sys_props_ts_trans ts lib) with (B := substc a' v' B') (eq1 := eqb1 a a' e4) (eq2 := eqb2 a' a' e3); sp.
Qed.*)

Lemma type_sys_props_eq {p} :
  forall (ts : cts(p)) uk lib A B C eq1 eq2,
    type_sys_props ts uk lib A C eq1
    -> type_sys_props ts uk lib B C eq2
    -> ts uk lib A B eq1.
Proof.
  introv tsp1 tsp2.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
  generalize (tygs B C eq2); intro i; dest_imp i h.
  rw i in tygt.
  generalize (tyt2 B eq2); sp.
Qed.

Lemma type_sys_props_ts_trans2 {p} :
  forall (ts : cts(p)) uk lib A B C D eq1 eq2 eq,
    ts uk lib A B eq1
    -> ts uk lib A C eq2
    -> type_sys_props ts uk lib A D eq
    -> ts uk lib B C eq.
Proof.
  introv ts1 ts2 tsp.
  generalize (type_sys_props_ts_uv2 ts uk lib B A D eq1 eq); intro i; repeat (dest_imp i h).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq); intro j; dest_imp j h.
  rw j in i.
  pose proof (tymt A B C eq eq2) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma type_sys_props_ts_trans3 {p} :
  forall (ts : cts(p)) uk lib A B C D eq1 eq2 eq,
    ts uk lib A B eq1
    -> ts uk lib B C eq2
    -> type_sys_props ts uk lib B D eq
    -> ts uk lib A C eq1.
Proof.
  introv ts1 ts2 tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  pose proof (tymt B A C eq1 eq2) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma type_sys_props_ts_trans4 {p} :
  forall (ts : cts(p)) uk lib A B C D eq1 eq2 eq,
    ts uk lib A B eq1
    -> ts uk lib B C eq2
    -> type_sys_props ts uk lib B D eq
    -> ts uk lib A C eq2.
Proof.
  introv ts1 ts2 tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  pose proof (tymt B A C eq1 eq2) as q; repeat (autodimp q hyp); tcsp.
Qed.

Lemma type_sys_props_ts_trans5 {p} :
  forall (ts : cts(p)) uk lib A B C D eq1 eq2 eq,
    ts uk lib A B eq1
    -> ts uk lib A C eq2
    -> type_sys_props ts uk lib A D eq
    -> ts uk lib B C eq1 # ts uk lib B C eq2 # ts uk lib C C eq2.
Proof.
  introv ts1 ts2 tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq1); intro j; dest_imp j h.
  generalize (tygs A C eq2); intro i; dest_imp i h.
  rw j in ts1.
  applydup i in ts2 as ts3.
  pd (tymt A B C eq1 eq2); pd (tymt A C C eq2 eq2).
Qed.

Lemma type_sys_props_ts_trans6 {p} :
  forall (ts : cts(p)) uk lib A B C eq1 eq2 eq,
    ts uk lib A B eq1
    -> ts uk lib B C eq2
    -> type_sys_props ts uk lib A B eq
    -> ts uk lib A C eq1 # ts uk lib A C eq2 # ts uk lib C C eq2.
Proof.
  introv ts1 ts2 tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tyt C eq2); sp.
  pd (dum B A C eq1 eq2).
Qed.

(*Lemma type_family_refl {p} :
  forall C (ts : cts(p)) uk lib T1 T2 eqa eqb A v B A' v' B',
    (forall x y z a b c, C x y z = C a b c -> x = a # y = b)
    -> (forall x y z c, C x y z = C x y c -> z = c)
    -> type_sys_props ts uk lib A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_sys_props ts uk lib (substc a v B) (substc a' v' B') (eqb a a' e))
    -> ccomputes_to_valc_ext lib T1 (C A v B)
    -> type_family C ts uk lib T1 T2 eqa eqb
    -> type_family C ts uk lib T1 T1 eqa eqb
       # type_family C ts uk lib T2 T2 eqa eqb.
Proof.
  introv c1 c2 tspa tspb co1 tf.
  allunfold @type_family; exrepd.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.

  dands.

  exists A A v v B B; sp; spcast; sp.

  generalize (type_sys_props_ts_refl ts uk lib A A' eqa); sp.

  assert (eqa a' a')
         as e'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt;
             apply tet with (t2 := a); sp).
  generalize (tspb a a' e); intro i.
  generalize (tspb a' a' e'); intro j.
  apply (type_sys_props_eq ts lib) with (C := substc a' v' B') (eq2 := eqb a' a' e'); sp.

  exists A'0 A'0 v'0 v'0 B'0 B'0; sp; spcast; sp.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tyst A'0 eqa); sp.

  assert (eqa a a)
         as e'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt;
             apply tet with (t2 := a'); sp).
  generalize (tspb a a' e); intro i.
  generalize (t0 a a' e); intro j.
  generalize (t0 a a e'); intro k.

  generalize (type_sys_props_ts_trans2 ts uk lib (substc a v B) (substc a v'0 B'0) (substc a' v'0 B'0) (substc a' v' B') (eqb a a e') (eqb a a' e) (eqb a a' e)); sp.
Qed.*)

(*
Lemma type_family_trans :
  forall C ts T1 T2 T3 eqa1 eqb1 eqa2 eqb2 A v B A' v' B',
    (forall x y z a b c, C x y z = C a b c -> x = a # y = b)
    -> (forall x y z c, C x y z = C x y c -> z = c)
    -> computes_to_valc T1 (C A v B)
    -> type_sys_props ts A A' eqa1
    -> (forall (a a' : CTerm) (e : eqa1 a a'),
          type_sys_props ts
                         (substc a v B)
                         (substc a' v' B')
                         (eqb1 a a' e))
    -> type_family C ts T1 T2 eqa1 eqb1
    -> type_family C ts T2 T3 eqa2 eqb2
    -> eq_term_equals eqa1 eqa2
       # (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
       # type_family C ts T1 T3 eqa1 eqb1.
Proof.
  introv c1 c2 co tspa ftspb tf1 tf2.
  allunfold type_family; exrepnd.
  computes_to_eqval.
  applydup c1 in eq; repd; subst; apply c2 in eq; subst; GC.
  computes_to_eqval.
  applydup c1 in eq; repd; subst; apply c2 in eq; subst; GC.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  (* We prove the first clause *)
  assert (eq_term_equals eqa1 eqa2)
         as eqta
         by (generalize (tygt A A'1 A'0 eqa1 eqa2); sp;
             apply uv with (T3 := A'0); sp).

  (* We prove the second clause *)
  assert (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2)).
  intros.
  assert (eqa1 a1 a1) as e3 by (apply tet with (t2 := a2); auto).
  generalize (tf1 a1 a1 e3); intro ts1.
  generalize (tf2 a1 a2 e2); intro ts2.
  generalize (ftspb a1 a2 e1); intro tsp.

  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (tygt2 (substc a1 v B)
                    (substc a1 v'1 B'1)
                    (substc a2 v'0 B'0)
                    (eqb1 a1 a1 e3)
                    (eqb2 a1 a2 e2)); sp.
  implies_ts_or (substc a2 v' B') X.
  apply uv2 in X; sp.

  (* We prove the third clause *)
  sp.

  exists A A'0 v v'0 B B'0; sp.
  generalize (tygt A A'1 A'0 eqa1 eqa2); sp.

  assert (eqa1 a' a') as e1 by (apply tet with (t2 := a); auto).
  assert (eqa2 a' a') as e2 by (rw <- eqta; sp).

  generalize (tf1 a a' e); intro ts1.
  generalize (tf2 a' a' e2); intro ts2.
  generalize (ftspb a a' e); intro tspb.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (tygt2 (substc a v B)
                    (substc a' v'1 B'1)
                    (substc a' v'0 B'0)
                    (eqb1 a a' e)
                    (eqb2 a' a' e2)); sp.
Qed.
*)

(*Lemma type_family_trans2 {p} :
  forall C (ts : cts(p)) uk lib T1 T2 T3 eqa1 eqb1 eqa2 eqb2 A v B A' v' B',
    (forall x y z a b c, C x y z = C a b c -> x = a # y = b)
    -> (forall x y z c, C x y z = C x y c -> z = c)
    -> ccomputes_to_valc_ext lib T2 (C A v B)
    -> type_sys_props ts uk lib A A' eqa1
    -> (forall (a a' : CTerm) (e : eqa1 a a'),
          type_sys_props ts uk lib
                         (substc a v B)
                         (substc a' v' B')
                         (eqb1 a a' e))
    -> type_family C ts uk lib T1 T2 eqa1 eqb1
    -> type_family C ts uk lib T2 T3 eqa2 eqb2
    -> eq_term_equals eqa1 eqa2
       # (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
       # type_family C ts uk lib T1 T3 eqa1 eqb1.
Proof.
  introv c1 c2 co tspa ftspb tf1 tf2.
  allunfold @type_family; exrepnd.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  ccomputes_to_eqval.
  applydup c1 in eqt; repd; subst; apply c2 in eqt; subst; GC.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.

  (* We prove the first clause *)
  assert (eq_term_equals eqa1 eqa2)
         as eqta
         by (implies_ts_or A' tf4; apply uv in tf4; sp).

  (* We prove the second clause *)
  assert (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
            eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2)).
  intros.
  generalize (tf2 a1 a2 e2); intro ts2.
  generalize (ftspb a1 a2 e1); intro tsp.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  implies_ts_or (substc a2 v' B') ts2.
  apply uv2 in ts2; sp.

  (* We prove the third clause *)
  sp.

  exists A1 A'0 v1 v'0 B1 B'0; sp; spcast; sp.

  { pd (tymt A A1 A'0 eqa1 eqa2). }

  assert (eqa1 a' a') as e1 by (apply tet with (t2 := a); auto).
  assert (eqa2 a' a') as e2 by (rw <- eqta; sp).

  generalize (tf1 a a' e); intro ts1.
  generalize (tf2 a' a' e2); intro ts2.
  generalize (ftspb a' a' e1); intro tspb.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
  pd (tymt2 (substc a' v B)
            (substc a v1 B1)
            (substc a' v'0 B'0)
            (eqb1 a a' e)
            (eqb2 a' a' e2)).
Qed.*)

Definition bcequivc_ext {p}
           (lib : library)
           (vs1 : list NVar)
           (t1  : @CVTerm p vs1)
           (vs2 : list NVar)
           (t2  : CVTerm vs2) :=
  in_ext lib (fun lib => Cast (bcequivc lib vs1 t1 vs2 t2)).

Lemma bcequivc_ext1 {o} :
  forall (lib : @library o) v1 v2 t1 t2,
    bcequivc_ext lib [v1] t1 [v2] t2
    -> forall t,
         ccequivc_ext lib (substc t v1 t1) (substc t v2 t2).
Proof.
  introv beq i.
  applydup beq in i; spcast.
  eapply bcequivc1; eauto.
Qed.

Lemma type_family_cequivc {p} :
  forall C (ts : cts(p)) uk (lib : library) T1 T2 eqa eqb A1 v1 B1 A2 v2 B2 A v B,
    cequivc lib T1 T2
    -> ccomputes_to_valc_ext lib T1 (C A1 v1 B1)
    -> ccomputes_to_valc_ext lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> ts uk lib A1 A eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v B)
                         (eqb a1 a2 e))
    -> type_sys_props ts uk lib A1 A eqa
    -> type_family C ts uk lib T1 T2 eqa eqb.
Proof.
  introv ceq co1 co2 ca cb tsa ftspb tspa.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  unfold type_family.
  exists A1 A2 v1 v2 B1 B2; sp; spcast; sp.

  assert (eqa a' a') as e' by (apply tet with (t2 := a); sp).

  generalize (ftspb a' a' e'); intro i.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (tyvr2 (substc a' v1 B1) (substc a' v2 B2)); intro k.
  dest_imp k h.
  dest_imp k h.

  {
    apply bcequivc_ext1 with (t := a') in cb; auto.
  }

  generalize (ftspb a a' e); intro i.
  generalize (ftspb a' a' e'); intro j.

  generalize (type_sys_props_eq ts uk lib (substc a v1 B1) (substc a' v1 B1) (substc a' v B) (eqb a a' e) (eqb a' a' e')); intro l; repeat (dest_imp l h).
  generalize (type_sys_props_ts_trans3 ts uk lib (substc a v1 B1) (substc a' v1 B1) (substc a' v2 B2) (substc a' v B) (eqb a a' e) (eqb a' a' e') (eqb a' a' e')); sp.
Qed.

Lemma type_family_cequivc2 {p} :
  forall C (ts : cts(p)) uk (lib : library) T1 T2 eqa eqb A1 v1 B1 A2 v2 B2 A v B,
    cequivc lib T1 T2
    -> ccomputes_to_valc_ext lib T1 (C A1 v1 B1)
    -> ccomputes_to_valc_ext lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> ts uk lib A A1 eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v B)
                         (substc a2 v1 B1)
                         (eqb a1 a2 e))
    -> type_sys_props ts uk lib A A1 eqa
    -> type_family C ts uk lib T1 T2 eqa eqb.
Proof.
  introv ceq co1 co2 ca cb tsa ftspb tspa.

  apply
    @type_family_cequivc
    with
      (A1 := A1)
      (v1 := v1)
      (B1 := B1)
      (A2 := A2)
      (v2 := v2)
      (B2 := B2)
      (A := A)
      (v := v)
      (B := B); sp;
  try (complete (apply (type_sys_props_sym ts uk lib); sp)).

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  assert (eqa a2 a1) as e1 by sp.
  assert (eqa a1 a1) as e2 by (apply tet with (t2 := a2); sp).
  assert (eqa a2 a2) as e3 by (apply tet with (t2 := a1); sp).

  apply type_sys_props_sym; sp.
  apply type_sys_props_eqb_comm; sp.
Qed.

(*
Lemma type_family_eq_term_equals :
  forall T1 T2 eqa1 eqa2 eqb1 eqb2 ts C,
    (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
       eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
    -> type_family C ts T1 T2 eqa1 eqb1
    -> eq_term_equals eqa2 eqa1
    -> type_family C ts T1 T2 eqa2 eqb2.
Proof.
  introv feqtb tf eqta.
  allunfold type_family; exrepd.
  exists A A' v v' B B'; sp.
Qed.
*)



Lemma is_per_iff {p} :
  forall eq1 eq2,
    (forall x y : @CTerm p, inhabited (eq1 x y) <=> inhabited (eq2 x y))
    -> is_per eq1
    -> is_per eq2.
Proof.
  unfold is_per; introv iff isper1.
  destruct isper1 as [sym tran]; sp.
  discover; sp.
  apply iff.
  apply tran with (y := y); sp; apply iff; sp.
Qed.

Lemma eq_term_equals_implies_inhabited {p} :
  forall a b,
    @eq_term_equals p a b
    -> (inhabited a <=> inhabited b).
Proof.
  unfold eq_term_equals, inhabited; sp; split; sp; exists t.
  allrw <-; sp.
  allrw; sp.
Qed.

Lemma is_per_sym {p} :
  forall (a b : @CTerm p) eq,
    is_per eq
    -> inhabited (eq a b)
    -> inhabited (eq b a).
Proof.
  introv isper inh.
  allunfold @is_per; sp.
Qed.

Lemma is_per_trans {p} :
  forall (a b c : @CTerm p) eq,
    is_per eq
    -> inhabited (eq a b)
    -> inhabited (eq b c)
    -> inhabited (eq a c).
Proof.
  introv isper inh.
  allunfold @is_per; sp.
  generalize (isper a b c); sp.
Qed.

Lemma type_sys_props_pertype_eq_term_equals {p} :
  forall (ts : cts(p)) uk lib R eq1 eq2,
    (forall x y, type_sys_props ts uk lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq1 x y))
    -> (forall x y, ts uk lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq2 x y))
    -> (forall x y, eq_term_equals (eq1 x y) (eq2 x y)).
Proof.
  introv tsp tseq; intros.
  generalize (tseq x y); intro j.
  generalize (tsp x y); intro k.
  repeat (dest_imp k h).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  implies_ts_or (mkc_apply2 R x y) j.
  apply uv in j; sp.
Qed.


Lemma weq_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p))
         eqb1 eqb2 t1 t2,
    (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
       eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
    -> eq_term_equals eqa1 eqa2
    -> weq lib eqa1 eqb1 t1 t2
    -> weq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqbeq eqaeq weqt.
  induction weqt as [t t' a f a' f' e c c' h h'].
  duplicate e as e'.
  rw eqaeq in e.
  apply @weq_cons with (a := a) (a' := a') (f := f) (f' := f') (e := e); sp.
  apply h'.
  generalize (eqbeq a a' e' e); intro eqb.
  rw eqb; sp.
Qed.

Lemma weq_sym {p} :
  forall uk lib eqa eqb t1 t2 v1 v2 B1 B2 (ts : cts(p)),
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq lib eqa eqb t1 t2
    -> weq lib eqa eqb t2 t1.
Proof.
  introv teqsa teqta ftsp weq1.
  induction weq1 as [t t' a f a' f' e c c' h h'].
  duplicate e as e'.
  apply teqsa in e.
  apply @weq_cons with (a := a') (f := f') (a' := a) (f' := f) (e := e); sp.
  apply h'; sp.
  generalize (eq_term_equals_sym_tsp2 ts uk lib eqa eqb v1 B1 v2 B2); introv i.
  dest_imp i hyp; sp.
  generalize (i a a' e' e); intro eqeb.
  rw eqeb.
  generalize (ftsp a' a e); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma eq_family_trans1 {o} :
  forall uk (lib : @library o) eqa eqb
         a a1 a2 t1 t2
         ts v1 B1 v2 B2
         (e1 : eqa a a1) (e2 : eqa a a2),
    (forall (a1 a2 : @CTerm o) (e : eqa a1 a2),
       type_sys_props ts uk lib
                      (substc a1 v1 B1)
                      (substc a2 v2 B2)
                      (eqb a1 a2 e))
    -> eqb a a1 e1 t1 t2
    -> eqb a a2 e2 t1 t2.
Proof.
  introv ftsp eqb1.
  generalize (ftsp a a1 e1); intro tsp1.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
  generalize (ftsp a a2 e2); intro tsp2.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.
  pd (uv2 (substc a1 v2 B2) (eqb a a1 e1)).
  rw h; sp.
Qed.

(*Lemma weq_trans {o} :
  forall (lib : @library o) eqa eqb t1 t2 t3 ts v1 B1 v2 B2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm o) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq lib eqa eqb t1 t2
    -> weq lib eqa eqb t2 t3
    -> weq lib eqa eqb t1 t3.
Proof.
  introv teqsa teqta ftsp weq1.
  generalize t3; clear t3.
  induction weq1 as [t t' a f a' f' e c c' h h'].
  introv weq2.
  inversion weq2 as [x g a'0 f'0 e0 d d' h1].
  ccomputes_to_eqval.
  assert (eqa a a'0) as e' by (apply teqta with (t2 := a'); sp).
  apply @weq_cons with (a := a) (f := f) (a' := a'0) (f' := f'0) (e := e');
    try (complete (spcast; sp)); introv hyp.
  apply h' with (b' := b'); sp.
  apply (eq_family_trans1 lib) with (a1 := a'0) (ts := ts) (v1 := v1) (B1 := B1) (v2 := v2) (B2 := B2) (e1 := e'); sp.
  apply h1.
  generalize (eq_term_equals_sym_tsp2 ts uk lib eqa eqb v1 B1 v2 B2); intro i; sp.
  duplicate e0 as e1.
  apply teqsa in e0.
  duplicate e' as e2.
  apply teqsa in e'.
  generalize (i a' a'0 e1 e0); intro eq1.
  rw eq1.
  generalize (i a a'0 e2 e'); intro eq2.
  rw eq2 in hyp.
  apply (eq_family_trans1 lib) with (a1 := a) (ts := ts) (v1 := v1) (B1 := B1) (v2 := v2) (B2 := B2) (e1 := e'); sp.
  generalize (ftsp a'0 a e'); intro tsp.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
  apply tet1 with (t2 := b); sp.
Qed.*)

(*
Lemma weq_cequivc2 :
  forall eqa eqb ts v1 B1 v2 B2 a a' e f f' b b',
    term_equality_respecting eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq eqa eqb (mkc_apply f b) (mkc_apply f b)
    -> eqb a a' e b b'
    -> cequivc f f'
    -> weq eqa eqb (mkc_apply f b) (mkc_apply f' b').
Proof.
  introv tera tesa teta ftspb weq1 eqb1 ceq.
  generalize f' b' eqb1 ceq; clear ceq eqb1 b' f'.
  remember (mkc_apply f b).
  generalize Heqc; clear Heqc.
  induction weq1.
  introv eq eqb1 ceq; subst.
  generalize (cequivc_mkc_sup t' t'0 a' f'); intros i.
  repeat (dest_imp i hyp); exrepnd.
  rename b' into f'0.
  unfold term_equality_respecting in tera.
  generalize (tera a' a'0); intro j.
  repeat (dest_imp j hyp).
  apply teta with (t2 := a); sp.
  apply weq_cons with (a := a') (f := f') (a' := a'0) (f' := f'0) (e := j); sp.
  apply X with (b := b'); sp.

  generalize (eq_term_equals_sym_tsp2 ts eqa eqb v1 B1 v2 B2); introv i.
  repeat (dest_imp i hyp); repnd.
  assert (eqa a' a) as e' by sp.
  generalize (i a a' e e'); intro eqt; rw eqt.
  generalize (ftspb a' a e'); intro tspb.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tes.
  generalize (eq_family_trans1 eqa eqb a' a'0 a b b' ts v1 B1 v2 B2 j e'); sp.

Abort.
*)

Lemma cequivc_val {o} :
  forall lib (t t' : @CTerm o) v,
    computes_to_valc lib t v
    -> cequivc lib t t'
    -> {w : CTerm & computes_to_valc lib t' w}.
Proof.
  introv comp ceq.
  destruct ceq as [h1 h2].
  dup h1 as apr.
  invertsn apr.
  repnud apr.
  dup comp as c.
  unfold computes_to_valc, computes_to_value in c; repnd.
  unfold computes_to_valc in *.
  applydup @isvalue_implies_iscan in c.
  apply iscan_implies in c1; exrepnd; rewrite c1 in *.
  apply apr2 in comp; exrepnd.
  applydup @preserve_program in comp1; eauto 3 with slow.
  exists (mk_cterm (oterm (Can c2) tr_subterms) comp2); simpl; dands; eauto 3 with slow.
Qed.

Lemma implies_approx_sup {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_sup f a) (mk_sup g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_sup {p} :
  forall lib f g a b,
    cequivc lib f g
    -> @cequivc p lib a b
    -> cequivc lib (mkc_sup f a) (mkc_sup g b).
Proof.
  unfold cequivc. introv H1c H2c.
  destruct_cterms. allsimpl. apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_sup; auto.
Qed.

Lemma ccequivc_ext_refl {o} :
  forall lib (a : @CTerm o), ccequivc_ext lib a a.
Proof.
  introv ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_refl : slow.

Lemma ccequivc_ext_mkc_sup {o} :
  forall lib t t' (a b : @CTerm o),
    ccomputes_to_valc_ext lib t (mkc_sup a b)
    -> ccequivc_ext lib t t'
    -> ccomputes_to_valc_ext lib t' (mkc_sup a b).
Proof.
  introv comp ceq.
  introv i.
  applydup comp in i as comp'; exrepnd.
  applydup ceq in i; spcast.
  eapply cequivc_mkc_sup in comp'0;[|eauto 3 with slow].
  exrepnd.
  apply computes_to_valc_isvalue_eq in comp'3; eauto 3 with slow; subst.
  dup i0 as ceq'.
  eapply @cequivc_val in ceq';[|eauto]; exrepnd.
  exists w; dands; spcast; eauto 3 with slow.
  eapply cequivc_trans;[|apply computes_to_valc_implies_cequivc;eauto].
  eapply cequivc_trans;[|eauto].
  apply cequivc_sym;eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; eauto|].
  apply cequivc_sym;apply implies_cequivc_sup; auto.
Qed.

Lemma sp_implies_ccequivc_ext_apply {o} :
  forall lib (f g a : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib (mkc_apply f a) (mkc_apply g a).
Proof.
  introv ceq ext.
  apply ceq in ext.
  spcast.
  apply sp_implies_cequivc_apply; auto.
Qed.

Lemma weq_cequivc {o} :
  forall uk (lib : @library o) eqa eqb t t1 t2 ts v1 B1 v2 B2,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm o) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq lib eqa eqb t t1
    -> ccequivc_ext lib t1 t2
    -> weq lib eqa eqb t t2.
Proof.
  introv tera tesa teta ftspb weq1.
  generalize t2; clear t2.
  induction weq1 as [t t' a f a' f' e c c' h h'].
  introv ceq.
  rename t' into t1.
  rename a' into a1.
  rename f' into f1.
  spcast.
  pose proof (ccequivc_ext_mkc_sup lib t1 t2 a1 f1) as i.
  repeat (dest_imp i hyp); exrepnd.
  eapply weq_cons; eauto.
Qed.

Lemma type_sys_props_cequivc {p} :
  forall (ts : cts(p)) uk lib A B C eq,
    type_sys_props ts uk lib A B eq
    -> ccequivc_ext lib A C
    -> ts uk lib A C eq.
Proof.
  introv tsp ceq.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tyvr A C); sp.
Qed.

Lemma iff_inhabited_if_eq_term_equals {p} :
  forall (eq1 eq2 : per(p)), (eq1 <=2=> eq2) -> (inhabited eq1 <=> inhabited eq2).
Proof.
  introv eqs.
  unfold inhabited; split; intro k; exrepnd; exists t;
  generalize (eqs t t); clear eqs; intro eqs;
  allrw; sp; allrw <-; sp.
Qed.

Lemma type_sys_props_pertype_eq_term_equals1 {p} :
  forall (ts : cts(p)) uk lib R R1 R2 eq1 eq2,
    (forall x y, type_sys_props ts uk lib (mkc_apply2 R x y) (mkc_apply2 R1 x y) (eq1 x y))
    -> (forall x y, ts uk lib (mkc_apply2 R x y) (mkc_apply2 R2 x y) (eq2 x y))
    -> (forall x y, (eq1 x y) <=2=> (eq2 x y)).
Proof.
  introv tsp k; intros t1 t2.
  generalize (k t1 t2); clear k; intro k.
  generalize (tsp t1 t2); clear tsp; intro tsp; repeat (autodimp tsp hyp).
  generalize (type_sys_props_eq_term_equals4
                ts uk lib
                (mkc_apply2 R t1 t2)
                (mkc_apply2 R2 t1 t2)
                (mkc_apply2 R1 t1 t2)
                (eq2 t1 t2) (eq1 t1 t2) k tsp); sp.
Qed.

Lemma type_sys_props_pertype_eq_term_equals2 {p} :
  forall (ts : cts(p)) uk lib R1 R2 R3 eq1 eq2,
    (forall x y, type_sys_props ts uk lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
    -> (forall x y, ts uk lib (mkc_apply2 R2 x y) (mkc_apply2 R3 x y) (eq2 x y))
    -> (forall x y, (eq1 x y) <=2=> (eq2 x y)).
Proof.
  introv tsp k; intros t1 t2.
  generalize (k t1 t2); clear k; intro k.
  generalize (tsp t1 t2); clear tsp; intro tsp; repeat (autodimp tsp hyp).
  generalize (type_sys_props_eq_term_equals3
                ts uk lib
                (mkc_apply2 R3 t1 t2)
                (mkc_apply2 R2 t1 t2)
                (mkc_apply2 R1 t1 t2)
                (eq2 t1 t2) (eq1 t1 t2) k tsp); sp.
Qed.
