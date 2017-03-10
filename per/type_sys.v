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


Require Export nuprl.
Require Export cequiv_refl.

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
(** printing <=2=> $\Leftarrow\!\!{\scriptstyle{2}}\!\!\Rightarrow$ *)

(* begin hide *)


(* end hide *)

(**

  A term equality is a partial equivalence relation if it is symmetric
  and transitive.  It also has to respect computation.

 *)

Definition term_equality_symmetric {p} (eq : per(p)) :=
  forall t1 t2, eq t1 t2 -> eq t2 t1.

Definition term_equality_transitive {p} (eq : per(p)) :=
  forall t1 t2 t3, eq t1 t2 -> eq t2 t3 -> eq t1 t3.

Definition term_equality_respecting {p} lib (eq : per(p)) :=
  forall t t', eq t t -> t ~=~(lib) t' -> eq t t'.

(**

  We now define the concept of a type system.  A candidate type system
  is a type system if it satisfies the following properties:

    - uniquely valued

    - type extensionality

    - type symmetric

    - type transitive

    - type value respecting

    - term symmetric

    - term transitive

    - term value respecting

  One difference with the way, e.g., the way Crary defines the value
  respecting
  properties%~\cite[section~4.4.1,definition~4.8,page~52]{Crary:1998}%
  is that he uses the computation relation while we have to use the
  computational equivalence relation.

  Here is the reason: In the case of equality types, we have to prove
  that [close cts] satisfies the type system properties.  Assuming
  that [per_eq cts T T' eq] is true, [T ===> (mkc_equality a1 a2 A)],
  [T' ===> (mkc_equality b1 b2 B)], and [eqa] is the equality relation
  of [A], and such that [close cts] satisfies the type system
  properties on [A], [B], and [eqa].

  In the [type_symmetric] case we have to prove [per_eq cts T' T eq].
  We can trivially prove most of the clauses of [per_eq].  The
  non-trivial one is proving the equivalence between [eq t t'] and [t
  ===> mkc_axiom # t' ===> mkc_axiom # eqa b1 b2] for all [t] and
  [t'], which we have to prove using the clause we get from [per_eq
  cts T T' eq], i.e., that [eq t t'] is equivalence to and [t ===>
  mkc_axiom # t' ===> mkc_axiom # eqa a1 a2] for all [t] and [t'].
  Therefore we have to prove that [eqa a1 a2] iff [eqa b1 b2] knowing
  that [eqorceq eqa a1 b1] and [eqorceq eqa a2 b2].  If [a1 ~=~ b1] or
  [a2 ~=~ b2] then to prove that double implication, we need to know
  that [A] and [B] are closed not only under computation but also
  under computational equivalence.

 *)

Definition uniquely_valued {p} (ts : cts(p)) :=
  forall T eq eq',
    ts T eq -> ts T eq' -> eq <=2=> eq'.

(* extensional type system *)
Definition ects o := @CTerm o -> @CTerm o -> per(o) -> [U].

Definition euniquely_valued {p} (ts : ects(p)) :=
  forall T T' eq eq',
    ts T T' eq -> ts T T' eq' -> eq <=2=> eq'.

Definition type_extensionality {p} (ts : cts(p)) :=
  forall T eq eq', ts T eq -> eq <=2=> eq' -> ts T eq'.

Definition etype_extensionality {p} (ts : ects(p)) :=
  forall T T' eq eq', ts T T' eq -> eq <=2=> eq' -> ts T T' eq'.

Definition etype_symmetric {p} (ts : ects(p)) :=
  forall T T' eq, ts T T' eq -> ts T' T eq.

Definition etype_transitive {p} (ts : ects(p)) :=
  forall T1 T2 T3 eq, ts T1 T2 eq -> ts T2 T3 eq -> ts T1 T3 eq.

(*
(* This is not part of a type system, but is sometimes easier to prove
 because stronger than type_transitive. *)
Definition type_trans (ts : cts) :=
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    ts T1 T2 eq1 -> ts T2 T3 eq2 -> (ts T1 T3 eq1 /\ eq_term_equals eq1 eq2).
*)

Definition type_value_respecting {p} lib (ts : cts(p)) :=
  forall T T' eq, ts T eq -> cequivc lib T T' -> ts T' eq.

Definition etype_value_respecting {p} lib (ts : ects(p)) :=
  forall T T' eq, ts T T eq -> cequivc lib T T' -> ts T T' eq.

Definition term_symmetric {p} (ts : cts(p)) :=
  forall T eq, ts T eq -> term_equality_symmetric eq.

Definition eterm_symmetric {p} (ts : ects(p)) :=
  forall T T' eq, ts T T' eq -> term_equality_symmetric eq.

Definition term_transitive {p} (ts : cts(p)) :=
  forall T eq, ts T eq -> term_equality_transitive eq.

Definition eterm_transitive {p} (ts : ects(p)) :=
  forall T T' eq, ts T T' eq -> term_equality_transitive eq.

Definition term_value_respecting {p} lib (ts : cts(p)) :=
  forall T eq, ts T eq -> term_equality_respecting lib eq.

Definition eterm_value_respecting {p} lib (ts : ects(p)) :=
  forall T T' eq, ts T T' eq -> term_equality_respecting lib eq.

(* begin hide *)

(*
Definition pre_type_system {p} (ts : ects(p)) : Type :=
  uniquely_valued ts
   # type_extensionality ts
   # type_symmetric ts
   # type_transitive ts
   # term_symmetric ts
   # term_transitive ts.
*)

(* end hide *)

Definition type_system {p} (lib : @library p) (ts : candidate_type_system) : Type :=
  uniquely_valued ts
   # type_extensionality ts
   # type_value_respecting lib ts
   # term_symmetric ts
   # term_transitive ts
   # term_value_respecting lib ts.

Definition etype_system {p} lib (ts : ects(p)) : Type :=
  euniquely_valued ts
   # etype_extensionality ts
   # etype_symmetric ts
   # etype_transitive ts
   # etype_value_respecting lib ts
   # eterm_symmetric ts
   # eterm_transitive ts
   # eterm_value_respecting lib ts.

(* begin hide *)

Ltac dest_ts ts :=
  destruct ts as [ ts_uv ts ];
  destruct ts as [ ts_ext ts ];
  destruct ts as [ ts_tyv ts ];
  destruct ts as [ ts_tes ts ];
  destruct ts as [ ts_tet ts_tev ].

Ltac dest_ets ts :=
  destruct ts as [ ts_uv ts ];
  destruct ts as [ ts_ext ts ];
  destruct ts as [ ts_tys ts ];
  destruct ts as [ ts_tyt ts ];
  destruct ts as [ ts_tyv ts ];
  destruct ts as [ ts_tes ts ];
  destruct ts as [ ts_tet ts_tev ].

(** Destruct type_system *)
Ltac onedts uv tye tyvr tes tet tevr :=
  match goal with
      [ H : type_system _ _ |- _ ] =>
      let tmp := fresh "tmp" in
      unfold type_system in H;
        destruct H   as [ uv   tmp ];
        destruct tmp as [ tye  tmp ];
        destruct tmp as [ tyvr tmp ];
        destruct tmp as [ tes  tmp ];
        destruct tmp as [ tet  tevr ]
  end.

(** Destruct etype_system *)
Ltac onedets uv tye tys tyt tyvr tes tet tevr :=
  match goal with
      [ H : etype_system _ _ |- _ ] =>
      let tmp := fresh "tmp" in
      unfold type_system in H;
        destruct H   as [ uv   tmp ];
        destruct tmp as [ tye  tmp ];
        destruct tmp as [ tys  tmp ];
        destruct tmp as [ tyt  tmp ];
        destruct tmp as [ tyvr tmp ];
        destruct tmp as [ tes  tmp ];
        destruct tmp as [ tet  tevr ]
  end.

Tactic Notation "prove_type_system" ident(c) :=
  unfold type_system;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_extensionality"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  ].

Tactic Notation "prove_etype_system" ident(c) :=
  unfold etype_system;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_extensionality"
  | Case_aux c "type_symmetric"
  | Case_aux c "type_transitive"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  ].

Definition uniquely_valued_body {p} (ts : cts(p)) (T : CTerm) (eq : per) :=
  forall eq' : per, ts T eq' -> eq <=2=> eq'.

Definition euniquely_valued_body {p}
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  forall eq' : per, ts T1 T2 eq' -> eq <=2=> eq'.

Definition type_extensionality_body {p}
           (ts : cts(p))
           (T : CTerm)
           (eq : per) :=
  forall eq' : per, eq <=2=> eq' -> ts T eq'.

Definition etype_extensionality_body {p}
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  forall (eq' : per), eq <=2=> eq' -> ts T1 T2 eq'.

Definition etype_symmetric_body {p}
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  ts T2 T1 eq.

Definition etype_transitive_body {p}
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  forall T3, ts T2 T3 eq -> ts T1 T3 eq.

Definition type_value_respecting_body {p}
           lib
           (ts : cts(p))
           (T : @CTerm p)
           (eq : per) :=
  forall T', cequivc lib T T' -> ts T' eq.

Definition etype_value_respecting_body {p}
           lib
           (ts : ects(p))
           (T1 T2 : @CTerm p)
           (eq : per) :=
  forall T3, cequivc lib T1 T3 -> ts T1 T3 eq.

Definition type_system_props {p}
           lib
           (ts : cts(p))
           (T : CTerm)
           (eq : per) :=
  uniquely_valued_body ts T eq
   # type_extensionality_body ts T eq
   # type_value_respecting_body lib ts T eq
   # term_equality_symmetric eq
   # term_equality_transitive eq
   # term_equality_respecting lib eq.

Definition etype_system_props {p}
           lib
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  euniquely_valued_body ts T1 T2 eq
   # etype_extensionality_body ts T1 T2 eq
   # etype_symmetric_body ts T1 T2 eq
   # etype_transitive_body ts T1 T2 eq
   # etype_value_respecting_body lib ts T1 T2 eq
   # term_equality_symmetric eq
   # term_equality_transitive eq
   # term_equality_respecting lib eq.

Definition is_type_system {p} lib (ts : cts(p)) :=
  forall T eq, ts T eq -> type_system_props lib ts T eq.

Definition is_etype_system {p} lib (ts : ects(p)) :=
  forall T1 T2 eq,
    ts T1 T2 eq -> etype_system_props lib ts T1 T2 eq.

Ltac dest_is_ts uv tye tyvr tes tet tevr :=
  match goal with
      [ H : type_system_props _ _ _ _ |- _ ] =>
      let tmp := fresh "tmp" in
      unfold type_system in H;
        destruct H   as [ uv   tmp ];
        destruct tmp as [ tye  tmp ];
        destruct tmp as [ tyvr tmp ];
        destruct tmp as [ tes  tmp ];
        destruct tmp as [ tet  tevr ]
  end.

Ltac dest_is_ets uv tye tys tyt tyvr tes tet tevr :=
  match goal with
      [ H : etype_system_props _ _ _ _ _ |- _ ] =>
      let tmp := fresh "tmp" in
      unfold etype_system in H;
        destruct H   as [ uv   tmp ];
        destruct tmp as [ tye  tmp ];
        destruct tmp as [ tys  tmp ];
        destruct tmp as [ tyt  tmp ];
        destruct tmp as [ tyvr tmp ];
        destruct tmp as [ tes  tmp ];
        destruct tmp as [ tet  tevr ]
  end.

Tactic Notation "prove_ts_props" ident(c) :=
  unfold type_system_props; dands; introv;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_extensionality"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  ].

Tactic Notation "prove_is_ts" ident(c) :=
  unfold is_type_system, type_system_props; introv cl;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_extensionality"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  ].

Tactic Notation "prove_is_ets" ident(c) :=
  unfold is_etype_system, etype_system_props; introv cl;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_extensionality"
  | Case_aux c "type_symmetric"
  | Case_aux c "type_transitive"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  ].

Lemma type_system_iff_is_type_system {p} :
  forall lib (ts : cts(p)),
    type_system lib ts <=> is_type_system lib ts.
Proof.
  introv; split; intro k.

  - onedts uv tye tyvr tes tet tevr.
    prove_is_ts Case.

    + Case "uniquely_valued".
      unfold uniquely_valued_body; introv e.
      unfold uniquely_valued in uv.
      generalize (uv T eq eq'); sp.

    + Case "type_extensionality".
      unfold type_extensionality_body; introv teq.
      unfold type_extensionality in tye.
      generalize (tye T eq eq'); sp.

    + Case "type_value_respecting".
      unfold type_value_respecting_body; introv c.
      unfold type_value_respecting in tyvr.
      generalize (tyvr T T' eq); intro k.
      repeat (dest_imp k hyp).

    + Case "term_symmetric".
      unfold term_symmetric in tes.
      generalize (tes T eq); sp.

    + Case "term_transitive".
      unfold term_transitive in tet.
      generalize (tet T eq); sp.

    + Case "term_value_respecting".
      unfold term_value_respecting in tevr.
      generalize (tevr T eq); intro k.
      repeat (dest_imp k hyp).

  - prove_type_system Case.

    + Case "uniquely_valued".
      unfold uniquely_valued; introv e1 e2.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr.
      unfold uniquely_valued_body in uv.
      generalize (uv eq'); sp.

    + Case "type_extensionality".
      unfold type_extensionality; introv e teq.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr.
      unfold type_extensionality_body in tye.
      generalize (tye eq'); sp.

    + Case "type_value_respecting".
      unfold type_value_respecting; introv e c.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr.
      apply tyvr; auto.

    + Case "term_symmetric".
      unfold term_symmetric; introv e.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr; auto.

    + Case "term_transitive".
      unfold term_transitive; introv e.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr; auto.

    + Case "term_value_respecting".
      unfold term_value_respecting; introv e.
      generalize (k T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ts uv tye tyvr tes tet tevr; auto.
Qed.

Lemma etype_system_iff_is_etype_system {p} :
  forall lib (ts : ects(p)),
    etype_system lib ts <=> is_etype_system lib ts.
Proof.
  introv; split; intro k.

  - onedets uv tye tys tyt tyvr tes tet tevr.
    prove_is_ets Case.

    + Case "uniquely_valued".
      unfold euniquely_valued_body; introv e.
      unfold euniquely_valued in uv.
      generalize (uv T1 T2 eq eq'); sp.

    + Case "type_extensionality".
      unfold etype_extensionality_body; introv teq.
      unfold etype_extensionality in tye.
      generalize (tye T1 T2 eq eq'); sp.

    + Case "type_symmetric".
      unfold etype_symmetric_body.
      unfold etype_symmetric in tys.
      generalize (tys T1 T2 eq); sp.

    + Case "type_transitive".
      unfold etype_transitive_body; introv e.
      unfold etype_transitive in tyt.
      generalize (tyt T1 T2 T3 eq); sp.

    + Case "type_value_respecting".
      unfold etype_value_respecting_body; introv c.
      unfold etype_value_respecting in tyvr.
      generalize (tyvr T1 T3 eq); intro k.
      repeat (dest_imp k hyp).
      unfold etype_transitive in tyt.
      generalize (tyt T1 T2 T1 eq); intro k.
      repeat (dest_imp k hyp).

    + Case "term_symmetric".
      unfold eterm_symmetric in tes.
      generalize (tes T1 T2 eq); sp.

    + Case "term_transitive".
      unfold eterm_transitive in tet.
      generalize (tet T1 T2 eq); sp.

    + Case "term_value_respecting".
      unfold eterm_value_respecting in tevr.
      generalize (tevr T1 T2 eq); intro k.
      repeat (dest_imp k hyp).


  - prove_etype_system Case.

    + Case "uniquely_valued".
      unfold euniquely_valued; introv e1 e2.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr.
      unfold uniquely_valued_body in uv.
      generalize (uv eq'); sp.

    + Case "type_extensionality".
      unfold etype_extensionality; introv e teq.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr.
      unfold etype_extensionality_body in tye.
      generalize (tye eq'); sp.

    + Case "type_symmetric".
      unfold etype_symmetric; introv e.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr.
      unfold etype_symmetric_body in tys; sp.

    + Case "type_transitive".
      unfold etype_transitive; introv e1 e2.
      generalize (k T1 T2 eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr.
      unfold etype_transitive_body in tyt.
      generalize (tyt T3); sp.

    + Case "type_value_respecting".
      unfold etype_value_respecting; introv e c.
      generalize (k T T eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr.
      unfold etype_value_respecting_body in tyvr.
      generalize (tyt T'); sp.

    + Case "term_symmetric".
      unfold eterm_symmetric; introv e.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr; auto.

    + Case "term_transitive".
      unfold eterm_transitive; introv e.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr; auto.

    + Case "term_value_respecting".
      unfold eterm_value_respecting; introv e.
      generalize (k T T' eq); clear k; intro k.
      dest_imp k hyp.
      dest_is_ets uv tye tys tyt tyvr tes tet tevr; auto.
Qed.


(*
Definition type_sys_props {p}
           (lib : library)
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  (* uniquely valued *)
  (forall T3 eq',
     (ts T1 T3 eq' [+] ts T2 T3 eq')
     -> eq_term_equals eq eq')
    # (* type_extensionality *)
    (forall T T3 eq',
       (T = T1 [+] T = T2)
       -> ts T T3 eq
       -> eq_term_equals eq eq'
       -> ts T T3 eq')
    # (* type transitive (1) *)
    (forall T3 eq',
       ts T2 T3 eq'
       -> ts T1 T3 eq # ts T1 T3 eq' # ts T3 T3 eq')
    # (* type transitivity (2) *)
    (forall T3 eq',
       ts T1 T3 eq'
       -> ts T2 T3 eq # ts T2 T3 eq' # ts T3 T3 eq')
    # (* type value respecting *)
    (forall T T3, (T = T1 [+] T = T2) -> cequivc lib T T3 -> ts T T3 eq)
    # (* term symmetric *)
    term_equality_symmetric eq
    # (* term transitivive (1) *)
    term_equality_transitive eq
    # (* term value respecting *)
    term_equality_respecting lib eq
    # (* type symmetric *)
    (forall T T3 eq', (T = T1 [+] T = T2) -> (ts T T3 eq' <=> ts T3 T eq'))
    # (* type transitive (3) *)
    ts T1 T2 eq
    (*(forall T T3 T4 eq1 eq2,
       (T = T1 [+] T = T2)
       -> ts T T3 eq1
       -> ts T3 T4 eq2
       -> ts T T4 eq1 # ts T T4 eq2)*)
    # (* type transitive (4) *)
    (forall T T3 T4 eq1 eq2,
       (T = T1 [+] T = T2)
       -> ts T3 T eq1
       -> ts T T4 eq2
       -> ts T3 T4 eq1 # ts T3 T4 eq2 # ts T T3 eq1).

Definition type_sys {p} lib (ts : ects(p)) :=
  forall T1 T2 eq,
    ts T1 T2 eq -> type_sys_props lib ts T1 T2 eq.

(** Destruct type_sys_props *)
Ltac dest_tsp c uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt :=
  let tmp := fresh "tmp" in
    unfold type_sys_props in c;
  destruct c   as [ uv   tmp ];
  destruct tmp as [ tys  tmp ];
  destruct tmp as [ tyt  tmp ];
  destruct tmp as [ tyst tmp ];
  destruct tmp as [ tyvr tmp ];
  destruct tmp as [ tes  tmp ];
  destruct tmp as [ tet  tmp ];
  destruct tmp as [ tevr tmp ];
  destruct tmp as [ tygs tmp ];
  destruct tmp as [ tygt tymt ].

Ltac onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt :=
  match goal with
      [ H : type_sys_props _ _ _ _ _ |- _ ] =>
      dest_tsp H uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt
  end.

(** This is like dest_tsp, but it picks the names of the clauses *)
Ltac dtsp c :=
  let uv   := fresh "tsp_uv"   in
  let tys  := fresh "tsp_tys"  in
  let tyt  := fresh "tsp_tyt"  in
  let tyst := fresh "tsp_tyst" in
  let tyvr := fresh "tsp_tyvr" in
  let tes  := fresh "tsp_tes"  in
  let tet  := fresh "tsp_tet"  in
  let tevr := fresh "tsp_tevr" in
  let tygs := fresh "tsp_tygs" in
  let tygt := fresh "tsp_tygt" in
  let tymt := fresh "tsp_tymt" in
  dest_tsp c uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.

Ltac d_tsp :=
  match goal with
      [ H : type_sys_props _ _ _ _ _ |- _ ] => dtsp H
  end.

Tactic Notation "prove_type_sys_props" ident(c) :=
  unfold type_sys_props;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_symmetric"
  | Case_aux c "type_transitive"
  | Case_aux c "type_stransitive"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  | Case_aux c "type_gsymmetric"
  | Case_aux c "type_gtransitive"
  | Case_aux c "type_mtransitive"
  ].

Definition type_sys_props2 {p}
           (lib : library)
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  (* uniquely valued *)
  (forall T3 eq',
     (ts T1 T3 eq' [+] ts T2 T3 eq')
     -> eq_term_equals eq eq')
    # (* type_extensionality *)
    (forall T T3 eq',
       (T = T1 [+] T = T2)
       -> ts T T3 eq
       -> eq_term_equals eq eq'
       -> ts T T3 eq')
    # (* type value respecting *)
    (forall T T3, (T = T1 [+] T = T2) -> cequivc lib T T3 -> ts T T3 eq)
    # (* term symmetric *)
    term_equality_symmetric eq
    # (* term transitivive (1) *)
    term_equality_transitive eq
    # (* term value respecting *)
    term_equality_respecting lib eq
    # (* type symmetric *)
    (forall T T3 eq', (T = T1 [+] T = T2) -> (ts T T3 eq' <=> ts T3 T eq'))
    # (* type transitive (3) *)
    ts T1 T2 eq
    (*(forall T T3 T4 eq1 eq2,
       (T = T1 [+] T = T2)
       -> ts T T3 eq1
       -> ts T3 T4 eq2
       -> ts T T4 eq1 # ts T T4 eq2)*)
    # (* type transitive (4) *)
    (forall T T3 T4 eq1 eq2,
       (T = T1 [+] T = T2)
       -> ts T3 T eq1
       -> ts T T4 eq2
       -> ts T3 T4 eq1 # ts T3 T4 eq2 # ts T T3 eq1).

Definition type_sys2 {p} lib (ts : ects(p)) :=
  forall T1 T2 eq,
    ts T1 T2 eq -> type_sys_props2 lib ts T1 T2 eq.

(** Destruct type_sys_props2 *)
Ltac dest_tsp2 c uv tys tyvr tes tet tevr tygs tygt tymt :=
  let tmp := fresh "tmp" in
    unfold type_sys_props2 in c;
  destruct c   as [ uv   tmp ];
  destruct tmp as [ tys  tmp ];
  destruct tmp as [ tyvr tmp ];
  destruct tmp as [ tes  tmp ];
  destruct tmp as [ tet  tmp ];
  destruct tmp as [ tevr tmp ];
  destruct tmp as [ tygs tmp ];
  destruct tmp as [ tygt tymt ].

Ltac onedtsp2 uv tys tyvr tes tet tevr tygs tygt tymt :=
  match goal with
      [ H : type_sys_props2 _ _ _ _ _ |- _ ] =>
      dest_tsp2 H uv tys tyvr tes tet tevr tygs tygt tymt
  end.

Tactic Notation "prove_type_sys_props2" ident(c) :=
  unfold type_sys_props2;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_symmetric"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  | Case_aux c "type_gsymmetric"
  | Case_aux c "type_gtransitive"
  | Case_aux c "type_mtransitive"
  ].

Lemma type_sys_props_iff_type_sys_props2 {p} :
  forall lib (ts : ects(p)) T1 T2 eq,
    type_sys_props lib ts T1 T2 eq <=> type_sys_props2 lib ts T1 T2 eq.
Proof.
  introv; split; intro tsp.

  - onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    prove_type_sys_props2 Case; sp.

  - onedtsp2 uv tys tyvr tes tet tevr tygs tygt tymt.
    prove_type_sys_props Case; try (complete sp).

    + Case "type_transitive".
      introv e.
      generalize (tymt T2 T1 T3 eq eq'); sp.
      generalize (tymt T2 T3 T3 eq' eq'); intro k.
      repeat (dest_imp k hyp).
      generalize (tygs T2 T3 eq'); intro j; dest_imp j hyp.
      apply j; sp.

    + Case "type_stransitive".
      introv e.
      generalize (tymt T1 T2 T3 eq eq'); intro k;
      repeat (dest_imp k hyp); try (complete (apply tygs; sp)); repnd.
      dands; auto.
      generalize (tymt T1 T3 T3 eq' eq'); intro j.
      repeat (dest_imp j hyp).
      generalize (tygs T1 T3 eq'); intro l; dest_imp l hyp.
      apply l; sp.
Qed.

Lemma type_sys_iff_type_sys2 {p} :
  forall lib (ts : ects(p)), type_sys lib ts <=> type_sys2 lib ts.
Proof.
  introv; unfold type_sys, type_sys2; split; intro k; introv e;
  try (complete (apply type_sys_props_iff_type_sys_props2; sp)).
Qed.



Definition type_sys_props3 {p}
           (lib : library)
           (ts : ects(p))
           (T1 T2 : CTerm)
           (eq : per) :=
  (* uniquely valued *)
  (forall T3 eq', ts T1 T3 eq' -> eq_term_equals eq eq')
    # (* type_extensionality *)
    (forall T3 eq', ts T1 T3 eq -> eq_term_equals eq eq' -> ts T1 T3 eq')
    # (* type value respecting *)
    (forall T T3, (T = T1 [+] T = T2) -> cequivc lib T T3 -> ts T T3 eq)
    # (* term symmetric *)
    term_equality_symmetric eq
    # (* term transitivive (1) *)
    term_equality_transitive eq
    # (* term value respecting *)
    term_equality_respecting lib eq
    # (* type symmetric *)
    (forall T3 eq', ts T1 T3 eq' <=> ts T3 T1 eq')
    # (* type transitive (3) *)
    ts T1 T2 eq
    # (* type transitive (4) *)
    (forall T T3 T4 eq1 eq2,
       (T = T1 [+] T = T2)
       -> ts T3 T eq1
       -> ts T T4 eq2
       -> ts T3 T4 eq1 # ts T3 T4 eq2).

Definition type_sys3 {p} lib (ts : ects(p)) :=
  forall T1 T2 eq,
    ts T1 T2 eq -> type_sys_props3 lib ts T1 T2 eq.

(** Destruct type_sys_props3 *)
Ltac dest_tsp3 c uv tys tyvr tes tet tevr tygs tygt tymt :=
  let tmp := fresh "tmp" in
    unfold type_sys_props3 in c;
  destruct c   as [ uv   tmp ];
  destruct tmp as [ tys  tmp ];
  destruct tmp as [ tyvr tmp ];
  destruct tmp as [ tes  tmp ];
  destruct tmp as [ tet  tmp ];
  destruct tmp as [ tevr tmp ];
  destruct tmp as [ tygs tmp ];
  destruct tmp as [ tygt tymt ].

Ltac onedtsp3 uv tys tyvr tes tet tevr tygs tygt tymt :=
  match goal with
      [ H : type_sys_props3 _ _ _ _ _ |- _ ] =>
      dest_tsp3 H uv tys tyvr tes tet tevr tygs tygt tymt
  end.

Tactic Notation "prove_type_sys_props3" ident(c) :=
  unfold type_sys_props3;
  dands;
  [ Case_aux c "uniquely_valued"
  | Case_aux c "type_symmetric"
  | Case_aux c "type_value_respecting"
  | Case_aux c "term_symmetric"
  | Case_aux c "term_transitive"
  | Case_aux c "term_value_respecting"
  | Case_aux c "type_gsymmetric"
  | Case_aux c "type_gtransitive"
  | Case_aux c "type_mtransitive"
  ].

Lemma type_sys_props_iff_type_sys_props3 {p} :
  forall lib (ts : ects(p)) T1 T2 eq,
    type_sys_props lib ts T1 T2 eq <=> type_sys_props3 lib ts T1 T2 eq.
Proof.
  introv.
  rw @type_sys_props_iff_type_sys_props2.
  split; intro tsp.

  - onedtsp2 uv tys tyvr tes tet tevr tygs tygt tymt.
    prove_type_sys_props3 Case; sp.

    + Case "uniquely_valued".
      generalize (uv T3 eq'); sp.

    + Case "type_mtransitive".
      subst; generalize (tymt T1 T3 T4 eq1 eq2); sp.

    + Case "type_mtransitive".
      subst; generalize (tymt T2 T3 T4 eq1 eq2); sp.

    + Case "type_mtransitive".
      subst; generalize (tymt T1 T3 T4 eq1 eq2); sp.

    + Case "type_mtransitive".
      subst; generalize (tymt T2 T3 T4 eq1 eq2); sp.

  - onedtsp3 uv tys tyvr tes tet tevr tygs tygt tymt.
    prove_type_sys_props2 Case; try (complete sp).

    + Case "uniquely_valued".
      introv o; destruct o as [o | o].
      generalize (uv T3 eq'); auto.
      generalize (tymt T2 T1 T3 eq eq'); intro k.
      repeat (autodimp k hyp); repnd.
      generalize (uv T3 eq'); auto.

    + Case "type_symmetric".
      introv o ets eqs; destruct o as [o | o]; subst; auto.
      generalize (tymt T2 T1 T3 eq eq); intro k.
      repeat (autodimp k hyp); repnd.
      generalize (tys T3 eq'); intro j; repeat (autodimp j hyp).
      apply tygs in tygt.
      generalize (tymt T1 T2 T3 eq eq'); intro l; repeat (autodimp l hyp); repnd; auto.

    + Case "type_gsymmetric".
      introv o; destruct o as [o | o]; subst; auto.
      split; intro k.

      generalize (tymt T2 T1 T3 eq eq'); intro j; repeat (autodimp j hyp); repnd; auto.
      rw tygs in j.
      generalize (tymt T1 T3 T2 eq' eq); intro l; repeat (autodimp l hyp); repnd; auto.

      applydup tygs in tygt.
      generalize (tymt T2 T3 T1 eq' eq); intro j; repeat (autodimp j hyp); repnd; auto.
      apply tygs in j0.
      apply tygs in tygt.
      generalize (tymt T1 T2 T3 eq eq'); intro l; repeat (autodimp l hyp); repnd; auto.

    + Case "type_mtransitive".
      introv o e1 e2.
      generalize (tymt T T3 T4 eq1 eq2 o e1 e2); intro e3; repnd.
      dands; auto.
      destruct o as [o | o]; subst.

      apply tygs; auto.

      applydup tygs in tygt.
      generalize (tymt T2 T3 T1 eq1 eq); intro k; repeat (autodimp k hyp); repnd.
      apply tygs in k0.
      generalize (tymt T1 T2 T3 eq eq1); intro l; repeat (autodimp l hyp); repnd; auto.
Qed.

Lemma type_sys_iff_type_sys3 {p} :
  forall lib (ts : ects(p)), type_sys lib ts <=> type_sys3 lib ts.
Proof.
  introv; unfold type_sys, type_sys3; split; intro k; introv e;
  try (complete (apply type_sys_props_iff_type_sys_props3; sp)).
Qed.
*)

Ltac implies_ts_or T H :=
  match type of H with
    | ?ts ?T1 ?T2 ?eq =>
      let name := fresh "or" in
      (assert (ts T1 T2 eq [+] ts T T2 eq) as name by (left; auto);
       clear H;
       rename name into H)
  end.

Ltac rev_implies_ts_or T H :=
  match type of H with
    | ?ts ?T1 ?T2 ?eq =>
      let name := fresh "or" in
      (assert (ts T T2 eq [+] ts T1 T2 eq) as name by (right; auto);
       clear H;
       rename name into H)
  end.

(*
Lemma type_sys_props_ts_refl {p} :
  forall lib (ts : ects(p)) A B eq,
    type_sys_props lib ts A B eq
    -> ts A A eq # ts B B eq.
Proof.
  introv tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq); intro k; repeat (dest_imp k h).
Qed.

Lemma type_sys_props_ts_refl2 {p} :
  forall lib (ts : ects(p)) A B eq1 eq2,
    type_sys_props lib ts A B eq1
    -> eq_term_equals eq1 eq2
    -> ts A A eq2 # ts B B eq2.
Proof.
  introv tsp eqt.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq2); intro k; repeat (dest_imp k h).
Qed.

Lemma type_sys_props_ts_uv {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts A B eq1
    -> type_sys_props lib ts B C eq2
    -> ts A B eq2.
Proof.
  introv tsab tsp.
  applydup @type_sys_props_ts_refl in tsp; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs B A eq1); intro i; dest_imp i h.
  duplicate tsab as j.
  rw <- i in j.
  generalize (uv A eq1); intro k; dest_imp k h.
  generalize (tyst A eq1); intro l; dest_imp l h; repnd.
  generalize (tyt A eq1); intro u; dest_imp u h; repnd.
  generalize (tygs B A eq2); intro v; dest_imp v h.
  rw v in u0; sp.
Qed.

Lemma type_sys_props_ts_uv2 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts B A eq1
    -> type_sys_props lib ts B C eq2
    -> ts B A eq2.
Proof.
  introv tsab tsp.
  applydup @type_sys_props_ts_refl in tsp; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (uv A eq1); intro k; dest_imp k h.
  generalize (tyst A eq1); intro l; dest_imp l h; repnd.
  generalize (tyt A eq1); intro u; dest_imp u h; repnd.
Qed.

Lemma type_sys_props_ts_uv3 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2 eq3,
    ts A B eq1
    -> type_sys_props lib ts A C eq2
    -> eq_term_equals eq2 eq3
    -> ts A B eq3.
Proof.
  introv tsab tsp eqt.
  applydup @type_sys_props_ts_refl in tsp; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tyst B eq1); intro l; dest_imp l h; repnd.
  generalize (tyt B eq1); intro u; dest_imp u h; repnd.
Qed.

Lemma type_sys_props_ts_uv4 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2 eq3,
    ts A B eq1
    -> type_sys_props lib ts B C eq2
    -> eq_term_equals eq2 eq3
    -> ts A B eq3.
Proof.
  introv tsab tsp eqt.
  applydup @type_sys_props_ts_refl in tsp; repnd.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs B A eq1); intro i; dest_imp i h.
  rw <- i in tsab.
  generalize (tyst A eq1); intro j; dest_imp j h; repnd.
  generalize (tyt A eq2); intro k; dest_imp k h; repnd.
  generalize (tys B A eq3); intro l; repeat (dest_imp l h).
  generalize (tygs B A eq3); intro u; dest_imp u h.
  rw u in l; sp.
Qed.

Lemma type_sys_props_ts_sym {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts A C eq1
    -> ts B A eq2
    -> ts A B eq1.
Proof.
  introv tsp tsa.
  assert (ts B A eq1) by (apply (type_sys_props_ts_uv lib) with (C := C) (eq1 := eq2); sp).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq1); intro i; dest_imp i h.
  rw i; sp.
Qed.

Lemma type_sys_props_ts_sym2 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts A C eq1
    -> ts B A eq2
    -> ts A B eq2.
Proof.
  introv tsp tsa.
  assert (ts B A eq1) by (apply (type_sys_props_ts_uv lib) with (C := C) (eq1 := eq2); sp).
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq2); intro j; dest_imp j h.
  rw <- j in tsa; sp.
Qed.

Lemma type_sys_props_ts_sym3 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts A C eq1
    -> ts A B eq2
    -> ts B A eq2.
Proof.
  introv tsp tsa.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq2); intro j; dest_imp j h.
  rw <- j; sp.
Qed.

Lemma type_sys_props_ts_sym4 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts A C eq1
    -> ts A B eq2
    -> ts B A eq1.
Proof.
  introv tsp tsa.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq1); intro j; dest_imp j h.
  apply j.
  generalize (tyst B eq2 tsa); intro k; repnd.
  generalize (tymt C A B eq1 eq1); sp.
Qed.

Lemma type_sys_props_ts_sym5 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts C A eq1
    -> ts A B eq2
    -> ts B A eq1.
Proof.
  introv tsp tsa.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq1); intro j; dest_imp j h.
  apply j.
  generalize (tyt B eq2 tsa); intro k; repnd.
  apply tygs in tygt; sp.
  generalize (tymt C A B eq1 eq1); sp.
Qed.

Lemma type_sys_props_ts_sym6 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    type_sys_props lib ts C A eq1
    -> ts A B eq2
    -> ts B A eq2.
Proof.
  introv tsp tsa.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs A B eq2); intro j; dest_imp j h.
  apply j; auto.
Qed.

Lemma type_sys_props_ts_trans {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2 eq,
    ts A B eq1
    -> ts B C eq2
    -> type_sys_props lib ts A B eq
    -> ts A C eq.
Proof.
  introv ts1 ts2 tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tyt C eq2); sp.
Qed.

Lemma type_sys_props_eq_term_equals {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts A B eq1
    -> type_sys_props lib ts B C eq2
    -> eq_term_equals eq2 eq1.
Proof.
  introv tsa tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs B A eq1); intro i; dest_imp i h.
  rw <- i in tsa.
  generalize (uv A eq1); sp.
Qed.

Lemma type_sys_props_eq_term_equals2 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts A B eq1
    -> type_sys_props lib ts C B eq2
    -> eq_term_equals eq2 eq1.
Proof.
  introv tsa tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (tygs B A eq1); intro i; dest_imp i h.
  rw <- i in tsa.
  generalize (uv A eq1); sp.
Qed.

Lemma type_sys_props_eq_term_equals3 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts B A eq1
    -> type_sys_props lib ts C B eq2
    -> eq_term_equals eq2 eq1.
Proof.
  introv tsa tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (uv A eq1); sp.
Qed.

Lemma type_sys_props_eq_term_equals4 {p} :
  forall lib (ts : ects(p)) A B C eq1 eq2,
    ts A B eq1
    -> type_sys_props lib ts A C eq2
    -> eq_term_equals eq2 eq1.
Proof.
  introv tsa tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  generalize (uv B eq1); sp.
Qed.

(*    apply tys in X; sp.
    apply tys in X; sp.*)

Lemma type_sys_props_sym {p} :
  forall lib (ts : ects(p)) A B eq,
    type_sys_props lib ts A B eq
    -> type_sys_props lib ts B A eq.
Proof.
  introv tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  prove_type_sys_props Case.

  - Case "uniquely_valued"; sp.
    rev_implies_ts_or A t.
    apply uv in t; auto.
    implies_ts_or B t.
    apply uv in t; auto.

  - Case "type_symmetric"; sp.

  - Case "type_transitive"; sp.

  - Case "type_stransitive"; sp.

  - Case "type_value_respecting"; sp.

  - Case "term_symmetric"; sp.

  - Case "term_transitive"; sp.

  - Case "term_value_respecting"; sp.

  - Case "type_gsymmetric"; sp.

(*  - Case "type_gtransitive"; sp; subst; sp.
    generalize (tygt B T3 T4 eq1 eq2); sp.
    generalize (tygt A T3 T4 eq1 eq2); sp.
    generalize (tygt B T3 T4 eq1 eq2); sp.
    generalize (tygt A T3 T4 eq1 eq2); sp.*)

  - Case "type_gtransitive"; sp.
    generalize (tygs A B eq); intro i; dest_imp i h.
    rw <- i; sp.

  - Case "type_mtransitive"; sp; subst; sp.
    generalize (tymt B T3 T4 eq1 eq2); sp.
    generalize (tymt A T3 T4 eq1 eq2); sp.
    generalize (tymt B T3 T4 eq1 eq2); sp.
    generalize (tymt A T3 T4 eq1 eq2); sp.

    generalize (tygs B T3 eq1); intro i; dest_imp i h.
    rw i; sp.

    generalize (tygs A T3 eq1); intro i; dest_imp i h.
    rw i; sp.
Qed.

Lemma type_system_type_symm {p} :
 forall (ts : ects(p)) T T' eq,
   type_symmetric ts
   -> ts T T' eq
   -> ts T' T eq.
Proof.
  sp.
Qed.
*)

Ltac use_trans_tac x :=
  match goal with
    | [ H : etype_transitive _ |- _ ] => apply H with (T2 := x)
  end.

Ltac use_trans_tac_in x h :=
  match goal with
    | [ H : etype_transitive _ |- _ ] => apply H with (T2 := x) in h
  end.

Tactic Notation "use_trans" constr(x) "in" ident(H) := use_trans_tac_in x H.
Tactic Notation "use_trans" constr(x) := use_trans_tac x.

Ltac use_ext_tac x :=
  match goal with
    | [ H : etype_extensionality _ |- _ ] => apply H with (eq := x)
  end.

Ltac use_ext_tac_in x h :=
  match goal with
    | [ H : etype_extensionality _ |- _ ] => apply H with (eq := x) in h
  end.

Tactic Notation "use_ext" constr(x) "in" ident(H) := use_ext_tac_in x H.
Tactic Notation "use_ext" constr(x) := use_ext_tac x.

Ltac use_sym_tac :=
  match goal with
    | [ H : etype_symmetric _ |- _ ] => apply H
  end.

Ltac use_sym_tac_in h :=
  match goal with
    | [ H : etype_symmetric _ |- _ ] => apply H in h
  end.

Tactic Notation "use_sym" "in" ident(H) := use_sym_tac_in H.
Tactic Notation "use_sym" := use_sym_tac.

Ltac use_vresp_tac :=
  match goal with
    | [ H : etype_value_respecting _ _ |- _ ] => apply H
  end.

Ltac use_vresp_tac_in h :=
  match goal with
    | [ H : etype_value_respecting _ _ |- _ ] => apply H in h
  end.

Tactic Notation "use_vresp" "in" ident(H) := use_vresp_tac_in H.
Tactic Notation "use_vresp" := use_vresp_tac.

Ltac ren_vresp h :=
  match goal with
    | [ H : etype_value_respecting _ _ |- _ ] => rename H into h
  end.

(*
Ltac use_tvresp_tac x :=
  match goal with
    | [ H : term_value_respecting _ _ |- _ ] => apply H with (T := x)
  end.

Ltac use_tvresp_tac_in x h :=
  match goal with
    | [ H : term_value_respecting _ _ |- _ ] => apply H with (T := x) in h
  end.

Tactic Notation "use_tvresp" constr(x) "in" ident(H) := use_tvresp_tac_in x H.
Tactic Notation "use_tvresp" constr(x) := use_tvresp_tac x.

Ltac use_uval_tac T T' :=
  match goal with
    | [ H : uniquely_valued _ |- _ ] => apply H with (T := T) (T' := T')
  end.

Ltac use_uval_tac_in T T' h :=
  match goal with
    | [ H : uniquely_valued _ |- _ ] => apply H with (T := T) (T' := T') in h
  end.

Tactic Notation "use_uval" constr(T) constr(U) "in" ident(H) :=
       use_uval_tac_in T U H.
Tactic Notation "use_uval" constr(T) constr(U) :=
       use_uval_tac T U.
*)

Lemma etype_system_ts_refl {p} :
  forall lib (ts : ects(p)) A B eq,
    etype_system lib ts
    -> ts A B eq
    -> ts A A eq # ts B B eq.
Proof.
  introv tysys tsab.
  allunfold @etype_system; sp.
  - use_trans B; sp.
  - use_trans A; sp.
Qed.

Lemma etype_system_type_mem {p} :
 forall (ts : ects(p)) (T T' : CTerm) (eq : per),
   etype_symmetric ts
   -> etype_transitive ts
   -> ts T T' eq
   -> ts T T eq.
Proof.
  sp.
  use_trans T'; auto.
Qed.

Lemma etype_system_type_mem1 {p} :
 forall (ts : ects(p)) (T T' : CTerm) (eq : per),
   etype_symmetric ts
   -> etype_transitive ts
   -> ts T T' eq
   -> ts T' T' eq.
Proof.
  sp.
  use_trans T; auto.
Qed.

Lemma etype_system_type_mem2 {p} :
 forall (ts : ects(p)) (T T' : CTerm) (eq : per),
   etype_symmetric ts
   -> etype_transitive ts
   -> ts T T' eq
   -> ts T T eq # ts T' T' eq.
Proof.
  sp.
  - use_trans T'; auto.
  - use_trans T; auto.
Qed.

(*
Check ex_intro.

Definition ex_proj (A : Prop) P (ex : exists (x : A), P x) : A :=
  match ex return A with
      @ex_intro x _ => x
  end.
*)

Lemma euniquely_valued_eq {p} :
  forall (ts : ects(p)) (T T1 T2 : CTerm) (eq1 eq2 : per),
    euniquely_valued ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T T1 eq1
    -> ts T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
 introv uv tys tyt t1 t2.
 assert (ts T T eq1) by (apply etype_system_type_mem with (T' := T1); auto).
 assert (ts T T eq2) by (apply etype_system_type_mem with (T' := T2); auto).
 apply uv with (T := T) (T' := T); auto.
Qed.

Lemma euniquely_valued_eq_ts {p} :
  forall lib (ts : ects(p)) (T T1 T2 : CTerm) (eq1 eq2 : per),
    etype_system lib ts
    -> ts T T1 eq1
    -> ts T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
  intros.
  allunfold @etype_system; sp.
  apply @euniquely_valued_eq with (ts := ts) (T := T) (T1 := T1) (T2 := T2); sp.
Qed.

Lemma uniquely_valued_eq_ts {p} :
  forall lib (ts : cts(p)) (T : CTerm) (eq1 eq2 : per),
    type_system lib ts
    -> ts T eq1
    -> ts T eq2
    -> eq1 <=2=> eq2.
Proof.
  introv h ts1 ts2.
  onedts uv tye tyvr tes tet tevr.
  eapply uv; eauto.
Qed.

Lemma euniquely_valued_eq2 {p} :
  forall (ts : ects(p)) (T T1 T2 : CTerm) (eq1 eq2 : per),
    euniquely_valued ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T eq1
    -> ts T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
 introv uv tys tyt t1 t2.
 assert (ts T T eq1) by (apply etype_system_type_mem with (T' := T1); auto).
 assert (ts T T eq2) by (apply etype_system_type_mem with (T' := T2); auto).
 apply uv with (T := T) (T' := T); auto.
Qed.

Lemma euniquely_valued_eq2_ts {p} :
  forall lib (ts : ects(p)) (T T1 T2 : CTerm) (eq1 eq2 : per),
    etype_system lib ts
    -> ts T1 T eq1
    -> ts T T2 eq2
    -> eq_term_equals eq1 eq2.
Proof.
  intros.
  allunfold @etype_system; sp.
  apply @euniquely_valued_eq2 with (ts := ts) (T := T) (T1 := T1) (T2 := T2); sp.
Qed.

Lemma euniquely_valued_trans {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T1 T2 eq2.
Proof.
  sp.
  assert (ts T2 T1 eq1) by (use_sym; auto).
  assert (eq_term_equals eq1 eq2) as eq.
  apply @euniquely_valued_eq with (ts := ts) (T := T2) (T1 := T1) (T2 := T3); auto.
  use_ext eq1; auto.
Qed.

Lemma euniquely_valued_trans2 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T1 T3 eq1.
Proof.
  introv uv tye tys tyt t1 t2.
  assert (ts T1 T2 eq2)
    by (apply @euniquely_valued_trans with (T3 := T3) (eq1 := eq1); auto).
  assert (ts T1 T3 eq2) by (use_trans T2; auto).
  assert (eq_term_equals eq2 eq1) by (apply uv with (T := T1) (T' := T2); auto).
  use_ext eq2; auto.
Qed.

Lemma euniquely_valued_trans2_r {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T3 T3 eq1.
Proof.
  sp.
  generalize (euniquely_valued_trans2 ts T1 T2 T3 eq1 eq2); sp.
  use_trans T1; sp.
Qed.

Lemma euniquely_valued_trans3 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T2 T3 eq1.
Proof.
  introv uv tye tys tyt t1 t2.
  assert (ts T1 T3 eq1)
    by (apply @euniquely_valued_trans2 with (T2 := T2) (eq2 := eq2); auto).
  assert (ts T2 T1 eq1) by sp.
  use_trans T1; auto.
Qed.

Lemma euniquely_valued_trans4 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T1 T3 eq2.
Proof.
  sp.
  assert (ts T1 T2 eq2).
  apply @euniquely_valued_trans with (T3 := T3) (eq1 := eq1); auto.
  use_trans T2; auto.
Qed.

Lemma euniquely_valued_trans4_r {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T2 T3 eq2
    -> ts T3 T3 eq2.
Proof.
  sp.
  generalize (euniquely_valued_trans4 ts T1 T2 T3 eq1 eq2); sp.
  use_trans T1; sp.
Qed.

Lemma euniquely_valued_trans5 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T1 T3 eq1.
Proof.
  sp.
  assert (ts T2 T1 eq1) by (use_sym; auto).
  apply @euniquely_valued_trans3 with (T1 := T2) (eq2 := eq2); auto.
Qed.

Lemma euniquely_valued_trans6 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T1 T2 eq2.
Proof.
  sp.
  assert (eq_term_equals eq1 eq2).
  apply @euniquely_valued_eq with (ts := ts) (T := T1) (T1 := T2) (T2 := T3); auto.
  use_ext eq1; auto.
Qed.

Lemma euniquely_valued_trans7 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T2 T3 eq1.
Proof.
  sp.
  assert (ts T2 T1 eq1) by (use_sym; auto).
  apply @euniquely_valued_trans2 with (T2 := T1) (eq2 := eq2); auto.
Qed.

Lemma euniquely_valued_trans7_r {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T3 T3 eq1.
Proof.
  sp.
  generalize (euniquely_valued_trans7 ts T1 T2 T3 eq1 eq2); sp.
  use_trans T2; sp.
Qed.

Lemma euniquely_valued_trans8 {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T2 T3 eq2.
Proof.
  sp.
  assert (ts T2 T1 eq1) by (use_sym; auto).
  apply @euniquely_valued_trans4 with (T2 := T1) (eq1 := eq1); auto.
Qed.

Lemma euniquely_valued_trans8_r {p} :
  forall ts : ects(p),
  forall T1 T2 T3 : CTerm,
  forall eq1 eq2 : per,
    euniquely_valued ts
    -> etype_extensionality ts
    -> etype_symmetric ts
    -> etype_transitive ts
    -> ts T1 T2 eq1
    -> ts T1 T3 eq2
    -> ts T3 T3 eq2.
Proof.
  sp.
  generalize (euniquely_valued_trans8 ts T1 T2 T3 eq1 eq2); sp.
  use_trans T2; sp.
Qed.

Lemma term_equality_refl {p} :
 forall t1 t2 : @CTerm p,
 forall eq : per,
   term_equality_symmetric eq
   -> term_equality_transitive eq
   -> eq t1 t2
   -> eq t1 t1.
Proof.
 introv tes tet e.
  apply tet with (t2 := t2); auto.
Qed.

Lemma term_equality_sym {p} :
 forall t1 t2 : @CTerm p,
 forall eq : per,
   term_equality_symmetric eq
   -> eq t1 t2
   -> eq t2 t1.
Proof.
  sp.
Qed.

Lemma type_system_term_mem {p} :
 forall (ts : cts(p)) (T t1 t2 : CTerm) (eq : per),
   term_symmetric ts
   -> term_transitive ts
   -> ts T eq
   -> eq t1 t2
   -> eq t1 t1.
Proof.
  introv tes tet e.
  apply @term_equality_refl with (t2 := t2); auto.
  - eapply tes; eauto.
  - eapply tet; eauto.
Qed.

Lemma etype_system_term_mem {p} :
 forall ts : ects(p),
 forall T T' t1 t2 : CTerm,
 forall eq : per,
   eterm_symmetric ts
   -> eterm_transitive ts
   -> ts T T' eq
   -> eq t1 t2
   -> eq t1 t1.
Proof.
  introv tes tet e.
  apply @term_equality_refl with (t2 := t2); auto.
  apply tes with (T := T) (T' := T'); auto.
  apply tet with (T := T) (T' := T'); auto.
Qed.

Lemma etype_extensionality_symm {p} :
  forall ts : ects(p),
  forall T1 T2 : CTerm,
  forall eq eq' : per,
    etype_symmetric ts
    -> etype_extensionality ts
    -> ts T1 T2 eq
    -> eq_term_equals eq eq'
    -> ts T2 T1 eq'.
Proof.
  intros.
  use_sym.
  use_ext eq; auto.
Qed.

Lemma etype_reduces_to_symm {p} :
  forall lib (ts : ects(p)) (T1 T2 T3 : CTerm) (eq : per),
   etype_symmetric ts
   -> etype_transitive ts
   -> etype_value_respecting lib ts
   -> ts T1 T2 eq
   -> cequivc lib T1 T3
   -> ts T1 T3 eq.
Proof.
  intros.
  ren_vresp h; apply h; auto.
  apply etype_system_type_mem with (T' := T2); auto.
Qed.

Lemma etype_reduces_to_symm2 {p} :
  forall lib (ts : ects(p)) (T1 T2 T3 : CTerm) (eq : per),
   etype_symmetric ts
   -> etype_transitive ts
   -> etype_value_respecting lib ts
   -> ts T2 T1 eq
   -> cequivc lib T1 T3
   -> ts T1 T3 eq.
Proof.
  sp; generalize (etype_reduces_to_symm lib ts T1 T2 T3 eq); sp.
Qed.

(*
Lemma term_reduces_to_symm {p} :
  forall lib (ts : ects(p)) (T1 T2 : CTerm) (eq : per),
   type_symmetric ts
   -> type_transitive ts
   -> term_value_respecting lib ts
   -> ts T1 T2 eq
   -> term_equality_respecting lib eq.
Proof.
  intros.
  use_tvresp T1.
  apply type_system_type_mem with (T' := T2); auto.
Qed.

Lemma type_system_prop {p} :
  forall lib (ts : ects(p)),
    type_system lib ts <=> type_sys lib ts.
Proof.
  introv; split_iff Case.
  - Case "->".
    unfold type_sys; sp; try (onedts uv tye tys tyt tyvr tes tet tevr);
    prove_type_sys_props SCase.
    + SCase "uniquely_valued"; sp.
      apply @uniquely_valued_eq with (ts := ts) (T := T1) (T1 := T2) (T2 := T3); auto.
      apply @uniquely_valued_eq2 with (ts := ts) (T := T2) (T1 := T1) (T2 := T3); auto.
    + SCase "type_symmetric"; sp.
      use_ext eq; auto.
      use_ext eq; auto.
    + SCase "type_transitive"; sp.
      apply @uniquely_valued_trans2 with (T2 := T2) (eq2 := eq'); auto.
      apply @uniquely_valued_trans4 with (T2 := T2) (eq1 := eq); auto.
      apply @uniquely_valued_trans2 with (T2 := T2) (eq2 := eq'); auto.
    + SCase "type_stransitive"; sp.
      apply @uniquely_valued_trans7 with (T1 := T1) (eq2 := eq'); auto.
      apply @uniquely_valued_trans8 with (T1 := T1) (eq1 := eq); auto.
      apply @uniquely_valued_trans7 with (T1 := T1) (eq2 := eq'); auto.
    + SCase "type_value_respecting"; sp; subst; sp.
      apply (type_reduces_to_symm lib) with (T2 := T2); auto.
      apply (type_reduces_to_symm lib) with (T2 := T1); auto.
    + SCase "term_symmetric"; sp.
      apply tes with (T := T1) (T' := T2); auto.
    + SCase "term_transitive"; sp.
      apply tet with (T := T1) (T' := T2); auto.
    + SCase "term_value_respecting"; sp.
      apply @term_reduces_to_symm with (ts := ts) (T1 := T1) (T2 := T2); auto.
    + SCase "type_gsymmetric"; sp.
    + SCase "type_gtransitive"; sp.


    + SCase "type_mtransitive"; sp; subst; sp.
      apply @uniquely_valued_trans2 with (T2 := T1) (eq2 := eq2); auto.
      apply @uniquely_valued_trans2 with (T2 := T2) (eq2 := eq2); auto.
      apply @uniquely_valued_trans4 with (T2 := T1) (eq1 := eq1); auto.
(*    + SCase "type_gtransitive"; sp; subst; sp.
      apply uniquely_valued_trans2 with (T2 := T3) (eq2 := eq2); auto.
      apply uniquely_valued_trans2 with (T2 := T3) (eq2 := eq2); auto.
      apply uniquely_valued_trans4 with (T2 := T3) (eq1 := eq1); auto.
      apply uniquely_valued_trans4 with (T2 := T3) (eq1 := eq1); auto.*)

(*    + SCase "type_mtransitive"; sp.*)
      apply @uniquely_valued_trans4 with (T2 := T2) (eq1 := eq1); auto.

  - Case "<-".
    unfold type_sys; sp; prove_type_system SCase.
    + SCase "uniquely_valued".
      unfold uniquely_valued; sp.
      discover.
      apply h0 with (T3 := T'); auto.
    + SCase "type_extensionality".
      unfold type_extensionality; sp.
      discover.
      d_tsp.
      apply tsp_tys; auto.
    + SCase "type_symmetric".
      unfold type_symmetric; sp.
      discover.
      d_tsp.
      generalize (tsp_tygs T T' eq); intro i; dest_imp i h.
      rw <- i; sp.
    + SCase "type_transitive".
      unfold type_transitive; sp.
      discover.
      d_tsp.
      generalize (tsp_tyt T3 eq); sp.
    + SCase "type_value_respecting"; sp.
      unfold type_value_respecting; sp.
      discover.
      d_tsp; sp.
    + SCase "term_symmetric"; sp.
      unfold term_symmetric; sp.
      discover.
      d_tsp; sp.
    + SCase "term_transitive"; sp.
      unfold term_transitive; sp.
      discover.
      d_tsp; sp.
    + SCase "term_value_respecting"; sp.
      unfold term_value_respecting; sp.
      discover.
      d_tsp; sp.
Qed.
*)

(*
Lemma eqorceq_implies_eq {p} :
  forall lib eq (a b c : @CTerm p),
    term_equality_respecting lib eq
    -> term_equality_symmetric eq
    -> term_equality_transitive eq
    -> eqorceq lib eq a b
    -> eq a c
    -> eq a b.
Proof.
  introv ter tes tet.
  unfold eqorceq; sp.
  unfold term_equality_respecting in ter.
  apply ter; auto.
  apply term_equality_refl with (t2 := c); auto.
Qed.

Lemma eqorceq_implies_eq2 {p} :
  forall lib eq (a b c : @CTerm p),
    term_equality_respecting lib eq
    -> term_equality_symmetric eq
    -> term_equality_transitive eq
    -> eqorceq lib eq a b
    -> eq c b
    -> eq a b.
Proof.
  unfold eqorceq; introv ter tes tet eo e; sp.
  apply tes.
  apply ter; auto.
  apply tes in e.
  apply term_equality_refl with (t2 := c); auto.
  spcast; apply cequivc_sym; auto.
Qed.

Lemma eqorceq_sym {p} :
  forall lib eq (a b : @CTerm p),
    term_equality_symmetric eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq b a.
Proof.
  unfold eqorceq; sp.
  right; spcast; apply cequivc_sym; auto.
Qed.

Lemma eqorceq_trans {p} :
  forall lib eq (a b c : @CTerm p),
    term_equality_symmetric eq
    -> term_equality_transitive eq
    -> term_equality_respecting lib eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq b c
    -> eqorceq lib eq a c.
Proof.
  unfold eqorceq; intros lib eq a b v tes tet ter e1 e2; sp.
  left; apply tet with (t2 := b); auto.
  left; apply tet with (t2 := b); auto.
  apply tes; apply ter.
  apply term_equality_refl with (t2 := v); auto.
  spcast; apply cequivc_sym; auto.
  left; apply tet with (t2 := b); auto.
  apply ter; auto.
  apply term_equality_refl with (t2 := a); auto.
  right; spcast; apply @cequivc_trans with (b := b); auto.
Qed.

Lemma eqorceq_eq_term_equals {p} :
  forall lib (eq1 eq2 : per(p)),
    eq_term_equals eq1 eq2
    -> forall a b, (eqorceq lib eq1 a b <=> eqorceq lib eq2 a b).
Proof.
  unfold eqorceq, eq_term_equals; sp; split; sp; left; allrw <-; sp; allrw; sp.
Qed.

Lemma eqorceq_commutes {p} :
  forall lib (a b c d : @CTerm p) eq,
    term_equality_respecting lib eq
    -> term_equality_symmetric eq
    -> term_equality_transitive eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> eq a c
    -> eq b d.
Proof.
  unfold eqorceq; introv ter tes tet eo1 eo2 e; sp.

  apply tet with (t2 := a); sp.
  apply tet with (t2 := c); sp.

  apply tet with (t2 := a); sp.
  apply tes.
  apply ter; auto.
  apply tet with (t2 := c); sp.
  apply tet with (t2 := c); sp.

  apply tet with (t2 := a); sp.
  apply tet with (t2 := c); sp.
  apply ter; auto.
  apply tet with (t2 := a); sp.

  apply tet with (t2 := a); sp.
  apply tes.
  apply ter; auto.
  apply tet with (t2 := c); sp.
  apply tet with (t2 := c); sp.
  apply ter; auto.
  apply tet with (t2 := a); sp.
Qed.
*)

Tactic Notation "dts_props" ident(h) ident(uv) ident(te) ident(tv) ident(tes) ident(tet) ident(ter) :=
  unfold type_system_props in h;
  destruct h as [uv  h];
  destruct h as [te  h];
  destruct h as [tv  h];
  destruct h as [tes h];
  destruct h as [tet ter].

Lemma eq_ts_cequivc {o} :
  forall lib (a b c d : @CTerm o) (eq : per(o)),
    term_equality_symmetric eq
    -> term_equality_transitive eq
    -> term_equality_respecting lib eq
    -> eq a b
    -> cequivc lib a c
    -> cequivc lib b d
    -> eq c d.
Proof.
  introv sym trans resp e1 c1 c2.

  apply (trans _ a).

  - apply sym.
    apply resp; spcast; auto.
    apply (trans _ b); auto.

  - apply (trans _ b); auto.
    apply resp; spcast; auto.
    apply (trans _ a); auto.
Qed.

(*
Lemma eqorceq_cequivc {o} :
  forall lib (a b c d : @CTerm o) (eq : per(o)),
    term_equality_symmetric eq
    -> term_equality_transitive eq
    -> term_equality_respecting lib eq
    -> eqorceq lib eq a b
    -> cequivc lib a c
    -> cequivc lib b d
    -> eqorceq lib eq c d.
Proof.
  introv sym trans resp e1 c1 c2.
  unfold eqorceq in *.
  repndors; spcast.

  - left.
    eapply eq_ts_cequivc; eauto.

  - right; spcast.
    eapply cequivc_trans;[|eauto].
    eapply cequivc_trans;[|eauto].
    apply cequivc_sym; auto.
Qed.
*)


(* --------- A FEW TACTICS --------- *)


Ltac appdup l H :=
  let newH := fresh H in
    remember H as newH; clear_eq newH H; apply l in newH.


Ltac eqconstr0 name :=
  match type of name with
    | mkc_uni _           = mkc_uni _           => apply mkc_uni_eq            in name
    | mkc_inl _           = mkc_inl _           => apply mkc_inl_eq            in name
    | mkc_inr _           = mkc_inr _           => apply mkc_inr_eq            in name
    | mkc_refl _          = mkc_refl _          => apply mkc_refl_eq           in name
    | mkc_prefl _ _       = mkc_prefl _ _       => apply mkc_prefl_eq          in name
    | mkc_integer _       = mkc_integer _       => apply mkc_integer_eq        in name
    | mkc_token _         = mkc_token _         => apply mkc_token_eq          in name
    | mkc_utoken _        = mkc_utoken _        => apply mkc_utoken_eq         in name
    | mkc_exception _ _   = mkc_exception _ _   => apply mkc_exception_eq      in name
    | mkc_pertype _       = mkc_pertype _       => apply mkc_pertype_eq        in name
    | mkc_ipertype _      = mkc_ipertype _      => apply mkc_ipertype_eq       in name
    | mkc_spertype _      = mkc_spertype _      => apply mkc_spertype_eq       in name
    | mkc_partial _       = mkc_partial _       => apply mkc_partial_eq        in name
    | mkc_admiss _        = mkc_admiss _        => apply mkc_admiss_eq         in name
    | mkc_mono _          = mkc_mono _          => apply mkc_mono_eq           in name
    | mkc_approx _ _      = mkc_approx _ _      => apply mkc_approx_eq         in name
    | mkc_cequiv _ _      = mkc_cequiv _ _      => apply mkc_cequiv_eq         in name
    | mkc_image _ _       = mkc_image _ _       => apply mkc_image_eq          in name
    | mkc_texc _ _        = mkc_texc _ _        => apply mkc_texc_eq           in name
    | mkc_union _ _       = mkc_union _ _       => apply mkc_union_eq          in name
    | mkc_eunion _ _      = mkc_eunion _ _      => apply mkc_eunion_eq         in name
    | mkc_sup _ _         = mkc_sup _ _         => apply mkc_sup_eq            in name
    | mkc_pair _ _        = mkc_pair _ _        => apply mkc_pair_eq           in name
    | mkc_aequality _ _ _ = mkc_aequality _ _ _ => apply mkc_aequality_eq      in name
    | mkc_equality _ _ _  = mkc_equality _ _ _  => apply mkc_equality_eq       in name
    | mkc_tequality _ _   = mkc_tequality _ _   => apply mkc_tequality_eq      in name

    | mkc_isect _ _ _    = mkc_isect _ _ _    => appdup mkc_isect_eq1    name; repd; subst; apply mkc_isect_eq2    in name
    | mkc_disect _ _ _   = mkc_disect _ _ _   => appdup mkc_disect_eq1   name; repd; subst; apply mkc_disect_eq2   in name
    | mkc_eisect _ _ _   = mkc_eisect _ _ _   => appdup mkc_eisect_eq1   name; repd; subst; apply mkc_eisect_eq2   in name
    | mkc_function _ _ _ = mkc_function _ _ _ => appdup mkc_function_eq1 name; repd; subst; apply mkc_function_eq2 in name
    | mkc_w _ _ _        = mkc_w _ _ _        => appdup mkc_w_eq1        name; repd; subst; apply mkc_w_eq2        in name
    | mkc_m _ _ _        = mkc_m _ _ _        => appdup mkc_m_eq1        name; repd; subst; apply mkc_m_eq2        in name
    | mkc_product _ _ _  = mkc_product _ _ _  => appdup mkc_product_eq1  name; repd; subst; apply mkc_product_eq2  in name
    | mkc_set _ _ _      = mkc_set _ _ _      => appdup mkc_set_eq1      name; repd; subst; apply mkc_set_eq2      in name
    | mkc_tunion _ _ _   = mkc_tunion _ _ _   => appdup mkc_tunion_eq1   name; repd; subst; apply mkc_tunion_eq2   in name

    | mkc_free_from_atom  _ _ _ = mkc_free_from_atom  _ _ _ => apply mkc_free_from_atom_eq  in name
    | mkc_efree_from_atom _ _ _ = mkc_efree_from_atom _ _ _ => apply mkc_efree_from_atom_eq in name

    | mkc_free_from_atoms _ _ = mkc_free_from_atoms _ _ => apply mkc_free_from_atoms_eq in name

    | mkc_pw _ _ _ _ _ _ _ _ _ _ _ = mkc_pw _ _ _ _ _ _ _ _ _ _ _ => appdup mkc_pw_eq1 name; repd; subst; apply mkc_pw_eq2 in name
    | mkc_pm _ _ _ _ _ _ _ _ _ _ _ = mkc_pm _ _ _ _ _ _ _ _ _ _ _ => appdup mkc_pm_eq1 name; repd; subst; apply mkc_pm_eq2 in name
  end.

Ltac eqconstr name :=
  try (eqconstr0 name);
  try (complete (dest_cterms name; allsimpl; inversion name));
  repd;
  subst;
  GC.

Ltac computes_to_eqval :=
  match goal with
    | [ H1 : computes_to_valc ?lib ?T ?T2,
             H2 : computes_to_valc ?lib ?T ?T1
        |- _ ] =>
      let name := fresh "eq" in
      assert (T1 = T2)
        as name
          by (apply (computes_to_valc_eq lib T); auto);
        eqconstr name
    | [ H1 : computes_to_excc ?lib ?a2 ?T ?T2,
             H2 : computes_to_excc ?lib ?a1 ?T ?T1
        |- _ ] =>
      let name := fresh "eq" in
      assert (a1 = a2 # T1 = T2)
        as name
          by (apply (computes_to_excc_eq lib T); auto);
       eqconstr name
  end.


(*
Ltac apply_defines_only_universes :=
  match goal with
    | [ H1 : type_system ?lib ?ts, H2 : defines_only_universes ?lib ?ts, H3 : ?ts ?T1 ?T2 ?eq |- _ ] =>
      let h  := fresh "h" in
      let h' := fresh "h'" in
      let e1 := fresh "e1" in
      let e2 := fresh "e2" in
      generalize (etype_system_ts_refl lib ts T1 T2 eq);
        intro h;
        repeat (dest_imp h h');
        destruct h as [e1 e2];
        apply H2 in e1;
        apply H2 in e2;
        exrepnd
  end.

Ltac close_diff :=
  allunfold_per;
  try (apply_defines_only_universes);
  uncast;
  computes_to_valc_diff.
*)

Ltac use_dou :=
  match goal with
    | [ H1 : defines_only_universes ?lib ?ts, H2 : ?ts ?T ?eq |- _ ] =>
      let c := fresh "c" in
      let i := fresh "i" in
      assert ({i : nat , ccomputes_to_valc lib T (mkc_uni i)}) as c
          by (apply H1 in H2; auto);
      exrepnd
  end.

Ltac close_diff :=
  allunfold_per;
  try (use_dou; exrepnd);
  uncast;
  computes_to_valc_diff.

Ltac ccomputes_to_eqval :=
  uncast; repeat computes_to_eqval.

Ltac dupcomp T h :=
  match goal with
    | [ H : computes_to_valc ?lib T ?x |- _ ] =>
        assert (computes_to_valc lib T x) as h by auto
  end.


Ltac dclose h1 h2 :=
  match goal with
    | [ H : close _ _ _ _ [+] close _ _ _ _ |- _ ] => destruct H as [h1 | h2]
    | [ H : close _ _ _ _ {+} close _ _ _ _ |- _ ] => destruct H as [h1 | h2]
  end.

Ltac doneclose :=
  match goal with
    | [ H : close _ _ _ _ |- _ ] => destruct H
  end.

Ltac ioneclose :=
  match goal with
    | [ H : close _ _ _ _ |- _ ] => inversion H
  end.

Ltac cioneclose :=
  match goal with
    | [ H : close _ _ _ _ |- _ ] => inversion H; clear H
  end.

Ltac cioneclose_eq eq :=
  match goal with
    | [ H : close _ _ _ eq |- _ ] => inversion H; clear H
  end.

Ltac find_term_equalities_step :=
  match goal with
    | [ H : type_system ?lib ?ts, H1 : ?ts ?T ?T1 ?eq1, H2 : ?ts ?T ?T2 ?eq2 |- _ ] =>
      let h := fresh "h" in
      assert (eq_term_equals eq1 eq2)
        as h
          by (generalize (euniquely_valued_eq_ts lib ts T T1 T2 eq1 eq2); sp);
        no_duplicate h
    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T ?eq1, H2 : ?ts ?T ?T2 ?eq2 |- _ ] =>
      let h := fresh "h" in
      assert (eq_term_equals eq1 eq2)
        as h
          by (generalize (euniquely_valued_eq2_ts lib ts T T1 T2 eq1 eq2); sp);
        no_duplicate h
  end.

Ltac find_term_equalities := repeat find_term_equalities_step.

(* simple reasoning on type systems *)
Ltac spts :=
  match goal with
    | [ H : etype_system ?lib ?ts, H1 : ?ts ?T ?T1 ?eq1, H2 : ?ts ?T ?T2 ?eq2
        |- eq_term_equals ?eq1 ?eq2 ] =>
      generalize (euniquely_valued_eq_ts lib ts T T1 T2 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T ?eq1, H2 : ?ts ?T ?eq2
        |- eq_term_equals ?eq1 ?eq2 ] =>
      generalize (uniquely_valued_eq_ts lib ts T eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T ?eq1, H2 : ?ts ?T ?T2 ?eq2
        |- eq_term_equals ?eq1 ?eq2 ] =>
      generalize (euniquely_valued_eq2_ts lib ts T T1 T2 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T ?T' ?eq1, H2 : eq_term_equals ?eq1 ?eq2
        |- ?ts ?T ?T' ?eq2 ] =>
      unfold type_system in H;
        repnd;
        match goal with
            [ H3 : etype_extensionality ts |- _ ] =>
            unfold etype_extensionality in H3;
              generalize (H3 T T' eq1 eq2);
              complete sp
        end

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T2 ?T3 ?eq2
        |- ?ts ?T1 ?T3 ?eq1 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans2 ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T2 ?T3 ?eq2
        |- ?ts ?T3 ?T3 ?eq1 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans2_r ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T2 ?T3 ?eq2
        |- ?ts ?T1 ?T3 ?eq2 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans4 ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T2 ?T3 ?eq2
        |- ?ts ?T3 ?T3 ?eq2 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans4_r ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T1 ?T3 ?eq2
        |- ?ts ?T2 ?T3 ?eq1 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans7 ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T1 ?T3 ?eq2
        |- ?ts ?T3 ?T3 ?eq1 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans7_r ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T1 ?T3 ?eq2
        |- ?ts ?T2 ?T3 ?eq2 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans8 ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq1, H2 : ?ts ?T1 ?T3 ?eq2
        |- ?ts ?T3 ?T3 ?eq2 ] =>
      unfold type_system in H;
        repnd;
        generalize (euniquely_valued_trans8_r ts T1 T2 T3 eq1 eq2);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq, H2 : cequivc ?lib ?T1 ?T3
        |- ?ts ?T1 ?T3 ?eq ] =>
      unfold type_system in H;
        repnd;
        generalize (etype_reduces_to_symm lib ts T1 T2 T3 eq);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T2 ?T1 ?eq, H2 : cequivc ?lib ?T1 ?T3
        |- ?ts ?T1 ?T3 ?eq ] =>
      unfold type_system in H;
        repnd;
        generalize (etype_reduces_to_symm2 lib ts T1 T2 T3 eq);
        complete sp

    | [ H : type_system ?lib ?ts, H1 : ?ts ?T1 ?T2 ?eq
        |- ?ts ?T2 ?T1 ?eq ] =>
      unfold type_system in H;
        complete sp
  end.

Ltac implies_ts_or_eq T1 T2 T h :=
  match goal with
      | [ H : ?ts T1 T2 ?eq |- _ ] =>
          rename H into h; implies_ts_or T h
  end.

Ltac rev_implies_ts_or_eq T1 T2 T h :=
  match goal with
      | [ H : ?ts T1 T2 ?eq |- _ ] =>
          rename H into h; rev_implies_ts_or T h
  end.

(* end hide *)
