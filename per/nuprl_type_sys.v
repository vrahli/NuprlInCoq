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


(* MOVE to computation_lib_extends *)
Tactic Notation "lib_ext_ind2" ident(ext) ident(c) ident(cor) ident(ni) ident(addc) ident(cond) :=
  induction ext as [|
                    |? ? ? ? ? ni
                    |? ? ? cor ni
                    |? ? ? ? ? ? ? ? ? addc findr cond
                    |? ? ? ? ? ? ? addc findr cond
                    |? ? ? ? ? ? ? addc findr cond];
  [ Case_aux c "lib_ext_refl"
  | Case_aux c "lib_ext_trans"
  | Case_aux c "lib_ext_new_abs"
  | Case_aux c "lib_ext_new_cs"
  | Case_aux c "lib_ext_cs"
  | Case_aux c "lib_ext_law"
  | Case_aux c "lib_ext_res"
  ];
  simpl.

Tactic Notation "lib_ext_ind2" ident(ext) ident(c) :=
  let cor  := fresh "cor"  in
  let ni   := fresh "ni"   in
  let addc := fresh "addc" in
  let cond := fresh "cond" in
  lib_ext_ind2 ext c cor ni addc cond.


Lemma implies_computes_to_uni {o} :
  forall inh lib (T : @CTerm o) i,
    ccomputes_to_valc_ext inh lib T (mkc_uni i)
    -> computes_to_uni inh lib T.
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext.
  exists i; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_uni : slow.

Lemma implies_computes_to_uni_like {o} :
  forall inh lib (T : @CTerm o) i,
    ccomputes_to_valc_ext inh lib T (mkc_uni i)
    -> computes_to_uni_like inh lib T.
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext.
  exists i; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_uni_like : slow.

Definition defines_only_uni {o} inh (ts : cts(o)) :=
  forall lib (T : @CTerm o) eq,
    ts lib T T eq
    -> computes_to_uni inh lib T.

Lemma computes_to_uni_implies_computes_to_uni_like {o} :
  forall inh lib (T : @CTerm o),
    computes_to_uni inh lib T
    -> computes_to_uni_like inh lib T.
Proof.
  introv comp.
  eapply in_open_bar_comb; try exact comp; clear comp.
  apply in_ext_implies_in_open_bar; introv ext comp; exrepnd; exists i; tcsp.
Qed.
Hint Resolve computes_to_uni_implies_computes_to_uni_like : slow.

Lemma defines_only_uni_implies_defines_only_universes {o} :
  forall inh (ts : cts(o)),
    defines_only_uni inh ts
    -> defines_only_universes inh ts.
Proof.
  introv dou h; apply dou in h; clear dou; eauto 3 with slow.
Qed.
Hint Resolve defines_only_uni_implies_defines_only_universes : slow.

Lemma defines_only_uni_univi {o} :
  forall inh uni i, @defines_only_uni o inh (univi i inh uni).
Proof.
  unfold defines_only_uni; sp.
  allrw @univi_exists_iff; sp; spcast; eauto 3 with slow.
Qed.
Hint Resolve defines_only_uni_univi : slow.

Lemma defines_only_universes_univi {o} :
  forall inh uni i, @defines_only_universes o inh (univi i inh uni).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve defines_only_universes_univi : slow.

Lemma defines_only_universes_univi_bar {o} :
  forall inh uni i,
    defines_only_universes inh uni
    -> @defines_only_universes o inh (univi_bar i inh uni).
Proof.
  introv dou u.
  unfold univi_bar, per_bar in u; exrepnd.
  apply in_open_bar_ext_in_open_bar.
  eapply in_open_bar_ext_comb; eauto; clear u1.
  apply in_ext_ext_implies_in_open_bar_ext; introv u1.
  destruct u1 as [u1|u1].
  { allrw @univi_exists_iff; exrepnd.
    apply in_ext_implies_in_open_bar; introv ext.
    exists j; eauto 3 with slow. }
  { apply dou in u1; tcsp. }
Qed.
Hint Resolve defines_only_universes_univi_bar : slow.

Lemma defines_only_universes_univ {o} :
  @defines_only_universes o nuprla_ex_inh univ.
Proof.
  unfold defines_only_universes, univ, univi_ex_bar, univi_ex.
  introv per.
  unfold per_bar in *; exrepnd.
  eapply in_open_bar_comb2; eauto; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv u1; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  exists j; auto.
Qed.
Hint Resolve defines_only_universes_univ : slow.


(* end hide *)

(**

  We prove that all the Nuprl universes satisfy the type system
  properties.

*)

Lemma ccequivc_ext_uni {o} :
  forall inh lib (T T' : @CTerm o) i,
    ccequivc_ext inh lib T T'
    -> ccomputes_to_valc lib T (mkc_uni i)
    -> ccomputes_to_valc lib T' (mkc_uni i).
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_uni in ceq';[|eauto]; exrepnd; auto.
Qed.

Lemma per_bar_univi_uniquely_valued {o} :
  forall inh uni i lib (T T' : @CTerm o) eq1 eq2,
    per_bar inh (univi i inh uni) lib T T' eq1
    -> per_bar inh (univi i inh uni) lib T T' eq2
    -> eq1 <=2=> eq2.
Proof.
  introv u v.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold per_bar_eq; introv; split; intro h.

  - eapply in_open_bar_ext_comb; try exact u1; clear u1.
    eapply in_open_bar_ext_comb; try exact v1; clear v1.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h v1 u1.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval_ext.
    apply ccequivc_ext_uni_uni_implies in ceq; subst.
    apply v2; apply u2; auto.

  - eapply in_open_bar_ext_comb; try exact u1; clear u1.
    eapply in_open_bar_ext_comb; try exact v1; clear v1.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h v1 u1.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval_ext.
    apply ccequivc_ext_uni_uni_implies in ceq; subst.
    apply u2; apply v2; auto.
Qed.

Lemma uniquely_valued_univi {o} :
  forall inh uni i, @uniquely_valued o (univi i inh uni).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd; spcast.
  computes_to_eqval_ext.
  apply ccequivc_ext_uni_uni_implies in ceq; subst.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve uniquely_valued_univi : slow.

Lemma type_symmetric_univi {o} :
  forall inh uni i, @type_symmetric o (univi i inh uni).
Proof.
  introv u.
  allrw @univi_exists_iff; exrepnd.
  exists j; sp.
Qed.
Hint Resolve type_symmetric_univi : slow.

Lemma type_extensionality_univi {o} :
  forall inh uni i, @type_extensionality o (univi i inh uni).
Proof.
  introv u e.
  allrw @univi_exists_iff; exrepnd.
  exists j; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve type_extensionality_univi : slow.

Lemma type_transitive_univi {o} :
  forall inh uni i, @type_transitive o (univi i inh uni).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd.
  spcast; computes_to_eqval_ext.
  apply ccequivc_ext_uni_uni_implies in ceq; subst.
  exists j0; dands; spcast; auto.
Qed.
Hint Resolve type_transitive_univi : slow.

Lemma type_value_respecting_univi {o} :
  forall inh uni i, @type_value_respecting o inh (univi i inh uni).
Proof.
  introv u c.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  exists j; dands; eauto 3 with slow.
Qed.
Hint Resolve type_value_respecting_univi : slow.

Definition ts_disjoint {o} (ts1 ts2 : cts(o)) :=
  forall lib (T T' : @CTerm o) eq1 eq2,
    ts1 lib T T' eq1
    -> ts2 lib T T' eq2
    -> False.

Lemma uniquely_valued_or {o} :
  forall (ts1 ts2 : cts(o)),
    ts_disjoint ts1 ts2
    -> uniquely_valued ts1
    -> uniquely_valued ts2
    -> uniquely_valued (cts_or ts1 ts2).
Proof.
  introv disj ua ub h q.
  destruct h as [h|h]; destruct q as [q|q]; tcsp;
    try (complete (eapply ua; eauto));
    try (complete (eapply ub; eauto));
    try (complete (eapply disj in h; apply h in q; tcsp));
    try (complete (eapply disj in q; apply q in h; tcsp)).
Qed.
Hint Resolve uniquely_valued_or : slow.

Lemma if_in_open_bar {o} :
  forall inh (lib : @library o) P,
    in_open_bar inh lib (fun lib => P)
    -> P.
Proof.
  introv h.
  pose proof (h _ (lib_extends_refl _ _)) as h; exrepnd.
  pose proof (h1 _ (lib_extends_refl _ _)) as h1; simpl in *; auto.
Qed.

Definition not_uni {o} inh (ts : cts(o)) :=
  forall lib (T T' : @CTerm o) eq,
    ts lib T T' eq
    -> in_open_bar inh lib (fun lib => forall i, ~ T ===>(inh,lib) (mkc_uni i)).

Lemma implies_ts_disjoint_univi {o} :
  forall inh uni i,
    not_uni inh uni
    -> @ts_disjoint o (univi i inh uni) uni.
Proof.
  introv nu h q.
  assert (univi i inh uni lib T T eq1) as w.
  { eapply type_transitive_univi;[|apply type_symmetric_univi]; eauto. }
  pose proof (defines_only_uni_univi inh uni i lib T eq1 w) as z.
  apply nu in q.
  unfold computes_to_uni in *.
  apply (if_in_open_bar inh lib).
  eapply in_open_bar_comb; try exact z; clear z.
  eapply in_open_bar_comb; try exact q; clear q.
  apply in_ext_implies_in_open_bar; introv ext q z; exrepnd.
  apply q in z0; auto.
Qed.
Hint Resolve implies_ts_disjoint_univi :slow.

Lemma ts_implies_per_bar_univi_bar {o} :
  forall inh uni i,
    not_uni inh uni
    -> uniquely_valued uni
    -> @ts_implies_per_bar o inh (univi_bar i inh uni).
Proof.
  introv nu uvu u.
  unfold univi_bar in *; exrepnd.

  applydup @per_bar_monotone_func2 in u; exrepnd.
  exists eq'.
  dands.

  { apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply u1. }

  { eapply implies_eq_term_equals_per_bar_eq_trivial_bar_mon; try exact u; eauto 3 with slow. }
Qed.
Hint Resolve ts_implies_per_bar_univi_bar : slow.

Lemma type_extensionality_or {o} :
  forall (ts1 ts2 : cts(o)),
    type_extensionality ts1
    -> type_extensionality ts2
    -> type_extensionality (cts_or ts1 ts2).
Proof.
  introv exta extb h q.
  destruct h as [h|h];[left|right].
  { eapply exta; eauto. }
  { eapply extb; eauto. }
Qed.
Hint Resolve type_extensionality_or : slow.

Lemma local_univi_bar {o} :
  forall inh uni i,
    uniquely_valued uni
    -> type_extensionality uni
    -> not_uni inh uni
    -> @local_ts o inh (univi_bar i inh uni).
Proof.
  introv uv ext nu eqiff alla.
  eapply local_per_bar in alla; eauto 3 with slow.
Qed.
Hint Resolve local_univi_bar : slow.

Lemma term_symmetric_univi_bar {o} :
  forall inh uni i,
    uniquely_valued uni
    -> defines_only_universes inh uni
    -> type_extensionality uni
    -> term_symmetric uni
    -> not_uni inh uni
    -> (forall m, m < i -> @type_system o inh (univi_bar m inh uni))
    -> @term_symmetric o (univi_bar i inh uni).
Proof.
  introv uv dou ext sym nu IND u e.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; eauto; clear e; introv h u1.

  destruct u1 as [u1|u1].

  { allrw @univi_exists_iff; exrepnd.
    spcast.
    apply u0 in h; apply u0; clear u0.
    unfold univi_eq, close_ex_eq in *; exrepnd.
    exists eqa0.
    apply close_type_symmetric; eauto 3 with slow. }

  { apply sym in u1; apply u1; auto. }
Qed.
Hint Resolve term_symmetric_univi_bar : slow.

Lemma term_transitive_univi_bar {o} :
  forall inh uni i,
    uniquely_valued uni
    -> defines_only_universes inh uni
    -> type_extensionality uni
    -> term_transitive uni
    -> not_uni inh uni
    -> (forall m, m < i -> @type_system o inh (univi_bar m inh uni))
    -> @term_transitive o (univi_bar i inh uni).
Proof.
  introv uv dou text trans nu IND u e f.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_comb; try exact e; clear e.
  eapply in_open_bar_ext_pres; try exact f; clear f; introv f h u1.

  destruct u1 as [u1|u1].

  { allrw @univi_exists_iff; exrepnd.
    spcast.
    apply u0 in h; apply u0 in f; apply u0; clear u0.
    unfold univi_eq, close_ex_eq in *; exrepnd.
    exists eqa0.

    eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_extensionality; eauto 2 with slow.

    assert (close inh (univi_bar j inh uni) lib' t2 t2 eqa1) as h1.
    { eapply close_type_transitive; eauto; eauto 3 with slow.
      eapply close_type_symmetric; eauto; eauto 3 with slow. }

    assert (close inh (univi_bar j inh uni) lib' t2 t2 eqa0) as h2.
    { eapply close_type_transitive; eauto; eauto 3 with slow.
      eapply close_type_symmetric; eauto; eauto 3 with slow. }

    eapply close_uniquely_valued in h1; eauto 3 with slow. }

  { eapply trans in u1; eauto. }
Qed.
Hint Resolve term_transitive_univi_bar : slow.

Lemma term_value_respecting_univi_bar {o} :
  forall inh uni i,
    uniquely_valued uni
    -> defines_only_universes inh uni
    -> type_extensionality uni
    -> term_value_respecting inh uni
    -> not_uni inh uni
    -> (forall m, m < i -> @type_system o inh (univi_bar m inh uni))
    -> @term_value_respecting o inh (univi_bar i inh uni).
Proof.
  introv uv dou text resp nu IND u e c.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.

  destruct u1 as [u1|u1].

  { allrw @univi_exists_iff; exrepnd.
    spcast.
    apply u0 in h; apply u0; clear u0.
    unfold univi_eq, close_ex_eq in *; exrepnd.
    exists eqa0.

    eapply close_type_value_respecting; eauto 3 with slow. }

  { eapply resp in u1; apply u1; eauto 3 with slow. }
Qed.
Hint Resolve term_value_respecting_univi_bar : slow.

Lemma type_symmetric_or {o} :
  forall (ts1 ts2 : cts(o)),
    type_symmetric ts1
    -> type_symmetric ts2
    -> type_symmetric (cts_or ts1 ts2).
Proof.
  introv syma symb h.
  destruct h as [h|h].
  { apply syma in h; tcsp. }
  { apply symb in h; tcsp. }
Qed.
Hint Resolve type_symmetric_or : slow.

Lemma type_transitive_or {o} :
  forall (ts1 ts2 : cts(o)),
    ts_disjoint ts1 ts2
    -> type_symmetric ts1
    -> type_symmetric ts2
    -> type_transitive ts1
    -> type_transitive ts2
    -> type_transitive (cts_or ts1 ts2).
Proof.
  introv disj syma symb tra trb h q.
  destruct h as [h|h]; destruct q as [q|q].
  { left; eapply tra in h; eauto. }
  { assert (ts1 lib T2 T2 eq) as h' by (eapply tra; eauto).
    assert (ts2 lib T2 T2 eq) as q' by (eapply trb; eauto).
    eapply disj in h'; apply h' in q'; tcsp. }
  { assert (ts1 lib T2 T2 eq) as h' by (eapply tra; eauto).
    assert (ts2 lib T2 T2 eq) as q' by (eapply trb; eauto).
    eapply disj in h'; apply h' in q'; tcsp. }
  { right; eapply trb in h; eauto. }
Qed.
Hint Resolve type_transitive_or : slow.

Lemma type_value_respecting_or {o} :
  forall inh (ts1 ts2 : cts(o)),
    type_value_respecting inh ts1
    -> type_value_respecting inh ts2
    -> type_value_respecting inh (cts_or ts1 ts2).
Proof.
  introv respa respb h ceq.
  destruct h as [h|h]; tcsp.
Qed.
Hint Resolve type_value_respecting_or : slow.

Lemma type_system_implies_uniquely_valued {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> uniquely_valued ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_uniquely_valued : slow.

Lemma type_system_implies_type_symmetric {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> type_symmetric ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_type_symmetric : slow.

Lemma type_system_implies_type_transitive {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> type_transitive ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_type_transitive : slow.

Lemma type_system_implies_type_extensionality {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> type_extensionality ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_type_extensionality : slow.

Lemma type_system_implies_type_value_respecting {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> type_value_respecting inh ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_type_value_respecting : slow.

Lemma type_system_implies_term_symmetric {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> term_symmetric ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_term_symmetric : slow.

Lemma type_system_implies_term_transitive {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> term_transitive ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_term_transitive : slow.

Lemma type_system_implies_term_value_respecting {o} :
  forall inh (ts : cts(o)),
    type_system inh ts -> term_value_respecting inh ts.
Proof.
  introv tysys.
  unfold type_system in *; tcsp.
Qed.
Hint Resolve type_system_implies_term_value_respecting : slow.

Lemma univi_bar_type_system {o} :
  forall inh uni (i : nat),
    not_uni inh uni
    -> defines_only_universes inh uni
    -> type_system inh uni
    -> @type_system o inh (univi_bar i inh uni).
Proof.
  induction i using comp_ind_type; introv nu dou tysys.
  unfold type_system; dands; eauto 6 with slow.

  - eapply uniquely_valued_per_bar; eauto 4 with slow.

  - apply type_symmetric_per_bar; eauto 3 with slow.

  - apply type_transitive_per_bar; eauto 5 with slow.

  - apply type_value_respecting_per_bar; eauto 4 with slow.
Qed.
Hint Resolve univi_bar_type_system : slow.

Lemma term_symmetric_univi {o} :
  forall inh uni i,
    not_uni inh uni
    -> defines_only_universes inh uni
    -> type_system inh uni
    -> @term_symmetric o (univi i inh uni).
Proof.
  introv nu dou tysys u e.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0; clear u0.
  unfold univi_eq, close_ex_eq in *; exrepnd.
  exists eqa.
  eapply close_type_symmetric; eauto 4 with slow.
Qed.
Hint Resolve term_symmetric_univi : slow.

Lemma term_transitive_univi {o} :
  forall inh uni i,
    not_uni inh uni
    -> defines_only_universes inh uni
    -> type_system inh uni
    -> @term_transitive o (univi i inh uni).
Proof.
  introv nu dou tysys u e f.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold univi_eq, close_ex_eq in *; exrepnd.
  exists eqa.
  eapply close_type_transitive; eauto 4 with slow.
  eapply close_type_extensionality; eauto 4 with slow;[].

  assert (close inh (univi_bar j inh uni) lib t2 t2 eqa0) as h1.
  { eapply close_type_transitive; eauto; eauto 4 with slow.
    eapply close_type_symmetric; eauto; eauto 4 with slow. }

  assert (close inh (univi_bar j inh uni) lib t2 t2 eqa) as h2.
  { eapply close_type_transitive; eauto; eauto 4 with slow.
    eapply close_type_symmetric; eauto; eauto 4 with slow. }

  eapply close_uniquely_valued in h1; eauto 4 with slow.
Qed.
Hint Resolve term_transitive_univi : slow.

Lemma term_value_respecting_univi {o} :
  forall inh uni i,
    not_uni inh uni
    -> defines_only_universes inh uni
    -> type_system inh uni
    -> @term_value_respecting o inh (univi i inh uni).
Proof.
  introv nu dou tysys u e c.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0; clear u0.
  unfold univi_eq, close_ex_eq in *; exrepnd.
  exists eqa.
  eapply close_type_value_respecting; eauto 4 with slow.
Qed.
Hint Resolve term_value_respecting_univi : slow.

Lemma univi_type_system {o} :
  forall inh uni (i : nat),
    not_uni inh uni
    -> defines_only_universes inh uni
    -> type_system inh uni
    -> @type_system o inh (univi i inh uni).
Proof.
  introv nu dou tysys; unfold type_system; dands; eauto 4 with slow.
Qed.
Hint Resolve univi_type_system : slow.

(* begin hide *)

Lemma univi_univa_ex_ts_disjoint {o} :
  forall i inh uni, @ts_disjoint o (univi i inh uni) univa_ex.
Proof.
  introv h q.
  allrw @univi_exists_iff; exrepnd.
  unfold univa_ex in *; exrepnd.
  allrw @univa_iff; exrepnd; subst.
  pose proof (h2 _ (lib_extends_refl _ _)) as h2; simpl in *.
  pose proof (q2 _ (lib_extends_refl _ _)) as q2; simpl in *.
  exrepnd; spcast.
  eapply computes_to_valc_eq in h2; try exact q2; subst.
  assert (cequivc lib (mkc_uni j) (mkc_index j0)) as ceq.
  { eapply cequivc_trans; eauto; apply cequivc_sym; auto. }
  apply cequivc_index_right_iscvalue in ceq; eauto 3 with slow.
  inversion ceq.
Qed.
Hint Resolve univi_univa_ex_ts_disjoint : slow.

Lemma implies_univia_successor {o} :
  forall i lib T T' (p : per(o)),
    univa i lib T T' p
    -> univa (S i) lib T T' p.
Proof.
  introv h; tcsp.
Qed.

Lemma implies_univa_add_right {o} :
  forall j i lib T T' (p : per(o)),
    univa i lib T T' p
    -> univa (i + j) lib T T' p.
Proof.
  induction j; introv h; autorewrite with nat in *; tcsp.
  rewrite Nat.add_succ_r.
  apply implies_univia_successor; tcsp.
Qed.

Lemma implies_univa_add_left {o} :
  forall j i lib T T' (p : per(o)),
    univa i lib T T' p
    -> univa (j + i) lib T T' p.
Proof.
  induction j; introv h; autorewrite with nat in *; tcsp.
Qed.

Lemma univa_uniquely_valued {o} : forall i, @uniquely_valued o (univa i).
Proof.
  introv ua ub.
  allrw @univa_iff; exrepnd.
  pose proof (ub2 _ (lib_extends_refl _ _)) as ub2; simpl in *.
  pose proof (ua2 _ (lib_extends_refl _ _)) as ua2; simpl in *.
  exrepnd; spcast.
  eapply computes_to_valc_eq in ua2; try exact ub2; subst.
  assert (cequivc lib (mkc_index j) (mkc_index j0)) as ceq.
  { eapply cequivc_trans; eauto; apply cequivc_sym; auto. }
  apply cequivc_index_right_iscvalue in ceq; eauto 3 with slow.
  inversion ceq; subst.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve univa_uniquely_valued : slow.

Lemma univa_ex_uniquely_valued {o} : @uniquely_valued o univa_ex.
Proof.
  introv ua ub.
  unfold univa_ex in *; exrepnd.
  apply (implies_univa_add_right i) in ua0.
  apply (implies_univa_add_left i0) in ub0.
  eapply univa_uniquely_valued; eauto.
Qed.
Hint Resolve univa_ex_uniquely_valued : slow.

Lemma univia_i_local_ts {o} :
  forall i, @local_ts o nuprla_ex_inh (univia_i i).
Proof.
  introv.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univia_i_local_ts : slow.

Lemma univia_i_ts_implies_per_bar {o} :
  forall i, @ts_implies_per_bar o nuprla_ex_inh (univia_i i).
Proof.
  introv u.

  applydup @per_bar_monotone_func2 in u; exrepnd.
  exists eq'.
  dands.

  { apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply u1. }

  { eapply implies_eq_term_equals_per_bar_eq_trivial_bar_mon; try exact u; eauto 3 with slow. }
Qed.
Hint Resolve univia_i_ts_implies_per_bar : slow.

Lemma univia_i_uniquely_valued {o} :
  forall i, @uniquely_valued o (univia_i i).
Proof.
  introv; apply uniquely_valued_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univia_i_uniquely_valued : slow.

Lemma univia_i_type_extensionality {o} :
  forall i, @type_extensionality o (univia_i i).
Proof.
  introv; eauto 3 with slow.
  apply type_extensionality_per_bar.
Qed.
Hint Resolve univia_i_type_extensionality : slow.

Lemma univa_type_symmetric {o} : forall i, @type_symmetric o (univa i).
Proof.
  introv h.
  allrw @univa_iff; exrepnd; exists j; dands; tcsp.
Qed.
Hint Resolve univa_type_symmetric : slow.

Lemma univa_ex_type_symmetric {o} : @type_symmetric o univa_ex.
Proof.
  introv h.
  unfold univa_ex in *; exrepnd; exists i.
  apply univa_type_symmetric; auto.
Qed.
Hint Resolve univa_ex_type_symmetric : slow.

Lemma univia_i_type_symmetric {o} :
  forall i, @type_symmetric o (univia_i i).
Proof.
  introv.
  apply type_symmetric_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univia_i_type_symmetric : slow.

Lemma univa_type_transitive {o} : forall i, @type_transitive o (univa i).
Proof.
  introv h q.
  allrw @univa_iff; exrepnd; exists j; dands; tcsp.
  pose proof (q2 _ (lib_extends_refl _ _)) as q2; simpl in *.
  pose proof (h3 _ (lib_extends_refl _ _)) as h3; simpl in *.
  exrepnd; spcast.
  eapply computes_to_valc_eq in q2; try exact h3; subst.
  assert (cequivc lib (mkc_index j) (mkc_index j0)) as ceq.
  { eapply cequivc_trans; eauto; apply cequivc_sym; auto. }
  apply cequivc_index_right_iscvalue in ceq; eauto 3 with slow.
  inversion ceq; subst; tcsp.
Qed.
Hint Resolve univa_type_transitive : slow.

Lemma univa_ex_type_transitive {o} : @type_transitive o univa_ex.
Proof.
  introv h q.
  unfold univa_ex in *; exrepnd.
  apply (implies_univa_add_right i) in h0.
  apply (implies_univa_add_left i0) in q0.
  exists (i0 + i).
  eapply univa_type_transitive; eauto.
Qed.
Hint Resolve univa_ex_type_transitive : slow.

Lemma univia_i_type_transitive {o} :
  forall i, @type_transitive o (univia_i i).
Proof.
  introv.
  apply type_transitive_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univia_i_type_transitive : slow.

Lemma inh_cts_nuprla_implies_nuprla_ex_inh {o} :
  forall j lib (T : @CTerm o),
    inh_cts (nuprla j) lib T
    -> nuprla_ex_inh lib T.
Proof.
  introv h; unfold nuprla_ex_inh, nuprla_ex, inh_cts in *; exrepnd.
  exists per t; dands; eauto.
Qed.
Hint Resolve inh_cts_nuprla_implies_nuprla_ex_inh : slow.

Lemma nuprla_ex_inh_implies_inh_cts_nuprla {o} :
  forall lib (T : @CTerm o),
    nuprla_ex_inh lib T
    -> exists j, inh_cts (nuprla j) lib T.
Proof.
  introv h; unfold nuprla_ex_inh, nuprla_ex, inh_cts in *; exrepnd.
  exists i per t; dands; eauto.
Qed.
Hint Resolve nuprla_ex_inh_implies_inh_cts_nuprla : slow.

Lemma lib_extends_cts_nuprla_implies_nuprla_ex_inh {o} :
  forall j (lib' lib : @library o),
    lib_extends (inh_cts (nuprla j)) lib' lib
    -> lib_extends nuprla_ex_inh lib' lib.
Proof.
  introv h; lib_ext_ind h Case; eauto.
Qed.
Hint Resolve lib_extends_cts_nuprla_implies_nuprla_ex_inh : slow.

Lemma lib_extends_cts_nuprla_implies_successor {o} :
  forall j (lib' lib : @library o),
    lib_extends (inh_cts (nuprla j)) lib' lib
    -> lib_extends (inh_cts (nuprla (S j))) lib' lib.
Proof.
  introv h; lib_ext_ind h Case; eauto.
  eapply lib_extends_res; eauto.
  unfold inh_cts in *; exrepnd.
  exists per t; dands; tcsp.
Qed.
Hint Resolve lib_extends_cts_nuprla_implies_successor : slow.

Lemma lib_extends_cts_nuprla_implies_add_right {o} :
  forall k j (lib' lib : @library o),
    lib_extends (inh_cts (nuprla j)) lib' lib
    -> lib_extends (inh_cts (nuprla (j + k))) lib' lib.
Proof.
  induction k; introv h; autorewrite with nat; auto.
  rewrite Nat.add_succ_r.
  apply lib_extends_cts_nuprla_implies_successor; auto.
Qed.
Hint Resolve lib_extends_cts_nuprla_implies_add_right : slow.

Lemma lib_extends_cts_nuprla_implies_add_left {o} :
  forall k j (lib' lib : @library o),
    lib_extends (inh_cts (nuprla j)) lib' lib
    -> lib_extends (inh_cts (nuprla (k + j))) lib' lib.
Proof.
  induction k; introv h; autorewrite with nat; auto.
  apply lib_extends_cts_nuprla_implies_successor; auto.
Qed.
Hint Resolve lib_extends_cts_nuprla_implies_add_left : slow.

Lemma lib_extends_nuprla_ex_inh_implies_cts_nuprla {o} :
  forall (lib' lib : @library o),
    lib_extends nuprla_ex_inh lib' lib
    -> exists j, lib_extends (inh_cts (nuprla j)) lib' lib.
Proof.
  introv h; lib_ext_ind2 h Case; try (complete (exists 0; eauto 2 with slow)).

  { exrepnd.
    apply (lib_extends_cts_nuprla_implies_add_right j) in IHh2.
    apply (lib_extends_cts_nuprla_implies_add_left j0) in IHh0.
    exists (j0 + j); eauto. }

  apply nuprla_ex_inh_implies_inh_cts_nuprla in cond; exrepnd.
  exists j.
  eapply lib_extends_res; eauto.
Qed.
Hint Resolve lib_extends_nuprla_ex_inh_implies_cts_nuprla : slow.

Lemma univa_type_value_respecting {o} :
  forall i, @type_value_respecting o nuprla_ex_inh (univa i).
Proof.
  introv h q.
  allrw @univa_iff; exrepnd; exists j; dands; tcsp; GC.

  introv ext.
  applydup @lib_extends_cts_nuprla_implies_nuprla_ex_inh in ext.
  pose proof (q _ ext0) as q.
  pose proof (h2 _ ext) as h2.
  simpl in *; exrepnd; spcast.
  eapply cequivc_preserves_computes_to_valc in h2; eauto; exrepnd.
  exists U'; dands; spcast; auto.
  eapply cequivc_trans;[|eauto]; eauto 3 with slow.
Qed.
Hint Resolve univa_type_symmetric : slow.

Lemma univa_ex_type_value_respecting {o} : @type_value_respecting o nuprla_ex_inh univa_ex.
Proof.
  introv h q.
  unfold univa_ex in *; exrepnd; exists i.
  apply univa_type_value_respecting; auto.
Qed.
Hint Resolve univa_ex_type_value_respecting : slow.

Lemma univia_i_type_value_respecting {o} :
  forall i, @type_value_respecting o nuprla_ex_inh (univia_i i).
Proof.
  introv; apply type_value_respecting_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univia_i_type_value_respecting : slow.

Lemma term_symmetric_or {o} :
  forall (ts1 ts2 : cts(o)),
    term_symmetric ts1
    -> term_symmetric ts2
    -> term_symmetric (cts_or ts1 ts2).
Proof.
  introv h q w z.
  destruct w as [w|w].
  { eapply h; eauto. }
  { eapply q; eauto. }
Qed.
Hint Resolve term_symmetric_or : slow.

Lemma univa_not_uni {o} :
  forall i, @not_uni o nuprla_ex_inh (univa i).
Proof.
  introv h.
  apply in_ext_implies_in_open_bar.
  introv ext comp.
  applydup @lib_extends_nuprla_ex_inh_implies_cts_nuprla in ext; exrepnd.

  allrw @univa_iff; exrepnd.

  apply (lib_extends_cts_nuprla_implies_add_right j0) in ext1.
  apply (implies_univa_add_left j) in h2.

XXXXXXXXXX

  pose proof (h2 _ (lib_extends_refl _ _)) as h2; simpl in h2; exrepnd; spcast.
SearchAbout lib_extends computes_to_valc.
Qed.
Hint Resolve univa_not_uni : slow.

(*Lemma univa_ex_not_uni {o} :
  @not_uni o nuprla_ex_inh univa_ex.
Proof.
  introv h; unfold univa_ex in *; exrepnd.
Qed.
Hint Resolve univa_ex_not_uni : slow.

subgoal 2 (ID 589) is:
 defines_only_universes nuprla_ex_inh univa_ex
subgoal 3 (ID 590) is:
 type_system nuprla_ex_inh univa_ex*)

Lemma univia_i_term_symmetric {o} :
  forall i, @term_symmetric o (univia_i i).
Proof.
  introv; apply term_symmetric_per_bar; eauto 3 with slow.
  eapply term_symmetric_or; eauto 3 with slow.
  { apply term_symmetric_univi; eauto 3 with slow.

SearchAbout not_uni.
SearchAbout defines_only_universes univa_ex.

Qed.
Hint Resolve univia_i_term_symmetric : slow.

Lemma univia_i_term_transitive {o} :
  forall i, @term_transitive o (univia_i i).
Proof.
Qed.
Hint Resolve univia_i_term_transitive : slow.

Lemma univia_i_term_value_respecting {o} :
  forall i, @term_value_respecting o (univia_i i).
Proof.
Qed.
Hint Resolve univia_i_term_value_respecting : slow.

Lemma univia_i_type_system {o} :
  forall i, @type_system o nuprla_ex_inh (univia_i i).
Proof.
  introv; split; dands; eauto 3 with slow.

Qed.
Hint Resolve univia_i_type_system : slow.

Lemma nuprli_type_system {o} :
  forall (i : nat), @type_system o nuprla_ex_inh (nuprli i).
Proof.
  unfold nuprli; sp.
  apply close_type_system; eauto 3 with slow.

Qed.
Hint Resolve nuprli_type_system : slow.

Lemma nuprli_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    nuprli i1 lib T T' eq
    -> nuprli i2 lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  sp.
  assert (nuprli (i2 + i1) lib T T' eq) as c1 by (apply typable_in_higher_univ; auto).
  assert (nuprli (i1 + i2) lib T T' eq') as c2 by (apply typable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@nuprli_type_system o (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  eapply u; eauto.
Qed.

Lemma nuprli_type_transitive {o} :
  forall lib i1 i2 (T1 T2 T3 : @CTerm o) eq,
    nuprli i1 lib T1 T2 eq
    -> nuprli i2 lib T2 T3 eq
    -> {i : nat & nuprli i lib T1 T3 eq # i1 <= i # i2 <= i}.
Proof.
  sp.
  assert (nuprli (i1 + i2) lib T1 T2 eq) as c1 by (apply typable_in_higher_univ_r; auto).
  assert (nuprli (i1 + i2) lib T2 T3 eq) as c2 by (apply typable_in_higher_univ; auto).
  exists (i1 + i2); sp; try omega.
  generalize (@nuprli_type_system o (i1 + i2)); intro nts.
  destruct nts; sp.
  apply p2 with (T2 := T2); sp.
Qed.

Lemma univi_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    univi i1 lib T T' eq
    -> univi i2 lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  introv u v.
  assert (univi (i2 + i1) lib T T' eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi (i1 + i2) lib T T' eq') as c2 by (apply uni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  eapply uniquely_valued_univi; eauto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

 *)

Lemma type_symmetric_univ_ex {o} :
  @type_symmetric o univ_ex.
Proof.
  introv u.
  unfold univ_ex in *; exrepnd.
  exists i.
  apply type_symmetric_univi; auto.
Qed.
Hint Resolve type_symmetric_univ_ex : slow.

Lemma type_transitive_univ_ex {o} :
  @type_transitive o univ_ex.
Proof.
  introv u v.
  unfold univ_ex in *; exrepnd.
  assert (univi (i + i0) lib T1 T2 eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi (i0 + i) lib T2 T3 eq) as c2 by (apply uni_in_higher_univ; auto).
  assert (i + i0 = i0 + i) as e by omega.
  rewrite e in c1; clear e.

  exists (i0 + i).
  eapply type_transitive_univi; eauto.
Qed.
Hint Resolve type_transitive_univ_ex : slow.

Lemma type_value_respecting_univ_ex {o} :
  @type_value_respecting o univ_ex.
Proof.
  introv u.
  unfold univ_ex in *; exrepnd.
  exists i.
  apply type_value_respecting_univi; auto.
Qed.
Hint Resolve type_value_respecting_univ_ex : slow.

Lemma term_symmetric_univ {o} :
  @term_symmetric o univ.
Proof.
  introv u e.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.
  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  apply close_type_symmetric; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_univ : slow.

Lemma term_transitive_univ {o} :
  @term_transitive o univ.
Proof.
  introv u e f.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_comb; try exact e; clear e.
  eapply in_open_bar_ext_pres; try exact f; clear f; introv f h u1.

  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1 in f; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_transitive; eauto; eauto 3 with slow.
  eapply close_type_extensionality; eauto 2 with slow.

  assert (close (univi_bar j) lib' t2 t2 eqa1) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) lib' t2 t2 eqa0) as h2.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  eapply close_uniquely_valued in h1; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_univ : slow.

Lemma term_value_respecting_univ {o} :
  @term_value_respecting o univ.
Proof.
  introv u e c.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.

  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_value_respecting; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_univ : slow.

Lemma univ_type_system {o} : @type_system o univ.
Proof.
  unfold type_system; dands; eauto 3 with slow.

  - eapply uniquely_valued_per_bar; eauto 3 with slow.

  - apply type_symmetric_per_bar; eauto 3 with slow.

  - apply type_transitive_per_bar; eauto 3 with slow.

  - apply type_value_respecting_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univ_type_system : slow.

(**

  Finally, we prove that that [nuprl] satisfies the type system properties.

*)

Lemma nuprl_type_system {p} : @type_system p nuprl.
Proof.
  introv.
  apply close_type_system; eauto 3 with slow.
Qed.
Hint Resolve nuprl_type_system : slow.

(* begin hide *)

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac nts :=
  match goal with
      [ p : POpid |- _ ] =>
      pose proof (@nuprl_type_system p) as nts;
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
  eapply uniquely_valued_eq; eauto.
Qed.

Lemma nuprl_uniquely_valued {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    nuprl lib t t eq1
    -> nuprl lib t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  introv n1 n2; nts.
  eapply nts_uv; eauto.
Qed.

Lemma nuprl_value_respecting_left {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq,
    nuprl lib t1 t2 eq
    -> ccequivc_ext lib t1 t3
    -> nuprl lib t3 t2 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; eapply nts_tyt; eauto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprl_value_respecting_right {p} :
  forall lib t1 t2 t3 eq,
    @nuprl p lib t1 t2 eq
    -> ccequivc_ext lib t2 t3
    -> nuprl lib t1 t3 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Ltac ntsi :=
  match goal with
    [ o : POpid , H : nuprli ?i _ _ _ _ |- _ ] =>
    pose proof (@nuprli_type_system o i) as nts;
    destruct nts as [ nts_uv nts ];
    destruct nts as [ nts_ext nts ];
    destruct nts as [ nts_tys nts ];
    destruct nts as [ nts_tyt nts ];
    destruct nts as [ nts_tyv nts ];
    destruct nts as [ nts_tes nts ];
    destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprli_value_respecting_left {o} :
  forall i lib (t1 t2 t3 : @CTerm o) eq,
    nuprli i lib t1 t2 eq
    -> ccequivc_ext lib t1 t3
    -> nuprli i lib t3 t2 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli i lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; eapply nts_tyt; eauto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprli_value_respecting_right {o} :
  forall i lib (t1 t2 t3 : @CTerm o) eq,
    nuprli i lib t1 t2 eq
    -> ccequivc_ext lib t2 t3
    -> nuprli i lib t1 t3 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli i lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Lemma in_ext_ext_nuprli_value_respecting_left {o} :
  forall i lib (t1 t2 t3 : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprli i lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t1 t3
    -> in_ext_ext lib (fun lib x => nuprli i lib t3 t2 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprli_value_respecting_right {o} :
  forall i lib (t1 t2 t3 : @CTerm o) eq,
    in_ext_ext lib (fun lib x => nuprli i lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t2 t3
    -> in_ext_ext lib (fun lib x => nuprli i lib t1 t3 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprli_value_respecting_left {o} :
  forall i lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v1] t1 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i lib (substc a v3 t3) (substc a' v2 t2) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprli_value_respecting_right {o} :
  forall i lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v2] t2 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i lib (substc a v1 t1) (substc a' v3 t3) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprl_value_respecting_left {o} :
  forall lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v1] t1 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl lib (substc a v3 t3) (substc a' v2 t2) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprl_value_respecting_right {o} :
  forall lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v2] t2 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl lib (substc a v1 t1) (substc a' v3 t3) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprl_value_respecting_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprl lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t1 t3
    -> in_ext_ext lib (fun lib x => nuprl lib t3 t2 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprl_value_respecting_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    in_ext_ext lib (fun lib x => nuprl lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t2 t3
    -> in_ext_ext lib (fun lib x => nuprl lib t1 t3 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma nuprl_eq_implies_eqorceq_refl {p} :
  forall lib T1 T2 eq t1 t2,
    @nuprl p lib T1 T2 eq
    -> eq t1 t2
    -> eqorceq lib eq t1 t1 # eqorceq lib eq t2 t2.
Proof.
  introv n e.
  nts; sp; left.

  { unfold term_transitive, term_equality_transitive in nts_tet.
    eapply nts_tet; eauto.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    eapply nts_tes; eauto. }

  { unfold term_transitive, term_equality_transitive in nts_tet.
    eapply nts_tet; eauto.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    eapply nts_tes; eauto. }
Qed.

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_respecting {o} :
  forall lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  eapply term_reduces_to_symm; eauto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_respecting : slow.

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_transitive {o} :
  forall lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  apply nts_tet in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_transitive : slow.

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_symmetric {o} :
  forall lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  apply nts_tes in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_symmetric : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_respecting {o} :
  forall i lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  eapply term_reduces_to_symm; eauto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_respecting : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_transitive {o} :
  forall i lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  apply nts_tet in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_transitive : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_symmetric {o} :
  forall i lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  apply nts_tes in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_symmetric : slow.

(* end hide *)
