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


(*Require Export per_props.*)
Require Export per_props_cequiv.
Require Export per_props_function.
Require Export per_props_uni.


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


(* begin hide *)

Lemma member_equality {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 T
    -> member lib mkc_axiom (mkc_equality t1 t2 T).
Proof.
  unfold member, equality; sp.
  exists (fun (t t' : @CTerm p) => t ===>(lib) mkc_axiom
                      # t' ===>(lib) mkc_axiom
                      # eq t1 t2);
    sp; spcast; try computes_to_value_refl.
  apply CL_eq.
  unfold per_eq.
  exists T T t1 t2 t1 t2 eq; sp; spcast; try computes_to_value_refl.
  unfold eqindomain; auto.
  unfold eqindomain; auto.
Qed.

(* end hide *)

(**

  Using the type definitions we can prove various useful equivalences
  that are true about the Nuprl type system [nuprl].  These
  equivalences provide characterizations of our types.  For example,
  we can prove that two terms [t1] and [t2] are equal in a type [T] if
  and only if the type [mkc_equality t1 t2 T] is inhabited by
  [mkc_axiom].  This equivalence shows the relations between the
  [equality] meta-relation and the [mkc_equality] type.

 *)

Lemma member_equality_iff {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 T
    <=> member lib mkc_axiom (mkc_equality t1 t2 T).
Proof.
  sp; split; intro e.
  apply member_equality; sp.
  allunfold @member; allunfold @equality; exrepnd.

  inversion e1; subst; try not_univ.

  allunfold_per.
  computes_to_value_isvalue.
  exists eqa; sp.
  discover; sp.
Qed.

(* begin hide *)

Lemma member_member_iff {p} :
  forall lib (t T : @CTerm p),
    member lib t T
    <=> member lib mkc_axiom (mkc_member t T).
Proof.
  sp; rewrite <- fold_mkc_member.
  apply member_equality_iff.
Qed.

Lemma if_member_vsubtype {p} :
  forall lib (A : @CTerm p) v B,
    member lib mkc_axiom (mkc_vsubtype A v B)
    -> forall x y, equality lib x y A -> equality lib x y B.
Proof.
  introv; rewrite <- fold_mkc_vsubtype; introv m e.
  apply member_member_iff in m.

  apply @if_member_function with (f := mkc_id)
                                  (v := v)
                                  (B := cvterm_var v B) in e; sp.


  apply equality_respects_cequivc_left with (t := x) in e;
    try (apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id).
  apply equality_respects_cequivc_right with (t := y) in e;
    try (apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id).

  rewrite substc_cvterm_var in e; sp.
Qed.

Lemma member_equality_is_axiom {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    -> a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom.
Proof.
  unfold equality, nuprl; introv e; exrepd.
  inversion c; subst; try not_univ.

  allunfold @per_eq; exrepnd.
  computes_to_value_isvalue.
  discover; sp.
Qed.

Lemma cequivc_eqindomain {p} :
  forall lib,
  forall(a b : @CTerm p),
  forall (eqa: per),
  term_equality_symmetric eqa ->
  term_equality_transitive eqa ->
  term_equality_respecting lib eqa ->
  cequivc lib a b -> eqindomain eqa a b.
Proof.  intros. unfold eqindomain.
 unfold term_equality_symmetric in H.
 unfold term_equality_transitive in H0.
 unfold term_equality_respecting in H1.
 split; try split; intro.
 assert (eqa a b). apply H1; auto. sp. spcast. auto.
 assert (eqa b a). apply H; auto. eapply H0; eauto.
 assert (eqa b a). apply H1; auto. sp. spcast. apply cequivc_sym. auto.
 assert (eqa a b). apply H; auto. eapply H0; eauto.
 apply H1; auto. sp. spcast. auto.
Qed.

Lemma tequality_equality_if_cequivc {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> tequality lib (mkc_equality t1 t2 A)
                 (mkc_equality t3 t4 B).
Proof.
  unfold tequality, equality; sp.
  exists (fun a b : @CTerm p =>
            a ===>(lib) mkc_axiom
            # b ===>(lib) mkc_axiom
            # eq t3 t4).
  unfold nuprl.
  apply CL_eq; unfold per_eq.
  exists A B t1 t2 t3 t4 eq.
  
  nts.
  assert (term_equality_symmetric eq). eapply nts_tes; eauto.
  assert (term_equality_transitive eq). eapply nts_tet; eauto.
  assert (term_equality_respecting lib eq). eapply nts_tev; eauto.
  sp; spcast;
  try (apply computes_to_valc_refl);
  try (apply iscvalue_mkc_equality; auto).
  apply (cequivc_eqindomain lib); auto.
  apply (cequivc_eqindomain lib); auto.
  
  split; sp; spcast.
  
  pose proof (eqindomain_commutes_nuprl lib t3 t1 t4 t2 eq A B) as xx; apply xx; auto;
  try (apply (cequivc_eqindomain lib); auto);
  try (apply (cequivc_sym lib); auto).
  assert (eq t1 t3).
  eapply nts_tev; eauto; spcast; auto.
  assert (eq t2 t4).
  eapply nts_tev; eauto; spcast; auto.

 eapply H1; eauto.
Qed.

Lemma eq_term_equals_eqindomain {p} :
  
  forall (eq1 eq2: per),
  eq1 <=2=> eq2 ->
  forall(a b : @CTerm p),
  eqindomain eq1 a b <=> eqindomain eq2 a b.
Proof.  intros. unfold eqindomain.
 repeat (rw H). sp.
 
Qed.


Lemma nuprl_eqindomain_iff {p} :
  forall lib (A B : @CTerm p),
  forall (eqa : per),
   nuprl lib A B eqa ->
  forall (a b : @CTerm p),
    eqindomain eqa a b <=>
   (member lib a A <=> member lib b A)
    # (member lib a A -> equality lib a b A).
Proof. intros. split; intro.

  - unfold member. unfold equality. split; try split; intro e; exrepnd;
    assert (eq_term_equals eq eqa) as etq by
    (apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := B);
            sp; nts; sp); apply nuprl_refl in H; unfold eqindomain in H0;
    exists eqa; sp; rw etq in e0; try (apply H1; auto). apply H0; auto.
        
 - unfold eqindomain; split; try split; intro e; exrepnd; dup H as H2; apply nuprl_refl in H.
   + assert (member lib a A). exists eqa; sp. apply H1 in H3. 
     unfold member in H3. unfold equality in H3. exrepnd. 
    assert (eq_term_equals eq eqa) as etq
        by (apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := B);
            sp; nts; sp). apply etq; auto.
   + assert (member lib b A). exists eqa; sp. apply H1 in H3. 
     unfold member in H3. unfold equality in H3. exrepnd. 
    assert (eq_term_equals eq eqa) as etq
        by (apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := B);
            sp; nts; sp). apply etq; auto.
   + assert (member lib a A). exists eqa; sp. apply H0 in H3. 
     unfold member in H3. unfold equality in H3. exrepnd. 
    assert (eq_term_equals eq eqa) as etq
        by (apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := B);
            sp; nts; sp). apply etq; auto.
Qed.


Lemma tequality_mkc_equality_implies {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    ->
    (
      tequality lib A B
      # (equality lib a1 a2 A -> equality lib b1 b2 B)
      # (member lib a1 A <=> member lib b1 A)
      # (member lib a1 A -> equality lib a1 b1 A)
      # (member lib a2 A <=> member lib b2 A)
      # (member lib a2 A -> equality lib a2 b2 A)
    ).
Proof.
  unfold tequality; introv teq; exrepnd.
  inversion teq0; subst; try (not_univ).

  allunfold @per_eq; exrepnd.
  computes_to_value_isvalue.
  allfold @nuprl.
  pose proof (nuprl_eqindomain_iff lib A0 B0 eqa H3 a0 b0) as xx. apply xx in H4.
  pose proof (nuprl_eqindomain_iff lib A0 B0 eqa H3 a3 b3) as yy. apply yy in H5.
  sp.

  - exists eqa; sp.

  - assert (equality lib a0 b0 A0) as e1 by (apply H4; apply equality_refl in H; auto).
    assert (equality lib a3 b3 A0) as e2 by
      (apply H5; apply equality_sym in H; apply equality_refl in H; auto).
    apply equality_sym in e1.
    assert (equality lib b0 b3 A0) as e3 by 
       (apply equality_trans with (t2 := a0); auto;
       apply equality_trans with (t2 := a3); auto).
   pose proof (equality_eq1 lib B0 A0 b0 b3 eqa) as r1; apply r1. apply nuprl_sym; auto.
   pose proof (equality_eq1 lib A0 B0 b0 b3 eqa) as r2; apply r2 in e3; auto.
Qed.

Lemma tequality_mkc_equality_in_universe_true {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_equality a1 b1 (mkc_uni i)) (mkc_equality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> equality lib a2 b2 (mkc_uni i).
Proof.
  introv t e.
  allapply @tequality_mkc_equality_implies; sp.
Qed.

Lemma equality_in_universe {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_equality a1 b1 (mkc_uni i)) (mkc_equality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> tequality lib a2 b2.
Proof.
  introv t e.
  apply tequality_mkc_equality_in_universe_true in t; sp.
  apply @equality_in_uni with (i := i); sp.
Qed.



Lemma tequality_mkc_equality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (tequality lib A B
      # (member lib a1 A <=> member lib b1 A)
      # (member lib a1 A -> equality lib a1 b1 A)
      # (member lib a2 A <=> member lib b2 A)
      # (member lib a2 A -> equality lib a2 b2 A)
      ).
Proof. unfold member.
  introv; split; intro k.

  - assert (tequality lib A B
     # (equality lib a1 a2 A -> equality lib b1 b2 B)
       # (equality lib a1 a1 A <=> equality lib b1 b1 A)
         # (equality lib a1 a1 A -> equality lib a1 b1 A)
           # (equality lib a2 a2 A <=> equality lib b2 b2 A) # (equality lib a2 a2 A -> equality lib a2 b2 A)).
     apply tequality_mkc_equality_implies; auto.
     sp.

  - repnd. 
    allunfold @tequality; exrepnd.
    pose proof (nuprl_eqindomain_iff lib A B eq k4) as eqd.
    assert (nuprl lib A A eq) as n by (allapplydup @nuprl_refl; sp).

    exists (fun x y : @CTerm p => x ===>(lib) mkc_axiom
                       # y ===>(lib) mkc_axiom
                       # eq a1 a2).
    apply CL_eq; unfold per_eq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
     apply eqd; split; auto.
     apply eqd; split; auto.
   
Qed.



Lemma tequality_mkc_equality2 {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    (tequality lib A B
      #  equality lib a1 b1 A
      #  equality lib a2 b2 A
      )
    ->
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B).
Proof. intros. apply tequality_mkc_equality; sp; split; intro.
     - apply equality_sym in H1. apply equality_refl in H1; auto.
     - apply equality_refl in H1; auto.
     - apply equality_sym in H. apply equality_refl in H; auto.
     - apply equality_refl in H; auto.

Qed.



Lemma tequality_mkc_equality_if_equal {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib A B
    -> equality lib a1 b1 A
    -> equality lib a2 b2 A
    -> tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B).
Proof.
  introv teq e1 e2.
  rw @tequality_mkc_equality; dands; auto.
  split; intro e. 
  apply equality_trans with (t2 := a1); eauto with nequality.
  apply equality_trans with (t2 := b1); eauto with nequality.
  split; intro e.
  apply equality_trans with (t2 := a2); eauto with nequality.
  apply equality_trans with (t2 := b2); eauto with nequality.
Qed.



Lemma tequality_mkc_member {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_member a A) (mkc_member b B)
    <=>
    (tequality lib A B
      # (member lib a A <=> member lib b B)
      # (member lib a A -> equality lib a b A)
     ).
Proof.
  intros. repeat (rewrite <- fold_mkc_member). trw @tequality_mkc_equality.
   split; intros; assert (tequality lib A B); exrepnd; auto. 
  assert (forall x, member lib x A <=> member lib x B) as mm.
  intros. unfold member; split; intro e; eapply tequality_preserving_equality; eauto.
  apply tequality_sym; auto.
  sp; rw mm; auto. repeat (rw <- mm); auto.
  assert (forall x, member lib x A <=> member lib x B) as mm.
  intros. unfold member; split; intro e; eapply tequality_preserving_equality; eauto.
  apply tequality_sym; auto.
  sp; rw <- mm in H2; auto. 
  
Qed.

Lemma tequality_mkc_member_if_equal {p} :
  forall lib (a b A B : @CTerm p),
    
    (tequality lib A B
      #  equality lib a b A
     )
    -> tequality lib (mkc_member a A) (mkc_member b B) .
Proof.
  intros. repnd. repeat (rewrite <- fold_mkc_member). 
   apply tequality_mkc_equality_if_equal; auto. 
  
Qed.

Lemma tequality_mkc_member_if_cequivc {p} :
  forall lib (a b A B : @CTerm p),
    
    (tequality lib A B
      #  cequivc lib a b 
     )
    -> tequality lib (mkc_member a A) (mkc_member b B) .
Proof.
  intros. repnd. repeat (rewrite <- fold_mkc_member). 
   apply tequality_equality_if_cequivc; sp.  
  
Qed.



Lemma equality_commutes {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq.
  apply equality_trans with (t2 := a2); auto; repnd.
  apply teq. unfold member. apply equality_trans with (t2 := a1); auto.
  apply equality_sym; auto.
Qed.

Lemma equality_commutes2 {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq. repnd.
  apply teq2.
  unfold member. apply equality_trans with (t2 := a2); auto.
  apply equality_sym; auto.
Qed.

Lemma equality_commutes3 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
 introv teq eq.
  rw @tequality_mkc_equality in teq. repnd.
  apply teq2.
  unfold member. apply equality_trans with (t2 := a2); auto.
  apply equality_sym; auto.
Qed.

Lemma equality_commutes4 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof. introv teq eq.
  rw @tequality_mkc_equality in teq.
  apply equality_trans with (t2 := a2); auto; repnd.
  apply teq. unfold member. apply equality_trans with (t2 := a1); auto.
  apply equality_sym; auto.
  
Qed.

Lemma equality_commutes5 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a2 a4 T.
Proof. introv teq eq.
  rw @tequality_mkc_equality in teq. repnd.
  apply teq.
  unfold member. apply equality_trans with (t2 := a1); auto.
  apply equality_sym; auto.
Qed.

Lemma equality_in_mkc_equality {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    <=> (equality lib t1 t2 T
         # a ===>(lib) mkc_axiom
         # b ===>(lib) mkc_axiom).
Proof.
  introv; split; intro i.

  applydup @member_equality_is_axiom in i; repnd; sp.
  allunfold @equality; allunfold @nuprl; exrepnd.
  inversion i3; subst; try not_univ.
  allunfold @per_eq; exrepnd.
  computes_to_value_isvalue.
  exists eqa; sp.
  discover; sp.

  repnd.
  allunfold @equality; allunfold @nuprl; exrepnd.
  exists (fun t t' : @CTerm p => t ===>(lib) mkc_axiom
              # t' ===>(lib) mkc_axiom
              # eq t1 t2); sp.
  apply CL_eq.
  unfold per_eq.
  exists T T t1 t2 t1 t2 eq; sp; spcast;
  try (apply computes_to_valc_refl);
  try (apply iscvalue_mkc_equality; auto);
  pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp.
  unfold eqindomain; sp. unfold eqindomain; sp.
Qed.

Lemma tequality_mkc_equality_base_iff {p} :
  forall lib (t1 t2 t3 t4 : @CTerm p),
    tequality lib (mkc_equality t1 t2 mkc_base) (mkc_equality t3 t4 mkc_base)
    <=>
    (ccequivc lib t1 t3 # ccequivc lib t2 t4).
Proof.
  introv. rw (@tequality_mkc_equality p).
  split; intro k; repnd. 

  - split; apply equality_in_base; try (apply k2); try (apply k); apply member_base.
    
  - sp; try (apply equality_in_base_iff; auto); split; intro; apply member_base.
 
Qed.

Lemma tequality_equality_if_eqorceq {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> t1 ~=~(lib) t3 [+] equality lib t1 t3 A
    ->  t2 ~=~(lib) t4 [+] equality lib t2 t4 A
    -> tequality lib (mkc_equality t1 t2 A)
                 (mkc_equality t3 t4 B).
Proof.
  introv Ht H13 H24.
  apply tequality_mkc_equality.
  assert (cequivc lib t1 t3 -> (member lib t1 A <=> member lib t3 A)) as ceq1.
   intro e; split; intro m. eapply member_respects_cequivc; eauto. 
   apply cequivc_sym in e. eapply member_respects_cequivc; eauto. 
  assert (cequivc lib t2 t4 -> (member lib t2 A <=> member lib t4 A)) as ceq2.
   intro e; split; intro m. eapply member_respects_cequivc; eauto. 
   apply cequivc_sym in e. eapply member_respects_cequivc; eauto. 
  
  dorn H13; dorn H24; dands; auto; cpx; spcast; 
   try (complete (apply ceq1; auto)); try (complete (apply ceq2; auto));
   try (complete (intro; apply equality_respects_cequivc; auto));
   split; intro; eapply equality_refl; eauto; 
   try (apply equality_sym in H24; eauto);
   try (apply equality_sym in H13; eauto).

Qed.

Lemma tequality_mkc_member_base {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_member a mkc_base) (mkc_member b mkc_base)
    <=>
    ccequivc lib a b.
Proof.
  introv. repeat (rw <- (@fold_mkc_member p)).
  rw @tequality_mkc_equality_base_iff. split; intro e; repnd; auto.
  
Qed.

Lemma equality_on_closed_terms_is_a_type {p} :
  forall lib (A x y : @CTerm p), type lib A -> type lib (mkc_equality x y A).
Proof.
  introv ta.
  apply tequality_equality_if_cequivc; sp.
Qed.

Lemma type_mkc_equality {p} :
  forall lib (A x y : @CTerm p), type lib (mkc_equality x y A) <=> type lib A.
Proof.
  introv; split; intro k.
  rw @tequality_mkc_equality in k; sp.
  apply equality_on_closed_terms_is_a_type; sp.
Qed.

Lemma type_mkc_equality2 {p} :
  forall lib (A : @CTerm p), (forall x y, type lib (mkc_equality x y A)) <=> type lib A.
Proof.
  introv; split; intro k; introv.
  generalize (k mkc_axiom mkc_axiom); clear k; intro k.
  rw @tequality_mkc_equality in k; sp.
  apply equality_on_closed_terms_is_a_type; sp.
Qed.

Lemma inhabited_mkc_equality {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_equality x y A) <=> equality lib x y A.
Proof.
  introv; split; intro k.
  unfold inhabited_type in k; exrepnd.
  rw @equality_in_mkc_equality in k0; sp.
  exists (@mkc_axiom p).
  apply member_equality; sp.
Qed.

Lemma inhabited_type_mkc_equality_sym {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_equality x y A)
    -> inhabited_type lib (mkc_equality y x A).
Proof.
  introv inh.
  allrw @inhabited_mkc_equality.
  apply equality_sym; sp.
Qed.

Lemma inhabited_type_mkc_equality_trans {p} :
  forall lib (A x y z : @CTerm p),
    inhabited_type lib (mkc_equality x y A)
    -> inhabited_type lib (mkc_equality y z A)
    -> inhabited_type lib (mkc_equality x z A).
Proof.
  introv inh1 inh2.
  allrw @inhabited_mkc_equality.
  apply equality_trans with (t2 := y); sp.
Qed.

Lemma member_if_inhabited {p} :
  forall lib (t1 t2 t T : @CTerm p),
    equality lib t1 t2 (mkc_member t T)
    -> member lib t T.
Proof.
  introv; allrw <- @fold_mkc_member; unfold member, equality, nuprl; intro i; exrepnd.

  inversion i1; try not_univ.
  allunfold @per_eq; sp.
  computes_to_value_isvalue; subst.
  exists eqa; sp.
  subst; discover; sp.
Qed.



Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    -> member lib T1 (mkc_uni i)
    -> tequality lib T1 T2.
Proof.
  introv teq typ.
  rw @tequality_mkc_member in teq; repnd.
  eapply @equality_in_uni. eauto.
  
Qed.



Lemma iff_inhabited_type_if_tequality_mem {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i)) (mkc_member T2 (mkc_uni i))
    -> member lib T1 (mkc_uni i)
    -> (inhabited_type lib T1 <=> inhabited_type lib T2).
Proof.
  introv teq. introv inh.
   assert (tequality lib T1 T2). eapply tequality_in_uni_implies_tequality; eauto.
  
  split; intro v.
  apply inhabited_type_tequality with (a := T1); sp.
  apply inhabited_type_tequality with (a := T2); sp.
  apply tequality_sym; sp.
Qed.



Lemma equality_mkc_equality2_sp_in_uni {p} :
  forall lib i (a1 a2 b1 b2 A B : @CTerm p),
    equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i)
    <=>
    (
      equality lib A B (mkc_uni i)
      # (member lib a1 A <=> member lib b1 A)
      # (member lib a1 A -> equality lib a1 b1 A)
      # (member lib a2 A <=> member lib b2 A)
      # (member lib a2 A -> equality lib a2 b2 A)
    ).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv e.
    unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    allunfold @per_eq; exrepnd.
    computes_to_value_isvalue; GC.
    allfold (@nuprl p).
    allfold (@nuprli p lib j0).
    assert (nuprl lib A0 B0 eqa) as n by
      (allapply @nuprli_implies_nuprl;auto).
    pose proof (nuprl_eqindomain_iff lib A0 B0 eqa n) as eqd.
    apply eqd in H4.
    apply eqd in H5.
    dands; sp.

    exists eq; sp.
    allrw.
    exists eqa; sp.

   
  - Case "<-".
    intro e.
    destruct e as [e eo].
    destruct eo as [eo1 eo2].
    unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).
    assert (nuprl lib A B eqa) as n by (allapply @nuprli_implies_nuprl; auto).
    pose proof (nuprl_eqindomain_iff lib A B eqa n) as eqd.
    

    exists eq; sp.
    allrw.

    exists (fun t1 t2 : @CTerm p => (t1 ===>(lib) mkc_axiom # t2 ===>(lib) mkc_axiom # eqa a1 a2)).
    apply CL_eq; fold (@nuprli p lib j0).
    unfold per_eq.
    exists A B a1 a2 b1 b2 eqa; dands; auto;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_equality))).
    apply eqd; auto.
    apply eqd; auto.
Qed.



Lemma equality_in_member {p} :
  forall lib (a b t T : @CTerm p),
    equality lib a b (mkc_member t T)
    <=> ((a ===>(lib) mkc_axiom)
         # (b ===>(lib) mkc_axiom)
         # member lib t T).
Proof.
  introv.
  rw <- @fold_mkc_member.
  rw @equality_in_mkc_equality.
  split; sp.
Qed.

Lemma tequality_mkc_member_implies_sp {o} :
  forall lib (a b A B : @CTerm o),
    tequality lib (mkc_member a A) (mkc_member b B)
    -> member lib a A
    -> equality lib a b A.
Proof.
  introv teq mem.
  allrw @tequality_mkc_member; repnd. apply teq. auto.
Qed.

Lemma tequality_mkc_equality_sp_eq {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    equality lib a1 a2 A
    -> (tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
        <=> (tequality lib A B # equality lib a1 b1 A # equality lib a2 b2 A)).
Proof.
  introv eqa.
  split; intro h; repnd; dands; auto.
  - rw @tequality_mkc_equality in h; sp.
  - rw @tequality_mkc_equality in h; repnd.
    repndors; spcast; eauto 3 with nequality.
  - rw @tequality_mkc_equality in h; repnd.
    repndors; spcast; eauto 3 with nequality.
    apply h. unfold member. apply equality_trans with (t2 := a1); auto.
    apply equality_sym; auto.
    
  - apply tequality_mkc_equality; dands; auto; unfold member; split; intro e.
    + apply equality_trans with (t2 := a1); auto.  apply equality_sym; auto.
    + apply equality_trans with (t2 := b1); auto.  apply equality_sym; auto.
    + apply equality_trans with (t2 := a2); auto.  apply equality_sym; auto.
    + apply equality_trans with (t2 := b2); auto.  apply equality_sym; auto.
Qed.

(* end hide *)
