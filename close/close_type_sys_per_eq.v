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


Require Export type_sys.
Require Import dest_close.

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

Lemma eqindomain_sym {p} :
  forall(a b : @CTerm p),
  forall (eqa: per),
  term_equality_symmetric eqa ->
  eqindomain eqa a b -> eqindomain eqa b a.
Proof.  intros. unfold eqindomain.
 unfold term_equality_symmetric in H.
 split; try split; intro. apply H0; auto. apply H0; auto. 
 assert (eqa a b). apply H0; auto. apply H0; auto. apply H. auto.
 
Qed.

Lemma eqindomain_trans {p} :
  forall(a b c: @CTerm p),
  forall (eqa: per),
  term_equality_transitive eqa ->
  eqindomain eqa a b -> eqindomain eqa b c -> eqindomain eqa a c.
Proof.  unfold eqindomain. intros.
 unfold term_equality_symmetric in H. sp. rw H3; auto.
 assert (eqa b c). apply H1; rw <- H4; auto.
 eapply H; eauto.
Qed.

Lemma eqindomain_combine {p} :
  forall(a1 a2 b1 b2 : @CTerm p),
  forall (eqa: per),
  term_equality_symmetric eqa ->
  term_equality_transitive eqa ->
  eqindomain eqa a1 b1 -> eqindomain eqa a2 b2 -> eqa a1 a2 -> eqa b1 b2.
Proof.  intros. unfold eqindomain.
 unfold term_equality_symmetric in H.
 unfold term_equality_transitive in H0.
 assert (eqa a1 b1). apply H1. eapply H0; eauto.
 assert (eqa a2 b2). apply H2. eapply H0; eauto.
 eapply H0; eauto.
 
Qed.

Lemma eq_term_equals_eqindomain {p} :
  
  forall (eq1 eq2: per),
  eq1 <=2=> eq2 ->
  forall(a b : @CTerm p),
  eqindomain eq1 a b <=> eqindomain eq2 a b.
Proof.  intros. unfold eqindomain.
 repeat (rw H). sp.
 
Qed.





Lemma close_type_system_eq {p} :
  forall lib (ts : cts(p)),
  forall T T' (eq : per) A B a1 a2 b1 b2 eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_equality a1 a2 A)
    -> computes_to_valc lib T' (mkc_equality b1 b2 B)
    -> close lib ts A B eqa
    -> eqindomain eqa a1 b1
    -> eqindomain eqa a2 b2
    -> (forall t t' : CTerm,
          eq t t' <=>
             ccomputes_to_valc lib t mkc_axiom
             # ccomputes_to_valc lib t' mkc_axiom
             # eqa a1 a2)
    -> per_eq lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A B eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 eos1 eos2 eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_eq".
      clear per.
      allunfold @per_eq; sp.
      unfold eq_term_equals; sp.
      spcast; allrw.
      ccomputes_to_eqval.
      unfold type_sys_props in IHX1; sp.
      implies_ts_or_eq A B0 B h.
      apply IHX0 in h.
      unfold eq_term_equals in h.
      rw h; split; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    allunfold @per_eq; exrepd;
    ccomputes_to_eqval;
    apply CL_eq; unfold per_eq.

    (* 1 *)
    exists A B0 a1 a2 b0 b3 eqa0; sp; spcast; sp.
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_eq; allunfold @per_eq; sp;
    ccomputes_to_eqval.

    duplicate c1 as c0.
    apply cequivc_mkc_equality with (t' := T3) in c0; sp.
    exists A T'0 a1 a2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp)).
    allunfold @type_sys_props; sp.
    pose proof (cequivc_eqindomain lib a1 a' eqa). apply H0; auto; apply IHX1.
    pose proof (cequivc_eqindomain lib a2 b' eqa). apply H0; auto; apply IHX1.

    duplicate c2 as c0.
    apply cequivc_mkc_equality with (t' := T3) in c0; sp.
    exists B T'0 b1 b2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp)).
    allunfold @type_sys_props; sp.
    pose proof (cequivc_eqindomain lib b1 a' eqa). apply H0; auto; apply IHX1.
    pose proof (cequivc_eqindomain lib b2 b' eqa). apply H0; auto; apply IHX1.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    rw eqiff; split; sp. eapply eqindomain_combine; eauto.
    pose proof (eqindomain_combine b1 b2 a1 a2 eqa) as xx; apply xx; auto; apply eqindomain_sym; auto.

  + SCase "term_symmetric".
    unfold term_equality_symmetric; sp.
    allrw; discover; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    allrw; discover; sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    allrw; discover; sp; spcast.
    apply @cequivc_axiom with (t := t); sp.

  + SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_eq;
    clear per;
    allunfold @per_eq; exrepd;
    ccomputes_to_eqval;
    unfold per_eq;
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
    try (assert (close lib ts A A0 eqa0)
                as k by (generalize (tygs A A0 eqa0); intro i; autodimp i h; rw <- i in c3; sp));
    try (assert (close lib ts B A0 eqa0)
                as k by (generalize (tygs B A0 eqa0); intro i; autodimp i h; rw <- i in c3; sp));
    try (assert (eq_term_equals eqa eqa0)
                as eqt by (apply uv with (T3 := A0); sp));
    try (assert (eq_term_equals eqa eqa0)
                as eqt by (apply uv with (T3 := B0); sp)).
    

    (* 1 *)
    exists B0 A b0 b3 a1 a2 eqa0.
    assert (term_equality_symmetric eqa0).
     unfold term_equality_symmetric; intros; rw <- eqt; apply tes; rw eqt; auto.
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa0 a b) as sameeq.
    apply eq_term_equals_eqindomain; auto. 
    
    sp; spcast; sp.
    generalize (tygs A B0 eqa0); intro i; autodimp i h; rw <- i; sp.
    apply eqindomain_sym; auto.
    apply eqindomain_sym; auto.
   
    rw t; repeat (rw <- eqt).
    split; sp.
    pose proof (eqindomain_combine a1 a2 b0 b3 eqa) as xx; apply xx; auto;
    rw sameeq; auto.
    pose proof (eqindomain_combine b0 b3 a1 a2 eqa) as xx; apply xx; auto;
    apply eqindomain_sym; auto; rw sameeq; auto.
    
    (* 2 *)
    exists A A0 a1 a2 a0 a3 eqa0.
    assert (term_equality_symmetric eqa0).
     unfold term_equality_symmetric; intros; rw <- eqt; apply tes; rw eqt; auto. 
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa0 a b) as sameeq.
    apply eq_term_equals_eqindomain; auto. 
     sp; spcast; sp.
    apply eqindomain_sym; auto.
    apply eqindomain_sym; auto.

    rw t; repeat (rw <- eqt).
    split; sp.
    pose proof (eqindomain_combine a0 a3 a1 a2 eqa) as xx; apply xx; auto;
    rw sameeq; auto.
    pose proof (eqindomain_combine a1 a2 a0 a3 eqa) as xx; apply xx; auto;
    apply eqindomain_sym; auto; rw sameeq; auto.
    
  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_eq lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_eq lib (close lib ts) T' T4 eq2));

    clear per;
    allunfold @per_eq; exrepd;
    ccomputes_to_eqval;
    applydup @type_sys_props_ts_refl in IHX1; repnd;
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.

    (* 1 *)
    assert (close lib ts A A1 eqa1) as eqta1 by (generalize (tymt A A1 A eqa1 eqa); sp).
    assert (eq_term_equals eqa eqa1) as eqt1 by (apply uv with (T3 := A1); sp).
    assert (eq_term_equals eqa eqa0) as eqt2 by (apply uv with (T3 := B0); sp).
    assert (close lib ts A1 B0 eqa0) as eqta2 by (generalize (tymt A A1 B0 eqa1 eqa0); sp).
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa0 a b) as sameeq1.
    apply eq_term_equals_eqindomain; auto. 
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa1 a b) as sameeq2.
    apply eq_term_equals_eqindomain; auto. 

    
    dands; apply CL_eq; unfold per_eq.

    exists A1 B0 a4 a5 b0 b3 eqa0. 
    allrw <- sameeq1.
    allrw <- sameeq2.
    sp; spcast; sp.
    eapply eqindomain_trans; eauto.
    eapply eqindomain_trans; eauto.
    
    rw t0.
    allrw <-; sp.

    exists A1 B0 a4 a5 b0 b3 eqa0.
    allrw <- sameeq1.
    allrw <- sameeq2.
    sp; spcast; sp.
    eapply eqindomain_trans; eauto.
    eapply eqindomain_trans; eauto.
    
    rw t.
    allrw <-; sp.
  
    rw eqiff; split; intros; sp.
    pose proof (eqindomain_combine a1 a2 a4 a5 eqa) as xx; apply xx; auto;
    apply eqindomain_sym; auto.
    pose proof (eqindomain_combine a4 a5 a1 a2 eqa) as xx; apply xx; auto.

 

    (* 2 *)
    assert (close lib ts B A1 eqa1) as eqta1 by (generalize (tymt B A1 B eqa1 eqa); sp).
    assert (eq_term_equals eqa eqa1) as eqt1 by (apply uv with (T3 := A1); sp).
    assert (eq_term_equals eqa eqa0) as eqt2 by (apply uv with (T3 := B0); sp).
    assert (close lib ts A1 B0 eqa1) as cl by (generalize (tymt B A1 B0 eqa1 eqa0); intro i; autodimp i h; sp).
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa0 a b) as sameeq1.
    apply eq_term_equals_eqindomain; auto. 
    assert (forall a b : CTerm, eqindomain eqa a b <=> eqindomain eqa1 a b) as sameeq2.
    apply eq_term_equals_eqindomain; auto. 

    dands; apply CL_eq; unfold per_eq.

    exists A1 B0 a4 a5 b0 b3 eqa1.
    allrw <- sameeq1.
    allrw <- sameeq2.
    sp; spcast; sp.
    eapply eqindomain_trans; eauto.
    eapply eqindomain_trans; eauto.
    
    exists A1 B0 a4 a5 b0 b3 eqa1.
    allrw <- sameeq1.
    allrw <- sameeq2.
    sp; spcast; sp. 
    eapply eqindomain_trans; eauto.
    eapply eqindomain_trans; eauto.
    
    rw t; repeat (rw <- eqt1); repeat (rw <- eqt2); split; sp.
    pose proof (eqindomain_combine b1 b2 a4 a5 eqa) as xx; apply xx; auto;
    apply eqindomain_sym; auto.
    pose proof (eqindomain_combine a4 a5 b1 b2 eqa) as xx; apply xx; auto.

Qed.

