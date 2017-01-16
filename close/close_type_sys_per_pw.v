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


Require Export type_sys_pfam.
Require Import dest_close.
Require Import pweq_lemmas.


Lemma close_type_system_pw {o} :
  forall (lib : library)
         (ts : cts(o))
         (T T' : CTerm)
         (eq : per)
         (P P': CTerm)
         ap ap'
         A A'
         bp bp' ba ba'
         B B'
         cp cp' ca ca' cb cb'
         C C'
         p p'
         (eqp : per)
         (eqa : per-fam(eqp))
         (eqb : per-fam-fam(eqp,eqa)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pw P ap A bp ba B cp ca cb C p)
    -> computes_to_valc lib T' (mkc_pw P' ap' A' bp' ba' B' cp' ca' cb' C' p')
    -> close lib ts P P' eqp
    -> type_sys_props lib (close lib ts) P P' eqp
    -> (forall (p p' : CTerm) (ep : eqp p p'),
          close lib ts (substc p ap A) (substc p' ap' A') (eqa p p' ep))
    -> type_sys_props_fam lib (close lib ts) eqp ap A ap' A' eqa
    -> (forall (p p' : CTerm) (ep : eqp p p')
               (a a' : CTerm) (ea : eqa p p' ep a a'),
          close lib ts
                (lsubstc2 bp p ba a B)
                (lsubstc2 bp' p' ba' a' B')
                (eqb p p' ep a a' ea))
    -> type_sys_props_fam_fam lib (close lib ts) eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> eqp p p'
    -> (forall t t' : CTerm, eq t t' <=> pweq lib eqp eqa eqb cp ca cb C p t t')
    -> per_pw lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 clP tspP clA tspA clB tspB.
  introv eqc peq eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_pw".
    allunfold @per_pw; exrepd.
    allrw @fold_eq_term_equals.
    sp_pfam.

    generalize (type_pfamily_eq_term_equals
                  lib mkc_pw
                  (close lib ts) T T' T3
                  eqp1 eqa1 eqb1 cp ca cb C cp' ca' cb' C' p p'
                  eqp0 eqa0 eqb0 cp ca cb C cp2 ca2 cb2 C2 p p2
                  P ap A bp ba B cp ca cb C p
                  P' eqp
                  ap' A' eqa
                  bp' ba' B' eqb).
    introv k; repeat (autodimp k hyp); try (apply eq_type_pfamilies_mkc_pw).
    repnd; repeat subst.
    red_eqTs; repeat subst; GC.

    apply eq_term_equals_trans with (eq2 := pweq lib eqp1 eqa1 eqb1 cp ca cb C p); auto.
    apply eq_term_equals_trans with (eq2 := pweq lib eqp0 eqa0 eqb0 cp ca cb C p); auto.
    apply eq_term_equals_pweq; try (complete sp).
    apply eq_term_equals_sym; sp.


  + SCase "type_symmetric".
    repdors; subst; dclose_lr;
    apply CL_pw;
    clear per;
    allunfold @per_pw; exrepd;
    exists eqp0 eqa0 eqb0 p1 p2;
    exists cp1 cp2 ca1 ca2 cb1 cb2 C1 C2; sp;
    allrw <-; sp;
    apply eq_term_equals_trans with (eq2 := eq); sp;
    try (complete (apply eq_term_equals_sym; sp)).


  + SCase "type_value_respecting".
    repdors; subst; apply CL_pw; unfold per_pw.

    (* 1 *)
    generalize (cequivc_mkc_pw lib T T3 P ap A bp ba B cp ca cb C p c1); intro k.
    autodimp k hyp; exrepnd.

    generalize (type_pfamily_cequivc
                  lib mkc_pw (close lib ts) T T3 eqp eqa eqb
                  P ap A bp ba B cp ca cb C p
                  P'0 ap'0 A'0 bp'0 ba'0 B'0 cp'0 ca'0 cb'0 C'0 p'0
                  P' ap' A' bp' ba' B' cp' ca' cb' C' p');
      intro k; repeat (autodimp k hyp).
    exists eqp eqa eqb p p'0.
    exists cp cp'0 ca ca'0 cb cb'0 C C'0; dands; auto.

    (* 2 *)
    generalize (cequivc_mkc_pw lib T' T3 P' ap' A' bp' ba' B' cp' ca' cb' C' p' c2); intro k.
    autodimp k hyp; exrepnd.

    generalize (type_pfamily_cequivc
                  lib mkc_pw (close lib ts) T' T3 eqp eqa eqb
                  P' ap' A' bp' ba' B' cp' ca' cb' C' p'
                  P'0 ap'0 A'0 bp'0 ba'0 B'0 cp'0 ca'0 cb'0 C'0 p'0
                  P ap A bp ba B cp ca cb C p);
      intro k; repeat (autodimp k hyp).
    apply type_sys_props_sym; sp.
    apply @type_sys_props_fam_sym with (P := P) (P' := P'); sp.
    apply @type_sys_props_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A'); sp.
    apply equal_Cparams_sym; sp.
    apply type_sys_props_implies_term_eq_sym in tspP; sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_eq_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    applydup @type_sys_props_implies_term_eq_sym in tspP as sym; sp.

    exists eqp eqa eqb p' p'0.
    exists cp' cp'0 ca' ca'0 cb' cb'0 C' C'0; dands; auto.
    allrw @fold_eq_term_equals.
    apply eq_term_equals_trans with (eq2 := pweq lib eqp eqa eqb cp ca cb C p); auto.

    apply eq_term_equals_pweq2.

    apply type_sys_props_implies_term_eq_sym in tspP; auto.
    apply type_sys_props_implies_term_eq_trans in tspP; auto.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply eq_term_equals_refl.
    apply (eq_term_equals_fam_refl lib) with (ts := close lib ts) (ap1 := ap) (A1 := A) (ap2 := ap') (A2 := A'); sp.
    apply (eq_term_equals_fam_fam_refl lib) with (ts := close lib ts) (bp1 := bp) (ba1 := ba) (B1 := B) (bp2 := bp') (ba2 := ba') (B2 := B'); sp.
    auto.
    auto.


  + SCase "term_symmetric".
    repnud per.
    exrepnd.
    sp_pfam.
    generalize (type_pfamily_sym
                    lib mkc_pw (close lib ts) T T' eqp0 eqa0 eqb0
                    cp ca cb C
                    cp' ca' cb' C'
                    p p'
                    P ap A bp ba B cp ca cb C p
                    eqp eqa eqb
                    P' ap' A' bp' ba' B' cp' ca' cb' C'); introv k.
    repeat (autodimp k hyp);
      try (complete (apply eq_type_pfamilies_mkc_pw)).
    repnd; subst; red_eqTs; GC; subst.

    unfold term_equality_symmetric; introv Heq.

    dup tspP as tspp.
    dtsprops tspP.
    repnud tspPtes.
    apply eqiff in Heq.
    apply eqiff.

    eapply pweq_sym; eauto.


  + SCase "term_transitive".
    unfold term_equality_transitive; introv.
    repeat (rw eqiff); introv pw1 pw2.
    eapply pweq_trans; eauto.


  + SCase "term_value_respecting".
    introv.
    repeat (rw eqiff).
    introv e c; spcast.

    eapply pweq_cequivc; eauto.


  + SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr; clear per; apply CL_pw;
    allunfold @per_pw; exrepnd.

    (* 1 *)
    generalize (type_pfamily_sym
                  lib mkc_pw (close lib ts)
                  T T3 eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2
                  P ap A bp ba B cp ca cb C p
                  eqp eqa eqb
                  P' ap' A' bp' ba' B' cp' ca' cb' C'); intro k.
    repeat (autodimp k hyp); repnd; subst; red_eqTs; subst; GC.
    exists eqp0 eqa0 eqb0 p2 p1.
    exists cp2 cp1 ca2 ca1 cb2 cb1 C2 C1; dands; auto.

    apply eq_term_equals_trans with (eq2 := pweq lib eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 p1); auto.
    apply eq_term_equals_pweq2.

    apply @term_equality_symmetric_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_sym in tspP; auto.
    apply @term_equality_transitive_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_trans in tspP; auto.

    apply term_equality_symmetric_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply term_equality_transitive_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.

    apply term_equality_symmetric_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply term_equality_transitive_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply eq_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply eq_fam_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply eq_term_equals_refl.
    apply eq_term_equals_fam_trans with (eqp2 := eqp) (eqa2 := eqa); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_trans with (eqp2 := eqp) (eqa2 := eqa) (eqb2 := eqb); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_sym; sp.

    apply type_pfamily_implies_equal_Cparams in h1; sp.

    apply type_pfamily_implies_params in h1; sp.


    (* 2 *)
    generalize (type_pfamily_sym2
                  lib mkc_pw (close lib ts)
                  T3 T eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2
                  P ap A bp ba B cp ca cb C p
                  eqp eqa eqb
                  P' ap' A' bp' ba' B' cp' ca' cb' C'); intro k.
    repeat (autodimp k hyp); repnd; subst; red_eqTs; subst; GC.
    exists eqp0 eqa0 eqb0 p2 p1.
    exists cp2 cp1 ca2 ca1 cb2 cb1 C2 C1; dands; auto.

    apply eq_term_equals_trans with (eq2 := pweq lib eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 p1); auto.
    apply eq_term_equals_pweq2.

    apply @term_equality_symmetric_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_sym in tspP; auto.
    apply @term_equality_transitive_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_trans in tspP; auto.

    apply term_equality_symmetric_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply term_equality_transitive_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.

    apply term_equality_symmetric_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply term_equality_transitive_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply eq_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply eq_fam_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply eq_term_equals_refl.
    apply eq_term_equals_fam_trans with (eqp2 := eqp) (eqa2 := eqa); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_trans with (eqp2 := eqp) (eqa2 := eqa) (eqb2 := eqb); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_sym; sp.

    apply type_pfamily_implies_equal_Cparams in h1; sp.

    apply type_pfamily_implies_params in h1; sp.


  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; clear per; dclose_lr; allunfold @per_pw; exrepd; sp_pfam.

    (* 1 *)
    generalize (type_pfamily_trans2 lib
                  (close lib ts) T3 T T4 mkc_pw
                  eqp0 eqa0 eqb0
                  eqp1 eqa1 eqb1
                  eqp eqa eqb
                  P ap A bp ba B cp ca cb C p
                  P' ap' A' bp' ba' B' cp' ca' cb' C'
                  cp1 ca1 cb1 C1 p1
                  cp ca cb C p
                  cp3 ca3 cb3 C3 p3); intro k.
    repeat (autodimp k hyp); repnd.

    dands; apply CL_pw; unfold per_pw.

    (* 1 - 1 *)
    exists eqp0 eqa0 eqb0 p1 p3.
    exists cp1 cp3 ca1 ca3 cb1 cb3 C1 C3; auto.

    (* 1 - 2 *)
    exists eqp0 eqa0 eqb0 p1 p3.
    exists cp1 cp3 ca1 ca3 cb1 cb3 C1 C3; dands; auto.
    apply @eq_term_equals_trans with (eq2 := pweq lib eqp1 eqa1 eqb1 cp ca cb C p); auto.

    generalize (type_pfamily_sym2
                  lib mkc_pw (close lib ts) T3 T
                  eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 cp ca cb C p1 p
                  P ap A bp ba B cp ca cb C p
                  eqp eqa eqb
                  P' ap' A' bp' ba' B' cp' ca' cb' C'); intro j.
    repeat (autodimp j hyp); repnd; subst; GC; red_eqTs; subst; GC.

    generalize (type_pfamily_eq_term_equals
                  lib mkc_pw (close lib ts) T T3 T4
                  eqp0 eqa0 eqb0 cp ca cb C cp1 ca1 cb1 C1 p p1
                  eqp1 eqa1 eqb1 cp ca cb C cp3 ca3 cb3 C3 p p3
                  P ap A bp ba B cp ca cb C p
                  P' eqp
                  ap' A' eqa
                  bp' ba' B' eqb); intro l.
    repeat (autodimp l hyp); repnd; subst; GC; red_eqTs; subst; GC.
    apply eq_term_equals_pweq2.

    apply @term_equality_symmetric_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_sym in tspP; auto.
    apply @term_equality_transitive_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_trans in tspP; auto.

    apply @term_equality_symmetric_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @term_equality_transitive_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.

    apply @term_equality_symmetric_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @term_equality_transitive_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply @eq_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @eq_fam_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply @eq_term_equals_trans with (eq2 := eqp); sp.
    apply eq_term_equals_sym; sp.
    apply @eq_term_equals_fam_trans with (eqp2 := eqp) (eqa2 := eqa); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply @eq_term_equals_fam_fam_trans with (eqp2 := eqp) (eqa2 := eqa) (eqb2 := eqb); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_sym; sp.

    apply type_pfamily_implies_equal_Cparams in j; sp.
    apply @equal_Cparams_eq_term_equals with (eqp1 := eqp0) (eqa1 := eqa0) (eqb1 := eqb0); sp.

    apply type_pfamily_implies_params in j; sp.
    apply l11.
    apply j5; sp.


    (* 2 *)
    generalize (type_pfamily_trans2 lib
                  (close lib ts) T3 T' T4 mkc_pw
                  eqp0 eqa0 eqb0
                  eqp1 eqa1 eqb1
                  eqp eqa eqb
                  P' ap' A' bp' ba' B' cp' ca' cb' C' p'
                  P ap A bp ba B cp ca cb C
                  cp1 ca1 cb1 C1 p1
                  cp' ca' cb' C' p'
                  cp3 ca3 cb3 C3 p3); intro k.
    repeat (autodimp k hyp); repnd.
    apply type_sys_props_sym; sp.
    apply @type_sys_props_fam_sym with (P := P) (P' := P'); sp.
    apply @type_sys_props_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A'); sp.
    apply equal_Cparams_sym; sp.
    apply type_sys_props_implies_term_eq_sym in tspP; sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_eq_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    dands; apply CL_pw; unfold per_pw.

    (* 1 - 1 *)
    exists eqp0 eqa0 eqb0 p1 p3.
    exists cp1 cp3 ca1 ca3 cb1 cb3 C1 C3; auto.

    (* 1 - 2 *)
    exists eqp0 eqa0 eqb0 p1 p3.
    exists cp1 cp3 ca1 ca3 cb1 cb3 C1 C3; dands; auto.
    apply @eq_term_equals_trans with (eq2 := pweq lib eqp1 eqa1 eqb1 cp' ca' cb' C' p'); auto.

    generalize (type_pfamily_sym2
                  lib mkc_pw (close lib ts) T3 T'
                  eqp0 eqa0 eqb0 cp1 ca1 cb1 C1 cp' ca' cb' C' p1 p'
                  P' ap' A' bp' ba' B' cp' ca' cb' C' p'
                  eqp eqa eqb
                  P ap A bp ba B cp ca cb C); intro j.
    repeat (autodimp j hyp); repnd; subst; GC; red_eqTs; subst; GC.
    apply type_sys_props_sym; sp.
    apply @type_sys_props_fam_sym with (P := P) (P' := P'); sp.
    apply @type_sys_props_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A'); sp.
    apply equal_Cparams_sym; sp.
    apply type_sys_props_implies_term_eq_sym in tspP; sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspA; sp.
    apply @type_sys_props_fam_fam_implies_eq_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    generalize (type_pfamily_eq_term_equals
                  lib mkc_pw (close lib ts) T' T3 T4
                  eqp0 eqa0 eqb0 cp' ca' cb' C' cp1 ca1 cb1 C1 p' p1
                  eqp1 eqa1 eqb1 cp' ca' cb' C' cp3 ca3 cb3 C3 p' p3
                  P' ap' A' bp' ba' B' cp' ca' cb' C' p'
                  P eqp
                  ap A eqa
                  bp ba B eqb); intro l.
    repeat (autodimp l hyp); repnd; subst; GC; red_eqTs; subst; GC.
    apply type_sys_props_sym; sp.
    apply @type_sys_props_fam_sym with (P := P) (P' := P'); sp.
    apply @type_sys_props_fam_fam_sym with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A'); sp.

    apply eq_term_equals_pweq2.

    apply @term_equality_symmetric_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_sym in tspP; auto.
    apply @term_equality_transitive_eq_term_equals with (eq := eqp); auto.
    apply type_sys_props_implies_term_eq_trans in tspP; auto.

    apply @term_equality_symmetric_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @term_equality_transitive_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.

    apply @term_equality_symmetric_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.
    apply @term_equality_transitive_fam_fam_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply @eq_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa); sp.
    apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
    apply @eq_fam_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.
    apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.

    apply @eq_term_equals_trans with (eq2 := eqp); sp.
    apply eq_term_equals_sym; sp.
    apply @eq_term_equals_fam_trans with (eqp2 := eqp) (eqa2 := eqa); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply @eq_term_equals_fam_fam_trans with (eqp2 := eqp) (eqa2 := eqa) (eqb2 := eqb); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_fam_sym; sp.
    apply eq_term_equals_fam_fam_sym; sp.

    apply type_pfamily_implies_equal_Cparams in j; sp.
    apply @equal_Cparams_eq_term_equals with (eqp1 := eqp0) (eqa1 := eqa0) (eqb1 := eqb0); sp.

    apply type_pfamily_implies_params in j; sp.
    apply l11.
    apply j5; sp.
Qed.

