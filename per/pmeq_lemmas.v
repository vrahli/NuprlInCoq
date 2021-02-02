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


Lemma pmeq_implies {o} :
  forall lib (eqp1 eqp2 : per(o)) eqa1 eqa2 eqb1 eqb2 cp ca cb C p,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> forall t1 t2,
         pmeq lib eqp1 eqa1 eqb1 cp ca cb C p t1 t2
         -> pmeq lib eqp2 eqa2 eqb2 cp ca cb C p t1 t2.
Proof.
  introv eqip eqia eqib pmeq1.
  revert dependent t2.
  revert dependent t1.
  revert dependent p.
  cofix MEQIH.
  introv meq1.
  destruct meq1 as [ ep a1 f1 a2 f2 ea c1 c2 I ].

  assert (eqp2 p p) as ep2 by (allrw <-; sp).

  assert (eqa2 p p ep2 a1 a2)
         as ea2
         by (generalize (eqia p p ep ep2 a1 a2); intro e; allrw <-; sp).

  apply @pmeq_cons
        with
        (ep := ep2)
        (a1 := a1)
        (f1 := f1)
        (a2 := a2)
        (f2 := f2)
        (ea := ea2);
    try (complete sp).

  introv eib.

  assert (eqb1 p p ep a1 a2 ea b1 b2)
         as eb1
         by (generalize (eqib p p ep ep2 a1 a2 ea ea2); intro e; allrw; sp).

  apply MEQIH.
  apply I; auto.
Qed.

Lemma pmeq_implies2 {o} :
  forall lib (eqp1 eqp2 : per(o)) eqa1 eqa2 eqb1 eqb2
         cp1 ca1 cb1 C1 p1
         cp2 ca2 cb2 C2 p2,
    term_equality_symmetric eqp1
    -> term_equality_transitive eqp1
    -> term_equality_symmetric_fam eqp1 eqa1
    -> term_equality_transitive_fam eqp1 eqa1
    -> term_equality_symmetric_fam_fam eqp1 eqa1 eqb1
    -> term_equality_transitive_fam_fam eqp1 eqa1 eqb1
    -> eq_fam_respects_eq_term_equals eqp1 eqa1
    -> eq_fam_fam_respects_eq_term_equals eqp1 eqa1 eqb1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> (forall (p p' : cterm) (ep : eqp1 p p')
               (a a' : cterm) (ea : eqa1 p p' ep a a')
               (b b' : cterm) (eb : eqb1 p p' ep a a' ea b b'),
          eqp1 (lsubstcn3 cp1 p ca1 a cb1 b C1)
               (lsubstcn3 cp2 p' ca2 a' cb2 b' C2))
    -> eqp1 p1 p2
    -> forall t1 t2,
         pmeq lib eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 p1 t1 t2
         -> pmeq lib eqp2 eqa2 eqb2 cp2 ca2 cb2 C2 p2 t1 t2.
Proof.
  introv tes tet tesa teta tesb tetb eqresa eqresb.
  introv eqip eqia eqib eCs eps pmeq1.

  revert dependent p2.
  revert dependent p1.
  revert dependent t2.
  revert dependent t1.

  cofix MEQIH.

  introv pmeq1; introv ep.

  destruct pmeq1 as [ ep' a1 f1 a2 f2 ea c1 c2 I ].

  assert (eqp1 p2 p2) as ep1 by (apply tet with (t2 := p1); sp).
  assert (eqp2 p2 p2) as ep2 by (rw <- eqip; sp).

  assert (eqa1 p2 p2 ep1 a1 a2)
    as ea1
      by (generalize (eqia p2 p2 ep1 ep2 a1 a2); intro e; allrw <-; sp;
          generalize (eqresa p1 p2 p1 p2 ep' ep1 ep ep); intro eqt;
          rw <- eqt; sp).

  assert (eqa2 p2 p2 ep2 a1 a2)
    as ea2
      by (generalize (eqia p2 p2 ep1 ep2 a1 a2); intro e; allrw <-; sp).

  apply @pmeq_cons
        with
        (ep := ep2)
        (a1 := a1)
        (f1 := f1)
        (a2 := a2)
        (f2 := f2)
        (ea := ea2);
    try (complete sp).

  introv eib.

  assert (eqb1 p2 p2 ep1 a1 a2 ea1 b1 b2)
         as eb1
         by (generalize (eqib p2 p2 ep1 ep2 a1 a2 ea1 ea2); intro e; allrw; sp).

  assert (eqa1 p1 p2 ep a1 a1)
    as e1
      by (generalize (eqresa p1 p1 p1 p2 ep' ep ep' ep); introv k;
          rw <- k; clear k;
          generalize (tesa p1 p1 ep'); intro k1;
          generalize (teta p1 p1 ep'); intro k2;
          apply k2 with (t2 := a2); sp).

  assert (eqa1 p1 p2 ep a2 a2)
    as e2
      by (generalize (eqresa p1 p1 p1 p2 ep' ep ep' ep); introv k;
          rw <- k; clear k;
          generalize (tesa p1 p1 ep'); intro k1;
          generalize (teta p1 p1 ep'); intro k2;
          apply k2 with (t2 := a1); sp).

  generalize (eqresb p1 p2 p1 p2 ep' ep1 a1 a1 a2 a2 ea ea1 ep ep e1 e2).
  introv eqt.
  rw <- eqt in eb1.

  apply MEQIH with (p1 := lsubstcn3 cp1 p1 ca1 a1 cb1 b1 C1).
  apply I; auto.

  assert (eqa1 p1 p2 ep a1 a1)
    as ea3
      by (generalize (eqresa p1 p1 p1 p2 ep' ep ep' ep); introv k;
          rw <- k; clear k;
          generalize (tesa p1 p1 ep'); introv k1;
          generalize (teta p1 p1 ep'); introv k2;
          apply k2 with (t2 := a2); sp).

  assert (eqa1 p1 p1 ep' a1 a1)
    as e3
      by (generalize (tesa p1 p1 ep'); introv k1;
          generalize (teta p1 p1 ep'); introv k2;
          apply k2 with (t2 := a2); sp).

  assert (eqa1 p1 p2 ep a1 a2)
    as e4 by (generalize (eqresa p1 p1 p1 p2 ep' ep ep' ep); introv k; rw <- k; sp).

  assert (eqa1 p1 p2 ep a2 a1)
    as e5 by (generalize (tesa p1 p2 ep); sp).

  assert (eqb1 p1 p2 ep a1 a1 ea3 b1 b1)
    as eb3
      by (generalize (eqresb p1 p1 p1 p2 ep' ep a1 a1 a2 a1 ea ea3 ep' ep e3 e5);
          intro k; rw <- k;
          generalize (tesb p1 p1 ep' a1 a2 ea); intro k1;
          generalize (tetb p1 p1 ep' a1 a2 ea); intro k2;
          apply k2 with (t2 := b2); sp).

  apply eCs with (ep := ep) (ea := ea3); auto.
Qed.

Lemma eq_term_equals_pmeq {o} :
  forall lib (eqp1 eqp2 : per(o)) eqa1 eqa2 eqb1 eqb2 cp ca cb C p,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> eq_term_equals (pmeq lib eqp1 eqa1 eqb1 cp ca cb C p)
                      (pmeq lib eqp2 eqa2 eqb2 cp ca cb C p).
Proof.
  introv eqip eqia eqib.
  unfold eq_term_equals; introv; split; intro k.
  apply @pmeq_implies with (eqp1 := eqp1) (eqa1 := eqa1) (eqb1 := eqb1); sp.

  apply @pmeq_implies with (eqp1 := eqp2) (eqa1 := eqa2) (eqb1 := eqb2); sp;
  try (apply eq_term_equals_fam_fam_sym; sp);
  try (apply eq_term_equals_fam_sym; sp);
  try (apply eq_term_equals_sym; sp).
Qed.

Lemma eq_term_equals_pmeq2 {o} :
  forall lib (eqp1 eqp2 : per(o)) eqa1 eqa2 eqb1 eqb2
         cp1 ca1 cb1 C1 p1
         cp2 ca2 cb2 C2 p2,
    term_equality_symmetric eqp1
    -> term_equality_transitive eqp1
    -> term_equality_symmetric_fam eqp1 eqa1
    -> term_equality_transitive_fam eqp1 eqa1
    -> term_equality_symmetric_fam_fam eqp1 eqa1 eqb1
    -> term_equality_transitive_fam_fam eqp1 eqa1 eqb1
    -> eq_fam_respects_eq_term_equals eqp1 eqa1
    -> eq_fam_fam_respects_eq_term_equals eqp1 eqa1 eqb1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp2 ca2 cb2 C2
    -> eqp1 p1 p2
    -> eq_term_equals (pmeq lib eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 p1)
                      (pmeq lib eqp2 eqa2 eqb2 cp2 ca2 cb2 C2 p2).
Proof.
  introv tesp tetp tesa teta tesb tetb repeqa respeqb.
  introv eqtp eqta eqtb eqCs eqps.
  unfold eq_term_equals; introv; split; intro e.

  apply @pmeq_implies2 with (eqp1 := eqp1) (eqa1 := eqa1) (eqb1 := eqb1) (cp1 := cp1) (ca1 := ca1) (cb1 := cb1) (C1 := C1) (p1 := p1); auto.

  apply @pmeq_implies2 with (eqp1 := eqp2) (eqa1 := eqa2) (eqb1 := eqb2) (cp1 := cp2) (ca1 := ca2) (cb1 := cb2) (C1 := C2) (p1 := p2);
    sp;
    try (apply eq_term_equals_fam_fam_sym; sp);
    try (apply eq_term_equals_fam_sym; sp);
    try (apply eq_term_equals_sym; sp).

  apply term_equality_symmetric_eq_term_equals with (eq := eqp1); sp.
  apply term_equality_transitive_eq_term_equals with (eq := eqp1); sp.

  apply @term_equality_symmetric_fam_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1); sp.
  apply @term_equality_transitive_fam_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1); sp.

  apply @term_equality_symmetric_fam_fam_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1) (eqb1 := eqb1); sp.
  apply @term_equality_transitive_fam_fam_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1) (eqb1 := eqb1); sp.

  apply @eq_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1); sp.
  apply @eq_fam_fam_respects_eq_term_equals_eq_term_equals with (eqp1 := eqp1) (eqa1 := eqa1) (eqb1 := eqb1); sp.

  apply eqtp.
  apply tesp.
  dup ep as ep1.
  apply eqtp in ep1.
  dup ep1 as ep1'.
  apply tesp in ep1'.

  generalize (eq_fam_sym_if_respects_eq eqp1 eqa1 repeqa); intro syma.
  generalize (syma p p' ep1 ep1'); introv eqt.
  dup ea as ea'.
  apply (eqta p p' ep1 ep) in ea'.
  dup ea' as ea1.
  apply eqt in ea'; clear eqt.
  apply (tesa p' p ep1') in ea'.

  apply eqCs with (ep := ep1') (ea := ea').

  generalize (eq_fam_fam_sym_if_respects_eq eqp1 eqa1 eqb1 respeqb); intro symb.
  generalize (symb p p' ep1 ep1' a a' ea1 ea'); intro eq.
  apply eq; clear eq.
  generalize (eqtb p p' ep1 ep a a' ea1 ea); intro eq.
  apply eq in eb.
  apply (tesb p p' ep1 a a' ea1); auto.

  apply eqtp.
  apply tesp; auto.
Qed.

Lemma pmeq_sym {o} :
  forall lib (eqp : per(o)) eqa eqb t1 t2 P1 P2 v1 v2 A1 A2
    bp1 ba1 bp2 ba2 B1 B2 ts p ca cb cp C cp' ca' cb' C',
    term_equality_symmetric eqp
    -> term_equality_transitive eqp
    -> type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp v1 A1 v2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> pmeq lib eqp eqa eqb cp ca cb C p t1 t2
    -> pmeq lib eqp eqa eqb cp ca cb C p t2 t1.
Proof.
  introv teqsp teqtp tsp ftsp fftsp eqCs Hweq.

  revert dependent p.
  revert dependent t2.
  revert dependent t1.

  cofix MEQIH.

  introv pmeq1.

  destruct pmeq1 as [ eqps a1 f1 a2 f2 eqpa c1 c2 Hie ].

  dup ftsp as tspa.
  repnud ftsp.
  (* generalize (eq_term_equals_sym_tsp2 ts eqp eqa v1 A1 v2 A2). introv Hyp.
    dimp Hyp ;eauto. rename hyp into Hsyma. exrepnd. clear Hyp. *)
  specialize (ftsp _ _ eqps).
  dup fftsp as tspb.
  repnud fftsp.
  specialize (fftsp _ _ eqps _ _ eqpa).
  dtsprops ftsp. duplicate eqpa as eqpas.
  apply ftsptes in eqpa.
  eapply @pmeq_cons with  (a2:=a1) (a1:=a2) (f1 := f2)  (f2 := f1)
    (ep:=eqps) (ea := eqpa); eauto.
  introv Heqb.
  assert (eq_term_equals
            (eqb p p eqps a2 a1 eqpa)
            (eqb p p eqps a1 a2 eqpas))
    as XX by (apply type_sys_props_fam_fam_implies_eq_fam_fam_sym with (P := P1) (P' := P2) (ap := v1) (A := A1) (ap' := v2) (A' := A2) in tspb; sp).
  apply XX in Heqb.
(*  clear ftspuv ftsptys ftsptyt ftsptyst ftsptyvr
    ftsptes ftsptet ftsptevr ftsptygs ftsptygt.*)
  dtsprops fftsp.
  dup Heqb as eqbs.
  apply fftsptes in Heqb.
  apply Hie in Heqb. clear XX.
  apply MEQIH.
  apply pmeq_implies2 with (eqp1 := eqp)
                             (eqa1 := eqa)
                             (eqb1 := eqb)
                             (cp1 := cp)
                             (ca1 := ca)
                             (cb1 := cb)
                             (C1 := C)
                             (p1 := lsubstcn3 cp p ca a1 cb b2 C);
    auto.
  apply type_sys_props_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) in tspa; sp.
  apply type_sys_props_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) in tspa; sp.
  apply type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) (ap := v1) (A := A1) (ap' := v2) (A' := A2) in tspb; sp.
  apply type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) (ap := v1) (A := A1) (ap' := v2) (A' := A2) in tspb; sp.
  apply type_sys_props_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) in tspa; sp.
  apply type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) (ap := v1) (A := A1) (ap' := v2) (A' := A2) in tspb; sp.
  apply eq_term_equals_fam_refl in tspa; sp.
  apply eq_term_equals_fam_fam_refl in tspb; sp.
  rw @fold_equal_Cparams.
  eapply equal_Cparams_refl; eauto.
  eapply equal_Cparams_refl in eqCs; eauto.
Qed.

Lemma pmeq_cequivc {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa bp ba B bp' ba' B' eqb
         cp ca cb C p t t1 t2,
    type_sys_props lib (close lib ts) P P' eqp
    -> type_sys_props_fam lib (close lib ts) eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib (close lib ts) eqp eqa bp ba B bp' ba' B' eqb
    -> pmeq lib eqp eqa eqb cp ca cb C p t t1
    -> cequivcn lib t1 t2
    -> pmeq lib eqp eqa eqb cp ca cb C p t t2.
Proof.
  introv tspp tspa tspb pw ceq.

  revert dependent p.
  revert dependent t2.
  revert dependent t1.
  revert dependent t.

  cofix MEQIH.

  introv ceq pmeq1.

  destruct pmeq1 as [ ep a1 f1 a2 f2 ea c1 c2 I ].

  spcast.

  generalize (cequivcn_mkcn_sup lib t1 t2 a2 f2 c2 ceq); intros c; exrepnd.
  rename a' into a.
  rename  b' into f.

  assert (eqa p p ep a1 a1)
    as ea1
      by (generalize (tspa p p ep); intro tsp;
          onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
          apply tet with (t2 := a2); sp).

  assert (eqa p p ep a1 a)
    as ea'
      by (generalize (tspa p p ep); intro tsp;
          onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
          apply tet with (t2 := a2); sp;
          generalize (tevr a2 a); intro k;
          repeat (autodimp k hyp); try (complete (spcast; sp));
          apply tet with (t2 := a1); sp).

  apply @pmeq_cons with (ep := ep) (a1 := a1) (f1 := f1) (a2 := a) (f2 := f) (ea := ea');
    try (complete (spcast; sp)).
  introv eb.
  apply MEQIH with (t1 := mkcn_apply f2 b2).

  apply sp_implies_cequivcn_apply; sp.

  apply I with (b2 := b2); sp.

  applydup @tsp_implies_eq_fam_fam_refl_left in tspb as rl.
  generalize (rl p p ep ep a1 a ea' ea1); intro e1.
  generalize (rl p p ep ep a1 a2 ea ea1); intro e2.
  apply e2.
  apply e1 in eb; auto.
Qed.

Lemma pmeq_implies_param {o} :
  forall lib (ts : cts(o)) eqp eqa eqb
         P P' ap A ap' A' bp ba B bp' ba' B'
         cp ca cb C cp' ca' cb' C'
         p1 p2 t1 t2,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> pmeq lib eqp eqa eqb cp ca cb C p1 t1 t2
    -> eqp p1 p2
    -> pmeq lib eqp eqa eqb cp ca cb C p2 t1 t2.
Proof.
  introv tspp tspa tspb eqCs pw eps.

  revert dependent p2.
  revert dependent p1.
  revert dependent t2.
  revert dependent t1.

  cofix MEQIH.

  introv pmeq1 eps.

  destruct pmeq1 as [ ep a1 f1 a2 f2 ea c1 c2 I ].

  assert (eqp p2 p2) as ep2 by (generalize (tsp_refl_right lib ts P P' eqp p1 p2 tspp eps); sp).

  assert (eqa p2 p2 ep2 a1 a2)
         as ea2
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             generalize (tspa p1 p2 p1 p2 ep ep2 eps eps); intro e;
             apply e; auto).

  apply @pmeq_cons with (ep := ep2) (a1 := a1) (f1 := f1) (a2 := a2) (f2 := f2) (ea := ea2);
    try (complete (spcast; sp)).

  introv eb.

  assert (eqa p1 p2 eps a1 a1)
         as ea'
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             generalize (tspa p1 p2 p2 p2 eps ep2 eps ep2); intro e;
             apply e;
             apply tspa1 with (t2 := a2); sp;
             apply tspa0; sp).

  assert (eqa p1 p2 eps a2 a2)
         as ea''
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             generalize (tspa p1 p2 p2 p2 eps ep2 eps ep2); intro e;
             apply e;
             apply tspa1 with (t2 := a1); sp;
             apply tspa0; sp).

  apply MEQIH with (p1 := lsubstcn3 cp p1 ca a1 cb b1 C).
  apply I; auto.

  apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspb; sp.
  generalize (tspb p1 p2 p1 p2 ep ep2 a1 a1 a2 a2 ea ea2 eps eps ea' ea''); intro e.
  apply e; sp.

  assert (eqp p2 p1) as ep' by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym; sp).

  assert (eqa p2 p1 ep' a1 a1)
         as ea3
         by (apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspa; auto;
             generalize (tspa p1 p2 eps ep'); intro e; apply e; sp).

  assert (eqa p2 p2 ep2 a2 a1)
         as ea4
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             apply tspa0; sp).

  assert (eqa p2 p2 ep2 a1 a1)
         as ea5
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             apply tspa1 with (t2 := a2); apply tspa0; sp).

  assert (eqb p1 p2 eps a1 a1 ea' b1 b1)
         as eb'
         by (apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspb; sp;
             generalize (tspb p2 p1 p2 p2 ep2 eps a1 a1 a2 a1 ea2 ea' ep' ep2 ea3 ea4); intro e;
             apply e; sp;
             apply tspb1 with (t2 := b2); sp;
             apply tspb0; sp).

  assert (eqb p2 p2 ep2 a1 a1 ea5 b1 b1)
         as eb''
         by (apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspb; sp;
             generalize (tspb p2 p2 p2 p2 ep2 ep2 a1 a1 a1 a2 ea5 ea2 ep2 ep2 ea5 ea2); intro e;
             apply e; sp;
             apply tspb1 with (t2 := b2); sp;
             apply tspb0; sp).

  generalize (eqCs p1 p2 eps a1 a1 ea' b1 b1 eb'); intro e1.
  generalize (eqCs p2 p2 ep2 a1 a1 ea5 b1 b1 eb''); intro e2.

  applydup @type_sys_props_implies_term_eq_sym in tspp as sym.
  applydup @type_sys_props_implies_term_eq_trans in tspp as trans.
  apply trans with (t2 := lsubstcn3 cp' p2 ca' a1 cb' b1 C'); sp.
Qed.

Lemma pmeq_trans {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa bp ba B bp' ba' B' eqb
         cp ca cb C cp' ca' cb' C'
         p t1 t2 t3,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> pmeq lib eqp eqa eqb cp ca cb C p t1 t2
    -> pmeq lib eqp eqa eqb cp ca cb C p t2 t3
    -> pmeq lib eqp eqa eqb cp ca cb C p t1 t3.
Proof.
  introv tspp tspa tspb eqCs pw1 pw2.

  revert dependent p.
  revert dependent t3.
  revert dependent t2.
  revert dependent t1.

  cofix MEQIH.

  introv pmeq1 pmeq2.

  destruct pmeq1 as [ ep a1 f1 a2 f2 ea c1 c2 I ].
  inversion pmeq2 as [ ep' a2' f2' a3 f3 ea' c2' c3 R2 ].
  ccomputes_to_eqval.

  assert (eqa p p ep a1 a3)
         as ea2
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             generalize (tspa1 p p ep); intro trans;
             apply trans with (t2 := a2); auto;
             generalize (tspa p p p p ep ep' ep ep); intro e; apply e; auto).

  assert (eqa p p ep a1 a1)
         as ea1
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             generalize (tspa1 p p ep); intro trans;
             apply trans with (t2 := a3); auto;
             apply tspa0; auto).

  apply @pmeq_cons with (ep := ep) (a1 := a1) (f1 := f1) (a2 := a3) (f2 := f3) (ea := ea2);
    try (complete (spcast; sp)).

  introv eb.

  apply MEQIH with (t2 := mkcn_apply f2 b1); sp.
  apply I; try (complete sp).

  applydup @tsp_implies_eq_fam_fam_refl_left in tspb as k.
  generalize (k p p ep ep a1 a3 ea2 ea1); intro e1.
  apply e1 in eb.
  generalize (k p p ep ep a1 a2 ea ea1); intro e2.
  apply e2.
  apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspb; repnd; sp.
  apply tspb1 with (t2 := b2); sp.
  apply tspb0; sp.

  assert (eqa p p ep a3 a3)
         as ea''
         by (apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; auto; repnd;
             apply tspa1 with (t2 := a1); sp; apply tspa0; sp).

  assert (eqb p p ep' a2 a3 ea' b1 b2)
         as eb'
         by (applydup @tsp_implies_eq_fam_fam_refl_right in tspb as k;
             generalize (k p p ep' ep a2 a3 ea' ea''); intro e; apply e; clear e;
             generalize (k p p ep ep a1 a3 ea2 ea''); intro e; apply e in eb; clear e; auto).

  generalize (R2 b1 b2 eb'); intro pw.

  generalize (pmeq_implies_param
                lib ts eqp eqa eqb
                P P' ap A ap' A' bp ba B bp' ba' B'
                cp ca cb C cp' ca' cb' C'
                (lsubstcn3 cp p ca a2 cb b1 C)
                (lsubstcn3 cp p ca a1 cb b1 C)
                (mkcn_apply f2 b1) (mkcn_apply f3 b2));
    intro k; repeat (autodimp k hyp).

  generalize (equal_Cparams_refl
                lib ts eqp eqa eqb
                P P' ap A ap' A' bp ba B bp' ba' B'
                cp ca cb C cp' ca' cb' C');
    intro j; repeat (autodimp j hyp).

  applydup @type_sys_props_implies_term_eq_sym in tspp as sym.
  apply sym.
  generalize (j p p ep a1 a2 ea b1 b1); intro l; apply l.

  applydup @tsp_implies_eq_fam_fam_refl_left in tspb as k.
  generalize (k p p ep ep a1 a3 ea2 ea1); intro e1.
  apply e1 in eb.
  generalize (k p p ep ep a1 a2 ea ea1); intro e2.
  apply e2; sp.
  apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspb; repnd; sp.
  apply tspb1 with (t2 := b2); sp.
  apply tspb0; sp.
Qed.
