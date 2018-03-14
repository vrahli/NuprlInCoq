(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export type_sys_useful2.
Require Import tactics2.

(*
Lemma lblift_cequiv4 :
  forall a b c d bterms,
    lblift (olift cequiv) [nobnd a, nobnd b, nobnd c, nobnd d] bterms
    -> {a', b', c', d' : NTerm
        $ bterms = [nobnd a', nobnd b', nobnd c', nobnd d']
        # (olift cequiv) a a'
        # (olift cequiv) b b'
        # (olift cequiv) c c'
        # (olift cequiv) d d'}.
Proof.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold nobnd.
  repeat(alpharelbtd).
  eexists; eexists; eexists; eexists; dands.

; dands; eauto 10 with slow.
Qed.

Lemma lblift_cequiv5 :
  forall a b c d e bterms,
    lblift (olift cequiv) [nobnd a, nobnd b, nobnd c, nobnd d, nobnd e] bterms
    -> {a', b', c', d', e' : NTerm
        $ bterms = [nobnd a', nobnd b', nobnd c', nobnd d', nobnd e']
        # (olift cequiv) a a'
        # (olift cequiv) b b'
        # (olift cequiv) c c'
        # (olift cequiv) d d'
        # (olift cequiv) e e'}.
Proof.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold nobnd.
  repeat(alpharelbtd).
  eexists; eexists; eexists; eexists; eexists; dands; eauto 10 with slow.
Qed.
*)

Definition eqAs {p} (ap1 : NVar) (A1 : @CVTerm p [ap1])
                (ap2 : NVar) (A2 : @CVTerm p [ap2]) :=
  match eq_var_dec ap1 ap2 with
    | left e =>
        (match e in _ = v return CVTerm [v] with eq_refl => A1 end) = A2
    | _ => False
  end.

Lemma eq_var_dec_same :
  forall v, eq_var_dec v v = left eq_refl.
Proof.
  intros.
  destruct (eq_var_dec v v); sp.
  assert (e = eq_refl).
  apply UIP_dec.
  apply eq_var_dec.
  subst.
  auto.
Qed.

Definition eqBs {p} (bp1 ba1 : NVar) (B1 : @CVTerm p [bp1,ba1])
                (bp2 ba2 : NVar) (B2 : @CVTerm p [bp2,ba2]) :=
  match eq_var_dec bp1 bp2, eq_var_dec ba1 ba2 with
    | left e1, left e2 =>
        (match e1 in _ = v1 return CVTerm [v1,ba2] with
             eq_refl => match e2 in _ = v2 return CVTerm [_,v2] with eq_refl => B1 end
         end)
      = B2
    | _, _ => False
  end.

Definition eqCs {p} (cp1 ca1 cb1 : NVar) (C1 : @CVTerm p [cp1,ca1,cb1])
                (cp2 ca2 cb2 : NVar) (C2 : @CVTerm p [cp2,ca2,cb2]) :=
  match eq_var_dec cp1 cp2, eq_var_dec ca1 ca2, eq_var_dec cb1 cb2 with
    | left ep, left ea, left eb =>
        (match ep in _ = vp return CVTerm [vp,ca2,cb2] with
             eq_refl => match ea in _ = va return CVTerm [_,va,cb2] with
                            eq_refl => match eb in _ = vb return CVTerm [_,_,vb] with
                                           eq_refl => C1
                                       end
                        end
         end)
      = C2
    | _, _, _ => False
  end.

Ltac red_eqTs_step :=
  match goal with
    | [ |- eqAs ?a1 ?A1 ?a2 ?A2 ] =>
      destruct (eq_var_dec a1 a2);
        [ unfold eqAs;
          rewrite eq_var_dec_same;
          simpl;
          try (complete reflexivity)
        | complete sp
        ]

    | [ H : eqAs ?a1 ?A1 ?a2 ?A2 |- _ ] =>
      destruct (eq_var_dec a1 a2);
        [ unfold eqAs in H;
          rewrite eq_var_dec_same in H;
          simpl in H
        | complete sp
        ]

    | [ |- eqBs ?p1 ?a1 ?B1 ?p2 ?a2 ?B2 ] =>
      destruct (eq_var_dec p1 p2);
        [ destruct (eq_var_dec a1 a2);
          [ unfold eqBs;
            repeat (rewrite eq_var_dec_same);
            simpl;
            try (complete reflexivity)
          | complete sp
          ]
        | complete sp
        ]

    | [ H : eqBs ?p1 ?a1 ?B1 ?p2 ?a2 ?B2 |- _ ] =>
      destruct (eq_var_dec p1 p2);
        [ destruct (eq_var_dec a1 a2);
          [ unfold eqBs in H;
            repeat (rewrite eq_var_dec_same in H);
            simpl in H
          | complete sp
          ]
        | complete sp
        ]

    | [ |- eqCs ?p1 ?a1 ?b1 ?C1 ?p2 ?a2 ?b2 ?C2 ] =>
      destruct (eq_var_dec p1 p2);
        [ destruct (eq_var_dec a1 a2);
          [ destruct (eq_var_dec b1 b2);
            [ unfold eqCs;
              repeat (rewrite eq_var_dec_same);
              simpl;
              try (complete reflexivity)
            | complete sp
            ]
          | complete sp
          ]
        | complete sp
        ]

    | [ H : eqCs ?p1 ?a1 ?b1 ?C1 ?p2 ?a2 ?b2 ?C2 |- _ ] =>
      destruct (eq_var_dec p1 p2);
        [ destruct (eq_var_dec a1 a2);
          [ destruct (eq_var_dec b1 b2);
            [ unfold eqCs in H;
              repeat (rewrite eq_var_dec_same in H);
              simpl in H
            | complete sp
            ]
          | complete sp
          ]
        | complete sp
        ]

  end.

Ltac red_eqTs := repeat red_eqTs_step.

Lemma eqAs_refl {p} :
  forall a A, @eqAs p a A a A.
Proof.
  intros.
  red_eqTs.
Qed.
Hint Immediate eqAs_refl.

Lemma eqAs_false {p} :
  forall a A, @eqAs p a A a A -> False.
Proof.
  intros.
  red_eqTs.
Abort.

Lemma eqBs_refl {pp} :
  forall p a B, @eqBs pp p a B p a B.
Proof.
  intros.
  red_eqTs.
Qed.
Hint Immediate eqBs_refl.

Lemma eqCs_refl {pp} :
  forall p a b C, @eqCs pp p a b C p a b C.
Proof.
  intros.
  red_eqTs.
Qed.
Hint Immediate eqCs_refl.

Definition eq_type_pfamilies {p} (C : pfam_type) :=
  forall P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 (p1 : @CTerm p)
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    C P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
    = C P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
    -> P1 = P2
       # ap1 = ap2
       # bp1 = bp2 # ba1 = ba2
       # cp1 = cp2 # ca1 = ca2 # cb1 = cb2
       # p1 = p2
       # eqAs ap1 A1 ap2 A2
       # eqBs bp1 ba1 B1 bp2 ba2 B2
       # eqCs cp1 ca1 cb1 C1 cp2 ca2 cb2 C2.

Lemma eq_type_pfamilies_mkc_pw {p} : @eq_type_pfamilies p mkc_pw.
Proof.
  unfold eq_type_pfamilies; dands; introv e.
  applydup @mkc_pw_eq1 in e as f; repnd; subst.
  apply mkc_pw_eq2 in e; repnd; subst; sp.
Qed.
Hint Immediate eq_type_pfamilies_mkc_pw.

Lemma eq_type_pfamilies_mkc_pm {p} : @eq_type_pfamilies p mkc_pm.
Proof.
  unfold eq_type_pfamilies; dands; introv e.
  applydup @mkc_pm_eq1 in e as f; repnd; subst.
  apply mkc_pm_eq2 in e; repnd; subst; sp.
Qed.
Hint Immediate eq_type_pfamilies_mkc_pm.

Definition term_equality_symmetric_fam {pp} (eqp : per) eqa :=
  forall (p p' : @CTerm pp) (ep : eqp p p'),
    @term_equality_symmetric pp (eqa p p' ep).

Definition term_equality_transitive_fam {pp} (eqp : per) eqa :=
  forall (p p' : @CTerm pp) (ep : eqp p p'),
    @term_equality_transitive pp (eqa p p' ep).

Definition term_equality_symmetric_fam_fam {pp} (eqp : per) eqa eqb :=
  forall (p p' : @CTerm pp) (ep : eqp p p'),
    @term_equality_symmetric_fam pp (eqa p p' ep) (eqb p p' ep).

Definition term_equality_transitive_fam_fam {pp} (eqp : per) eqa eqb :=
  forall (p p' : @CTerm pp) (ep : eqp p p'),
    @term_equality_transitive_fam pp (eqa p p' ep) (eqb p p' ep).

Definition eq_fam_respects_eq_term_equals {p} (eqp : per) eqa :=
  forall (p1 p2 p3 p4 : @CTerm p) (e1 : eqp p1 p3) (e2 : eqp p2 p4),
    eqp p1 p2
    -> eqp p3 p4
    -> @eq_term_equals p (eqa p1 p3 e1) (eqa p2 p4 e2).

Definition eq_fam_fam_respects_eq_term_equals {p} (eqp : per) eqa eqb :=
  forall (p1 p2 p3 p4 : @CTerm p) (ep1 : eqp p1 p3) (ep2 : eqp p2 p4)
         (a1 a2 a3 a4 : @CTerm p) (ea1 : eqa p1 p3 ep1 a1 a3) (ea2 : eqa p2 p4 ep2 a2 a4)
         (e1 : eqp p1 p2)
         (e2 : eqp p3 p4),
    eqa p1 p2 e1 a1 a2
    -> eqa p3 p4 e2 a3 a4
    -> @eq_term_equals p (eqb p1 p3 ep1 a1 a3 ea1) (eqb p2 p4 ep2 a2 a4 ea2).

Definition eq_fam_refl_left {pp} (eqp : per) eqa :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p p),
    @eq_term_equals pp (eqa p p' ep) (eqa p p ep').

Definition eq_fam_refl_right {pp} (eqp : per) eqa :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p' p'),
    @eq_term_equals pp (eqa p p' ep) (eqa p' p' ep').

Definition eq_fam_sym {pp} (eqp : per) eqa :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p' p),
    @eq_term_equals pp (eqa p p' ep) (eqa p' p ep').

Lemma eq_fam_refl_left_if_respects_eq {p} :
  forall (eqp : per(p)) eqa,
    term_equality_symmetric eqp
    -> eq_fam_respects_eq_term_equals eqp eqa
    -> eq_fam_refl_left eqp eqa.
Proof.
  introv tes resp.
  allunfold @eq_fam_respects_eq_term_equals.
  unfold eq_fam_refl_left; introv.
  apply resp; sp.
Qed.

Lemma eq_fam_sym_if_respects_eq {p} :
  forall (eqp : per(p)) eqa,
    eq_fam_respects_eq_term_equals eqp eqa
    -> eq_fam_sym eqp eqa.
Proof.
  introv resp.
  allunfold @eq_fam_respects_eq_term_equals.
  unfold eq_fam_sym; introv.
  apply resp; sp.
Qed.

Definition eq_fam_fam_refl_left {pp} eqp eqa eqb :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p p)
         (a a' : @CTerm pp) (ea : eqa p p' ep a a') (ea' : eqa p p ep' a a),
    @eq_term_equals pp (eqb p p' ep a a' ea) (eqb p p ep' a a ea').

Definition eq_fam_fam_refl_right {pp} eqp eqa eqb :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p' p')
         (a a' : @CTerm pp) (ea : eqa p p' ep a a') (ea' : eqa p' p' ep' a' a'),
    @eq_term_equals pp (eqb p p' ep a a' ea) (eqb p' p' ep' a' a' ea').

Definition eq_fam_fam_sym {pp} eqp eqa eqb :=
  forall (p p' : @CTerm pp) (ep : eqp p p') (ep' : eqp p' p)
         (a a' : @CTerm pp) (ea : eqa p p' ep a a') (ea' : eqa p' p ep' a' a),
    @eq_term_equals pp (eqb p p' ep a a' ea) (eqb p' p ep' a' a ea').

Lemma eq_fam_fam_refl_left_if_respects_eq {pp} :
  forall (eqp : per(pp)) eqa eqb,
    term_equality_symmetric eqp
    -> term_equality_symmetric_fam eqp eqa
    -> eq_fam_sym eqp eqa
    -> eq_fam_fam_respects_eq_term_equals eqp eqa eqb
    -> eq_fam_fam_refl_left eqp eqa eqb.
Proof.
  introv tesp tesa1 tesa2 resp.
  allunfold @eq_fam_fam_respects_eq_term_equals.
  unfold eq_fam_fam_refl_left; introv.
  dup ep as ep1.
  apply tesp in ep1.
  apply resp with (e1 := ep') (e2 := ep1); sp.
  rw (tesa2 p' p ep1 ep).
  apply (tesa1 p p' ep); sp.
Qed.

Lemma eq_fam_fam_sym_if_respects_eq {p} :
  forall (eqp : per(p)) eqa eqb,
    eq_fam_fam_respects_eq_term_equals eqp eqa eqb
    -> eq_fam_fam_sym eqp eqa eqb.
Proof.
  introv resp.
  allunfold @eq_fam_fam_respects_eq_term_equals.
  unfold eq_fam_fam_sym; introv.
  apply resp with (e1 := ep) (e2 := ep'); sp.
Qed.

Definition type_sys_props_fam {pp} lib (ts : cts(pp)) (eqp : per) ap A ap' A' eqa :=
  forall p p' (ep : eqp p p'),
    type_sys_props lib ts
                   (substc p ap A)
                   (substc p' ap' A')
                   (eqa p p' ep).

Definition type_sys_props_fam_fam {pp} lib (ts : cts(pp)) (eqp : per) eqa bp ba B bp' ba' B' eqb :=
  forall p p' (ep : eqp p p') a a' (ea : eqa p p' ep a a'),
    type_sys_props lib ts
                   (lsubstc2 bp p ba a B)
                   (lsubstc2 bp' p' ba' a' B')
                   (eqb p p' ep a a' ea).

Definition eq_term_equals_fam {q} (eqp : per) eqa eqp1 eqa1 :=
  forall (p p' : @CTerm q) (ep : eqp p p') (ep1 : eqp1 p p'),
    @eq_term_equals q (eqa p p' ep) (eqa1 p p' ep1).

Definition eq_term_equals_fam_fam {q}
             (eqp  : per) (eqa  : per-fam(eqp))  eqb
             (eqp1 : per) (eqa1 : per-fam(eqp1)) eqb1 :=
  forall (p p' : @CTerm q) (ep : eqp p p') (ep1 : eqp1 p p'),
         @eq_term_equals_fam q (eqa p p' ep)
                            (eqb p p' ep)
                            (eqa1 p p' ep1)
                            (eqb1 p p' ep1).

Lemma term_equality_symmetric_fam_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o)) eqa1 eqa2,
    term_equality_symmetric_fam eqp1 eqa1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> term_equality_symmetric_fam eqp2 eqa2.
Proof.
  introv tes eqta eqtb.
  introv.
  dup ep as ep'.
  apply eqta in ep'.
  generalize (tes p p' ep'); introv tesa.
  apply term_equality_symmetric_eq_term_equals with (eq := eqa1 p p' ep'); sp.
Qed.

Lemma term_equality_transitive_fam_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o)) eqa1 eqa2,
    term_equality_transitive_fam eqp1 eqa1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> term_equality_transitive_fam eqp2 eqa2.
Proof.
  introv tet eqta eqtb.
  introv.
  dup ep as ep'.
  apply eqta in ep'.
  generalize (tet p p' ep'); introv teta.
  apply term_equality_transitive_eq_term_equals with (eq := eqa1 p p' ep'); sp.
Qed.

Lemma eq_fam_respects_eq_term_equals_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o)) eqa1 eqa2,
    eq_fam_respects_eq_term_equals eqp1 eqa1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_fam_respects_eq_term_equals eqp2 eqa2.
Proof.
  introv resp eqta eqtb.
  introv e3 e4.
  dup e1 as e1'.
  dup e2 as e2'.
  dup e3 as e3'.
  dup e4 as e4'.
  apply eqta in e1'.
  apply eqta in e2'.
  apply eqta in e3'.
  apply eqta in e4'.
  generalize (resp p1 p2 p3 p4 e1' e2' e3' e4'); introv k.
  apply eq_term_equals_trans with (eqa1 p1 p3 e1').
  apply eq_term_equals_sym; sp.
  apply eq_term_equals_trans with (eqa1 p2 p4 e2'); sp.
Qed.

Lemma term_equality_symmetric_fam_fam_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o))
         (eqa1 : per-fam(eqp1))
         (eqa2 : per-fam(eqp2))
         eqb1 eqb2,
    term_equality_symmetric_fam_fam eqp1 eqa1 eqb1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> term_equality_symmetric_fam_fam eqp2 eqa2 eqb2.
Proof.
  introv tes eqtp eqta eqtb.
  introv.
  dup ep as ep'.
  apply eqtp in ep'.
  generalize (tes p p' ep'); introv tesb.
  apply @term_equality_symmetric_fam_eq_term_equals
        with (eqp1 := eqa1 p p' ep') (eqa1 := eqb1 p p' ep'); sp.
Qed.

Lemma term_equality_transitive_fam_fam_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o))
         (eqa1 : per-fam(eqp1))
         (eqa2 : per-fam(eqp2))
         eqb1 eqb2,
    term_equality_transitive_fam_fam eqp1 eqa1 eqb1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> term_equality_transitive_fam_fam eqp2 eqa2 eqb2.
Proof.
  introv tet eqtp eqta eqtb.
  introv.
  dup ep as ep'.
  apply eqtp in ep'.
  generalize (tet p p' ep'); introv teta.
  apply @term_equality_transitive_fam_eq_term_equals
        with (eqp1 := eqa1 p p' ep') (eqa1 := eqb1 p p' ep'); sp.
Qed.

Lemma eq_fam_fam_respects_eq_term_equals_eq_term_equals {o} :
  forall (eqp1 eqp2 : per(o))
         (eqa1 : per-fam(eqp1))
         (eqa2 : per-fam(eqp2))
         eqb1 eqb2,
    eq_fam_fam_respects_eq_term_equals eqp1 eqa1 eqb1
    -> eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> eq_fam_fam_respects_eq_term_equals eqp2 eqa2 eqb2.
Proof.
  introv resp eqtp eqta eqtb.
  introv ea3 ea4.

  dup ep1 as ep1'.
  dup ep2 as ep2'.
  dup e1 as e1'.
  dup e2 as e2'.
  apply eqtp in ep1'.
  apply eqtp in ep2'.
  apply eqtp in e1'.
  apply eqtp in e2'.

  dup ea1 as ea1'.
  dup ea2 as ea2'.
  dup ea3 as ea3'.
  dup ea4 as ea4'.
  generalize (eqta p1 p3 ep1' ep1); intro k; apply k in ea1'; clear k.
  generalize (eqta p2 p4 ep2' ep2); intro k; apply k in ea2'; clear k.
  generalize (eqta p1 p2 e1' e1); intro k; apply k in ea3'; clear k.
  generalize (eqta p3 p4 e2' e2); intro k; apply k in ea4'; clear k.

  generalize (resp p1 p2 p3 p4 ep1' ep2' a1 a2 a3 a4 ea1' ea2' e1' e2' ea3' ea4') ; introv k.
  apply eq_term_equals_trans with (eqb1 p1 p3 ep1' a1 a3 ea1').
  apply eq_term_equals_sym; sp.
  apply eqtb.
  apply eq_term_equals_trans with (eqb1 p2 p4 ep2' a2 a4 ea2'); sp.
  apply eqtb.
Qed.

Lemma type_sys_props_fam_implies_eq_fam_sym {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> eq_fam_sym eqp eqa.
Proof.
  introv tspp tspf.
  applydup @type_sys_props_implies_term_eq_sym in tspp as tes.
  applydup @type_sys_props_implies_term_eq_trans in tspp as tet.
  clear tspp.
  unfold eq_fam_sym; introv.
  unfold type_sys_props_fam in tspf.
  assert (eqp p p) as ep1 by (apply tet with (t2 := p'); sp).
  apply eq_term_equals_trans with (eq2 := eqa p p ep1).

  generalize (tspf p p' ep); introv tsp1.
  generalize (tspf p p ep1); introv tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  apply uv2 with (T3 := substc p ap' A'); sp.

  generalize (tspf p' p ep'); introv tsp1.
  generalize (tspf p p ep1); introv tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (tygs2 (substc p' ap A) (substc p ap' A') (eqa p' p ep'));
    intro k; dest_imp k hyp.
  applydup k in tygt2.
  apply uv1 with (T3 := substc p' ap A); sp.
Qed.

Lemma tsp_implies_eq_fam_refl_left {o} :
  forall lib ts (eqp : per(o)) ap A ap' A' eqa,
    type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> eq_fam_refl_left eqp eqa.
Proof.
  introv tes.
  unfold eq_fam_refl_left; introv.
  unfold type_sys_props_fam in tes.
  generalize (tes p p' ep); intro tsp1.
  generalize (tes p p ep'); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (uv2 (substc p ap' A') (eqa p p ep')); intro k; repeat (autodimp k hyp).
Qed.

Lemma tsp_implies_eq_fam_refl_right {o} :
  forall lib (ts : cts(o)) eqp ap A ap' A' eqa,
    type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> eq_fam_refl_right eqp eqa.
Proof.
  introv tes.
  unfold eq_fam_refl_right; introv.
  unfold type_sys_props_fam in tes.
  generalize (tes p p' ep); intro tsp1.
  generalize (tes p' p' ep'); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (uv2 (substc p' ap A) (eqa p' p' ep')); intro k; repeat (autodimp k hyp).
  right.
  apply tygs1; auto.
Qed.

Lemma tsp_implies_eq_fam_fam_refl_left {o} :
  forall lib (ts : cts(o)) eqp eqa bp ba B bp' ba' B' eqb,
    type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> eq_fam_fam_refl_left eqp eqa eqb.
Proof.
  introv tes.
  unfold eq_fam_fam_refl_left; introv.
  generalize (tes p p' ep a a' ea); intro tsp1.
  generalize (tes p p ep' a a ea'); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (uv2 (lsubstc2 bp' p ba' a B') (eqb p p ep' a a ea'));
    intro k; repeat (autodimp k hyp).
Qed.

Lemma tsp_implies_eq_fam_fam_refl_right {o} :
  forall lib (ts : cts(o)) eqp eqa bp ba B bp' ba' B' eqb,
    type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> eq_fam_fam_refl_right eqp eqa eqb.
Proof.
  introv tes.
  unfold eq_fam_fam_refl_right; introv.
  generalize (tes p p' ep a a' ea); intro tsp1.
  generalize (tes p' p' ep' a' a' ea'); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (uv2 (lsubstc2 bp p' ba a' B) (eqb p' p' ep' a' a' ea'));
    intro k; repeat (autodimp k hyp).
  right.
  apply tygs1; auto.
Qed.

Lemma type_sys_props_fam_implies_sym_trans_respeq {o} :
  forall lib (ts : cts(o)) eqp P P' ap A ap' A' eqa,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> term_equality_symmetric_fam eqp eqa
       # term_equality_transitive_fam eqp eqa
       # eq_fam_respects_eq_term_equals eqp eqa.
Proof.
  introv tspp tspf; dands.

  - unfold term_equality_symmetric_fam; introv.
    generalize (tspf p p' ep); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; auto.

  - unfold term_equality_transitive_fam; introv.
    generalize (tspf p p' ep); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; auto.

  - unfold eq_fam_respects_eq_term_equals; introv ep1 ep2.
    applydup @type_sys_props_implies_term_eq_sym in tspp as tes.
    applydup @type_sys_props_implies_term_eq_trans in tspp as tet.
    clear tspp.

    assert (eqp p1 p2) as ep3 by (apply tet with (t2 := p3); sp; apply tet with (t2 := p4); sp).
    assert (eqp p1 p1) as ep4 by (apply tet with (t2 := p3); sp).
    assert (eqp p2 p2) as ep5 by (apply tet with (t2 := p1); sp).

    apply eq_term_equals_trans with (eq2 := eqa p1 p2 ep3).

    generalize (tsp_implies_eq_fam_refl_left lib ts eqp ap A ap' A' eqa);
      intro tsp1; autodimp tsp1 hyp.
    apply eq_term_equals_trans with (eq2 := eqa p1 p1 ep4); sp.
    apply eq_term_equals_sym; sp.

    apply eq_term_equals_trans with (eq2 := eqa p2 p2 ep5).

    generalize (tsp_implies_eq_fam_refl_right lib ts eqp ap A ap' A' eqa);
      intro tsp1; autodimp tsp1 hyp.

    apply eq_term_equals_sym.
    generalize (tsp_implies_eq_fam_refl_left lib ts eqp ap A ap' A' eqa);
      intro tsp1; autodimp tsp1 hyp.
Qed.

Lemma type_sys_props_fam_fam_implies_sym_trans_respeq {o} :
  forall lib (ts : cts(o)) eqp P P' ap A ap' A' eqa bp ba B bp' ba' B' eqb,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> term_equality_symmetric_fam_fam eqp eqa eqb
       # term_equality_transitive_fam_fam eqp eqa eqb
       # eq_fam_fam_respects_eq_term_equals eqp eqa eqb.
Proof.
  introv tspp tspa tspb; dands.

  - unfold term_equality_symmetric_fam_fam; intros p p' ep.
    unfold term_equality_symmetric_fam; intros a a' ea.
    generalize (tspb p p' ep a a' ea); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; auto.

  - unfold term_equality_transitive_fam_fam; intros p p' ep.
    unfold term_equality_transitive_fam; intros a a' ea.
    generalize (tspb p p' ep a a' ea); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; auto.

  - unfold eq_fam_fam_respects_eq_term_equals; introv eqa1 eqa2.
    applydup @type_sys_props_implies_term_eq_sym in tspp as tes.
    applydup @type_sys_props_implies_term_eq_trans in tspp as tet.
    generalize (type_sys_props_fam_implies_sym_trans_respeq lib ts eqp P P' ap A ap' A' eqa tspp tspa);
      intro eqaprp; repnd.
    clear tspp.

    assert (eqp p1 p1) as ep4 by (apply tet with (t2 := p3); sp).
    assert (eqp p2 p2) as ep5 by (apply tet with (t2 := p1); sp).

    assert (eqa p1 p1 ep4 a1 a1)
           as eqa3
           by (generalize (tsp_implies_eq_fam_refl_left lib ts eqp ap A ap' A' eqa);
               introv k; autodimp k hyp;
               generalize (k p1 p2 e1 ep4); intro j; rw <- j; sp;
               apply eqaprp1 with (t2 := a2); sp;
               apply eqaprp0; sp).

    assert (eqa p2 p2 ep5 a2 a2)
           as eqa4
           by (generalize (tsp_implies_eq_fam_refl_right lib ts eqp ap A ap' A' eqa);
               introv k; autodimp k hyp;
               generalize (k p1 p2 e1 ep5); intro j; rw <- j; sp;
               apply eqaprp1 with (t2 := a1); sp;
               apply eqaprp0; sp).

    apply eq_term_equals_trans with (eq2 := eqb p1 p2 e1 a1 a2 eqa1).

    generalize (tsp_implies_eq_fam_fam_refl_left lib ts eqp eqa bp ba B bp' ba' B' eqb);
      intro tsp1; autodimp tsp1 hyp.
    apply eq_term_equals_trans with (eq2 := eqb p1 p1 ep4 a1 a1 eqa3); sp.
    apply eq_term_equals_sym; sp.

    apply eq_term_equals_trans with (eq2 := eqb p2 p2 ep5 a2 a2 eqa4).

    generalize (tsp_implies_eq_fam_fam_refl_right lib ts eqp eqa bp ba B bp' ba' B' eqb);
      intro tsp1; autodimp tsp1 hyp.

    apply eq_term_equals_sym.
    generalize (tsp_implies_eq_fam_fam_refl_left lib ts eqp eqa bp ba B bp' ba' B' eqb);
      intro tsp1; autodimp tsp1 hyp.
Qed.

Lemma type_sys_props_fam_fam_implies_eq_fam_fam_sym {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa bp ba B bp' ba' B' eqb,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> eq_fam_fam_sym eqp eqa eqb.
Proof.
  introv tspp tspa tspb.

  generalize (type_sys_props_fam_implies_eq_fam_sym lib ts P P' eqp ap A ap' A' eqa);
    introv sym; repeat (autodimp sym hyp).

  unfold eq_fam_fam_sym; introv.

  applydup @type_sys_props_implies_term_eq_sym in tspp as tes.
  applydup @type_sys_props_implies_term_eq_trans in tspp as tet.

  assert (eqp p p) as ep1 by (apply tet with (t2 := p'); sp).

  generalize (tsp_implies_eq_fam_refl_left lib ts eqp ap A ap' A' eqa);
    intro refll; autodimp refll hyp.

  generalize (tsp_implies_eq_fam_refl_right lib ts eqp ap A ap' A' eqa);
    intro reflr; autodimp reflr hyp.

  generalize (refll p p' ep ep1); intro k1.
  generalize (reflr p' p ep' ep1); intro k2.

  assert (eqa p p ep1 a a)
         as ea1
         by (rw <- k1;
             generalize (tspa p p' ep); intro k;
             applydup @type_sys_props_implies_term_eq_sym in k as sym1;
             applydup @type_sys_props_implies_term_eq_trans in k as tran1;
             apply tran1 with (t2 := a'); sp).

  generalize (tsp_implies_eq_fam_fam_refl_left
                lib ts eqp eqa bp ba B bp' ba' B' eqb);
    intro e1; autodimp e1 hyp.

  generalize (tsp_implies_eq_fam_fam_refl_right
                lib ts eqp eqa bp ba B bp' ba' B' eqb);
    intro e2; autodimp e2 hyp.

  generalize (e1 p p' ep ep1 a a' ea ea1); intro r1.
  generalize (e2 p' p ep' ep1 a' a ea' ea1); intro r2.

  apply eq_term_equals_trans with (eq2 := eqb p p ep1 a a ea1); sp.
  apply eq_term_equals_sym; sp.
Qed.

Lemma type_sys_props_fam_sym {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam lib ts eqp ap' A' ap A eqa.
Proof.
  introv tspp tspf.
  allunfold @type_sys_props_fam; introv.
  apply type_sys_props_sym.
  assert (eqp p' p)
         as ep'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  generalize (tspf p' p ep'); intro tsp.
  apply type_sys_props_uv with (eq := eqa p' p ep'); sp.
  generalize (type_sys_props_fam_implies_eq_fam_sym lib ts P P' eqp ap A ap' A' eqa);
    intro k; dest_imp k hyp.
Qed.

Lemma type_sys_props_fam_fam_sym {o} :
  forall lib (ts : cts(o)) P P' eqp ap A ap' A' eqa bp ba B bp' ba' B' eqb,
    type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> type_sys_props_fam_fam lib ts eqp eqa bp' ba' B' bp ba B eqb.
Proof.
  introv tspp tspa tspb.
  allunfold @type_sys_props_fam_fam; introv.
  apply type_sys_props_sym.

  assert (eqp p' p)
         as ep'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).

  assert (eqa p' p ep' a' a)
         as ea'
         by (generalize (type_sys_props_fam_implies_eq_fam_sym lib ts P P' eqp ap A ap' A' eqa);
             intro k; repeat (autodimp k hyp);
             generalize (k p p' ep ep'); intro e; rw <- e;
             generalize (tspa p p' ep); intro t;
             apply type_sys_props_implies_term_eq_sym in t;
             apply t; auto).

  generalize (tspb p' p ep' a' a ea'); intro tsp.
  apply type_sys_props_uv with (eq := eqb p' p ep' a' a ea'); sp.

  generalize (type_sys_props_fam_fam_implies_eq_fam_fam_sym
                lib ts P P' eqp ap A ap' A' eqa bp ba B bp' ba' B' eqb);
    intro j; repeat (autodimp j hyp).
Qed.

Lemma type_pfamily_eq_term_equals {o} :
  forall lib TC (ts : cts(o)) T T1 T2
         eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp1' ca1' cb1' C1'
         p1 p1'
         eqp2 eqa2 eqb2
         cp2 ca2 cb2 C2
         cp2' ca2' cb2' C2'
         p2 p2'
         P ap A bp ba B cp ca cb C p
         P' eqp
         ap' A' eqa
         bp' ba' B' eqb,
    computes_to_valc lib T (TC P ap A bp ba B cp ca cb C p)
    -> eq_type_pfamilies TC
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> type_pfamily lib TC ts T T1 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp1' ca1' cb1' C1'
                    p1 p1'
    -> type_pfamily lib TC ts T T2 eqp2 eqa2 eqb2
                    cp2 ca2 cb2 C2
                    cp2' ca2' cb2' C2'
                    p2 p2'
    -> p = p1 # p = p2
       # cp = cp1 # ca = ca1 # cb = cb1
       # eqCs cp ca cb C cp1 ca1 cb1 C1
       # cp = cp2 # ca = ca2 # cb = cb2
       # eqCs cp ca cb C cp2 ca2 cb2 C2
       # eq_term_equals eqp eqp1
       # eq_term_equals eqp eqp2
       # eq_term_equals eqp1 eqp2
       # eq_term_equals_fam eqp eqa eqp1 eqa1
       # eq_term_equals_fam eqp eqa eqp2 eqa2
       # eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
       # eq_term_equals_fam_fam eqp eqa eqb eqp1 eqa1 eqb1
       # eq_term_equals_fam_fam eqp eqa eqb eqp2 eqa2 eqb2
       # eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2.
Proof.
  introv comp eqpf tspP tspA tspB tpf1 tpf2.
  allunfold @type_pfamily; exrepnd; spcast.
  computes_to_eqval.
  apply eqpf in eq; repnd; subst.
  red_eqTs; subst; GC.
  computes_to_eqval.
  apply eqpf in eq; repnd; subst.
  red_eqTs; subst; GC.

  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; red_eqTs; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; red_eqTs; GC.

  prove_and eqp_1.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
    apply uv with (T3 := P3); sp.

  prove_and eqp_2.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
    apply uv with (T3 := P2); sp.

  prove_and eqp_1_2.

  apply eq_term_equals_trans with (eq2 := eqp); sp;
  apply eq_term_equals_sym; sp.

  prove_and eqa_1.

  introv.
  generalize (tpf11 p0 p' ep1); intro e1.
  generalize (tspA p0 p' ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := substc p' ap3 A3); sp.

  prove_and eqa_2.

  introv.
  generalize (tpf5 p0 p' ep1); intro e2.
  generalize (tspA p0 p' ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := substc p' ap2 A2); sp.

  prove_and eqa_1_2.

  introv.
  generalize (tpf11 p0 p' ep); intro e1.
  generalize (tpf5 p0 p' ep1); intro e2.
  assert (eqp p0 p') as ep' by (allrw; sp).
  generalize (tspA p0 p' ep'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply eq_term_equals_trans with (eq2 := eqa p0 p' ep'); sp;
  apply eq_term_equals_sym; sp.

  prove_and eqb_1.

  intros p0 p' ep ep1.
  intros a a' ea ea1.
  generalize (tpf12 p0 p' ep1 a a' ea1); intro e1.
  generalize (tspB p0 p' ep a a' ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := lsubstc2 bp3 p' ba3 a' B3); sp.

  prove_and eqb_2.

  intros p0 p' ep ep1.
  intros a a' ea ea1.
  generalize (tpf6 p0 p' ep1 a a' ea1); intro e2.
  generalize (tspB p0 p' ep a a' ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := lsubstc2 bp2 p' ba2 a' B2); sp.

  (* last one *)
  intros p0 p' ep ep1.
  intros a a' ea ea1.
  generalize (tpf12 p0 p' ep a a' ea); intro e1.
  generalize (tpf6 p0 p' ep1 a a' ea1); intro e2.
  assert (eqp p0 p') as ep' by (allrw; sp).
  assert (eqa p0 p' ep' a a') as ea' by (generalize (eqa_1 p0 p' ep' ep); intro k; allrw; sp).
  generalize (tspA p0 p' ep'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply eq_term_equals_trans with (eq2 := eqb p0 p' ep' a a' ea'); sp.
  apply eq_term_equals_sym; apply eqb_1.
  apply eqb_2.
Qed.

Lemma eq_term_equals_fam_sym {o} :
  forall (eqp1 : per(o)) eqa1 (eqp2 : per) eqa2,
    eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam eqp2 eqa2 eqp1 eqa1.
Proof.
  unfold eq_term_equals_fam.
  introv eqt; introv.
  apply eq_term_equals_sym.
  apply eqt.
Qed.

Lemma eq_term_equals_fam_fam_sym {o} :
  forall (eqp1 : per(o)) eqa1 eqb1 eqp2 eqa2 eqb2,
    eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> eq_term_equals_fam_fam eqp2 eqa2 eqb2 eqp1 eqa1 eqb1.
Proof.
  unfold eq_term_equals_fam_fam.
  introv eqt; introv.
  apply eq_term_equals_fam_sym.
  apply eqt.
Qed.

Lemma eq_term_equals_fam_trans {o} :
  forall (eqp1 : per(o)) eqa1 eqp2 eqa2 eqp3 eqa3,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam eqp2 eqa2 eqp3 eqa3
    -> eq_term_equals_fam eqp1 eqa1 eqp3 eqa3.
Proof.
  introv eq eqt1 eqt2; introv.
  assert (eqp2 p p') as ep2 by (apply eq; sp).
  apply eq_term_equals_trans with (eq2 := eqa2 p p' ep2).
  apply eqt1.
  apply eqt2.
Qed.

Lemma eq_term_equals_fam_fam_trans {o} :
  forall (eqp1 : per(o)) eqa1 eqb1 eqp2 eqa2 eqb2 eqp3 eqa3 eqb3,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> eq_term_equals_fam_fam eqp2 eqa2 eqb2 eqp3 eqa3 eqb3
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp3 eqa3 eqb3.
Proof.
  introv eqps eqas eqt1 eq2; introv.
  assert (eqp2 p p') as ep2 by (apply eqps; sp).
  apply @eq_term_equals_fam_trans with (eqp2 := eqa2 p p' ep2) (eqa2 := eqb2 p p' ep2); sp.
Qed.

Definition equal_Cparams {o} (eqp : per(o)) eqa eqb cp ca cb C cp' ca' cb' C' : [U] :=
  forall (p p' : CTerm) (ep : eqp p p')
         (a a' : CTerm) (ea : eqa p p' ep a a')
         (b b' : CTerm),
    eqb p p' ep a a' ea b b'
    -> eqp (lsubstc3 cp p ca a cb b C) (lsubstc3 cp' p' ca' a' cb' b' C').

Definition equal_fams {o} (ts : cts(o)) eqp ap1 A1 ap2 A2 eqa :=
  forall p1 p2,
  forall ep : eqp p1 p2,
    ts (substc p1 ap1 A1) (substc p2 ap2 A2) (eqa p1 p2 ep).

Definition equal_fams_fams {o} (ts : cts(o)) eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb :=
  forall p1 p2,
  forall ep : eqp p1 p2,
  forall a1 a2,
  forall ea : eqa p1 p2 ep a1 a2,
    ts (lsubstc2 bp1 p1 ba1 a1 B1)
       (lsubstc2 bp2 p2 ba2 a2 B2)
       (eqb p1 p2 ep a1 a2 ea).

Lemma fold_equal_Cparams {o} :
  forall (eqp : per(o)) eqa eqb cp ca cb C cp' ca' cb' C',
    (forall (p p' : CTerm) (ep : eqp p p')
            (a a' : CTerm) (ea : eqa p p' ep a a')
            (b b' : CTerm),
       eqb p p' ep a a' ea b b'
       -> eqp (lsubstc3 cp p ca a cb b C) (lsubstc3 cp' p' ca' a' cb' b' C'))
    = equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'.
Proof. sp. Qed.

Lemma fold_equal_fams {o} :
  forall (ts : cts(o)) eqp ap1 A1 ap2 A2 eqa,
    (forall p1 p2,
     forall ep : eqp p1 p2,
       ts (substc p1 ap1 A1) (substc p2 ap2 A2) (eqa p1 p2 ep))
    = equal_fams ts eqp ap1 A1 ap2 A2 eqa.
Proof. sp. Qed.

Lemma fold_equal_fams_fams {o} :
  forall (ts : cts(o)) eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb,
    (forall p1 p2,
     forall ep : eqp p1 p2,
     forall a1 a2,
     forall ea : eqa p1 p2 ep a1 a2,
       ts (lsubstc2 bp1 p1 ba1 a1 B1)
          (lsubstc2 bp2 p2 ba2 a2 B2)
          (eqb p1 p2 ep a1 a2 ea))
    = equal_fams_fams ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb.
Proof. sp. Qed.

Lemma equal_Cparams_eq_term_equals {o} :
  forall (eqp1 : per(o)) eqa1 eqb1 eqp2 eqa2 eqb2
         cp ca cb C cp' ca' cb' C',
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> equal_Cparams eqp1 eqa1 eqb1 cp ca cb C cp' ca' cb' C'
    -> equal_Cparams eqp2 eqa2 eqb2 cp ca cb C cp' ca' cb' C'.
Proof.
  introv eqps eqas eqbs eqCs.
  introv eb.
  apply eqps.
  assert (eqp1 p p') as ep' by (apply eqps; sp).
  assert (eqa1 p p' ep' a a') as ea' by (generalize (eqas p p' ep' ep); intro e; apply e; sp).
  assert (eqb1 p p' ep' a a' ea' b b') as eb' by (generalize (eqbs p p' ep' ep a a' ea' ea); intro e; apply e; sp).
  generalize (eqCs p p' ep' a a' ea' b b' eb'); sp.
Qed.

Lemma equal_Cparams_sym {o} :
  forall (eqp : per(o)) eqa eqb cp ca cb C cp' ca' cb' C',
    term_equality_symmetric eqp
    -> term_equality_symmetric_fam eqp eqa
    -> term_equality_symmetric_fam_fam eqp eqa eqb
    -> eq_fam_sym eqp eqa
    -> eq_fam_fam_sym eqp eqa eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> equal_Cparams eqp eqa eqb cp' ca' cb' C' cp ca cb C.
Proof.
  introv eqsp eqsa eqsb eqfsa eqfsb eqCs.
  introv eb.
  assert (eqp p' p) as ep' by sp.
  assert (eqa p' p ep' a' a)
    as ea'
      by (generalize (eqfsa p p' ep ep'); intro e; apply e; clear e;
          generalize (eqsa p p' ep a a'); sp).
  assert (eqb p' p ep' a' a ea' b' b)
    as eb'
      by (generalize (eqfsb p p' ep ep' a a' ea ea'); intro e; apply e; clear e;
          generalize (eqsb p p' ep a a' ea b b'); sp).
  generalize (eqCs p' p ep' a' a ea' b' b eb'); sp.
Qed.

Lemma type_sys_props_change_equality {o} :
  forall lib (ts : cts(o)) A B C eq1 eq2 eq3,
    ts A B eq1
    -> type_sys_props lib ts C A eq2
    -> eq_term_equals eq2 eq3
    -> ts A B eq3.
Proof.
  introv tsa tsp eqt.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tys; sp.
  generalize (uv B eq1); intro k; dest_imp k hyp.
  generalize (tygs A B eq1); intro e1; dest_imp e1 hyp.
  generalize (tygs A B eq2); intro e2; dest_imp e2 hyp.
  rw e2.
  rw e1 in tsa.
  generalize (tygs A C eq2); intro e3; dest_imp e3 hyp.
  duplicate tygt as tsc.
  rw <- e3 in tygt.
  generalize (dum A B C eq1 eq2); intro j; repeat (dest_imp j hyp); repnd.
  generalize (dum C B A eq2 eq2); intro l; repeat (dest_imp l hyp); repnd.
Qed.

Lemma type_sys_props_change_equality2 {o} :
  forall lib (ts : cts(o)) A B C eq1 eq2 eq3,
    ts A B eq1
    -> type_sys_props lib ts A C eq2
    -> eq_term_equals eq2 eq3
    -> ts B A eq3.
Proof.
  introv tsa tsp eqt.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tygs A B eq3); intro e1; dest_imp e1 hyp.
  rw <- e1; clear e1.
  apply tys; sp.
  generalize (tygs A C eq2); intro e1; dest_imp e1 hyp.
  duplicate tygt as e.
  rw e1 in e; clear e1.
  generalize (tyt A eq2); intro e1; dest_imp e1 hyp; repnd.
  generalize (dum A A B eq2 eq1); sp.
Qed.

Lemma type_pfamily_sym {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2
         P ap A bp ba B cp ca cb C p
         eqp eqa eqb
         P' ap' A' bp' ba' B' cp' ca' cb' C',
    eq_type_pfamilies TC
    -> computes_to_valc lib T1 (TC P ap A bp ba B cp ca cb C p)
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> type_pfamily lib TC ts T1 T2 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> p = p1
       # cp = cp1 # ca = ca1 # cb = cb1
       # eqCs cp ca cb C cp1 ca1 cb1 C1
       (* eqp = eqp1 *)
       # eq_term_equals eqp eqp1
       (* eqa = eqa1 *)
       # eq_term_equals_fam eqp eqa eqp1 eqa1
       (* eqb = eqb1 *)
       # eq_term_equals_fam_fam eqp eqa eqb eqp1 eqa1 eqb1
       (* eqa refl left *)
       # eq_fam_refl_left eqp eqa
       (* eqa sym *)
       # eq_fam_sym eqp eqa
       (* eqb refl left *)
       # eq_fam_fam_refl_left eqp eqa eqb
       (* eqb sym *)
       # eq_fam_fam_sym eqp eqa eqb
       (* type_pfamily sym *)
       # type_pfamily lib TC ts T2 T1 eqp1 eqa1 eqb1
                      cp2 ca2 cb2 C2
                      cp1 ca1 cb1 C1
                      p2 p1.
Proof.
  introv eqtc comp tspP tspA tspB eqC tpf.
  allunfold @type_pfamily; exrepnd.
  spcast; computes_to_eqval.
  apply eqtc in eq; repnd; subst; red_eqTs; subst; GC.

  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; red_eqTs; GC.


  (* eqp = eqp1 *)
  prove_and eqps.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := P2); sp.


  (* eqa = eqa1 *)
  prove_and eqas.

  introv.
  generalize (tpf4 p0 p' ep1); intro e1.
  generalize (tspA p0 p' ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := substc p' ap2 A2); sp.


  (* eqb = eqb1 *)
  prove_and eqbs.

  intros p0 p' ep ep1 a a' ea ea1.
  generalize (tpf5 p0 p' ep1 a a' ea1); intro e1.
  generalize (tspB p0 p' ep a a' ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply uv with (T3 := lsubstc2 bp2 p' ba2 a' B2); sp.


  (* eqa refl left *)
  prove_and eqas_refl_l.

  intros p0 p' ep ep'.
  generalize (tspA p0 p' ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  assert (eqp1 p0 p0) as ep1' by (apply eqps; sp).
  generalize (tpf4 p0 p0 ep1'); intro e1.
  generalize (uv (substc p0 ap2 A2) (eqa1 p0 p0 ep1')); intro eqt1.
  dest_imp eqt1 hyp.
  generalize (eqas p0 p0 ep' ep1'); intro eqt2.
  apply eq_term_equals_trans with (eq2 := eqa1 p0 p0 ep1'); sp.
  apply eq_term_equals_sym; sp.


  (* eqa sym *)
  prove_and eqas_sym.

  introv.
  assert (eqp p0 p0)
         as ep1'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             generalize (tet p0 p' p0); sp).
  generalize (eqas_refl_l p0 p' ep ep1'); intro eqt1.
  apply eq_term_equals_trans with (eq2 := eqa p0 p0 ep1'); sp.
  generalize (tspA p' p0 ep'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tspA p0 p0 ep1'); intro tsp.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  apply uv1 with (T3 := substc p0 ap' A'); sp.


  (* eqb refl left *)
  prove_and eqbs_relf_l.
  introv.
  generalize (tspB p0 p' ep a a' ea); introv tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tspB p0 p0 ep' a a ea'); introv tsp1.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  generalize (uv (lsubstc2 bp' p0 ba' a B') (eqb p0 p0 ep' a a ea')); introv k.
  dest_imp k hyp.


  (* eqb sym *)
  prove_and eqbs_sym.
  introv.
  assert (eqp p0 p0)
         as ep1'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             generalize (tet p0 p' p0); sp).
  generalize (eqas_refl_l p0 p' ep ep1'); intro eqt1.
  dup ea as ea0; rw eqt1 in ea0; clear eqt1.
  assert (eqa p0 p0 ep1' a a)
    as ea1
    by (generalize (tspA p0 p0 ep1'); introv tsp;
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
        apply tet with (t2 := a'); sp).
  generalize (eqbs_relf_l p0 p' ep ep1' a a' ea ea1); intro eqt.
  apply eq_term_equals_trans with (eq2 := eqb p0 p0 ep1' a a ea1);
    try (complete auto); clear eqt.
  generalize (tspB p' p0 ep' a' a ea'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tspB p0 p0 ep1' a a ea1); intro tsp1.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  apply uv1 with (T3 := lsubstc2 bp' p0 ba' a B'); sp.


  (* type_pfamily sym *)
  exists P2 P ap2 ap A2 A.
  exists bp2 bp ba2 ba B2 B.

  prove_and c1; GC; try (complete (spcast; sp)).
  prove_and c2; GC; try (complete (spcast; sp)).

  prove_and eP.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tygs P P2 eqp1); intro k; dest_imp k hyp.
  rw <- k; sp.

  prove_and eqA.

  introv.

  assert (eqp p0 p1)
         as ep'
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tes; apply eqps; sp).
  assert (eqp1 p0 p1) as ep1' by (apply eqps; sp).
  assert (eqp p1 p0) as ep2' by (apply eqps; sp).

  generalize (tpf4 p0 p1 ep1'); intro e1; sp.
  generalize (tspA p0 p1 ep'); intro tsp.
  apply (type_sys_props_change_equality2 lib)
    with (C := substc p1 ap' A') (eq1 := eqa1 p0 p1 ep1') (eq2 := eqa p0 p1 ep'); sp.
  apply eq_term_equals_trans with (eq2 := eqa p1 p0 ep2'); sp.

  prove_and eqB.

  introv.

  assert (eqp p0 p1)
         as ep_01
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tes; apply eqps; sp).

  assert (eqp p1 p0) as ep_10 by (apply eqps; sp).
  assert (eqp1 p0 p1) as ep1_01 by (apply eqps; sp).

  assert (eqa p0 p1 ep_01 a2 a1)
    as ea_21
      by (generalize (eqas p1 p0 ep_10 ep); introv eqt;
          rw <- eqt in ea; clear eqt;
          generalize (eqas_sym  p1 p0 ep_10 ep_01); intro eqt;
          rw <- eqt; clear eqt;
          generalize (tspA p1 p0 ep_10); intro tsp;
          onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).

  assert (eqa p1 p0 ep_10 a1 a2)
    as ea_12
      by (generalize (eqas p1 p0 ep_10 ep); intro eqt; rw eqt; sp).

  assert (eqa1 p0 p1 ep1_01 a2 a1)
    as ea1_21
      by (generalize (eqas p0 p1 ep_01 ep1_01); intro eqt; rw <- eqt; sp).

  generalize (tpf5 p0 p1 ep1_01 a2 a1 ea1_21); intro ts1.
  apply (type_sys_props_change_equality2 lib)
    with (C := lsubstc2 bp' p1 ba' a1 B')
           (eq1 := eqb1 p0 p1 ep1_01 a2 a1 ea1_21)
           (eq2 := eqb p0 p1 ep_01 a2 a1 ea_21); sp.
  apply eq_term_equals_trans with (eq2 := eqb p1 p0 ep_10 a1 a2 ea_12); sp.
  apply eqbs.

  prove_and eqCps.

  introv eib.
  assert (eqp p0 p1)
         as ep_01
         by (onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
             apply tes; apply eqps; sp).
  assert (eqp p1 p0) as ep_10 by (apply eqps; sp).
  assert (eqp1 p0 p1) as ep1_01 by (apply eqps; sp).
  assert (eqa p0 p1 ep_01 a2 a1)
    as ea_21
      by (clear eib; generalize (eqas p1 p0 ep_10 ep); introv eqt;
          rw <- eqt in ea; clear eqt;
          generalize (eqas_sym  p1 p0 ep_10 ep_01); intro eqt;
          rw <- eqt; clear eqt;
          generalize (tspA p1 p0 ep_10); intro tsp;
          onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  assert (eqa p1 p0 ep_10 a1 a2)
    as ea_12
      by (generalize (eqas p1 p0 ep_10 ep); intro eqt; rw eqt; sp).
  assert (eqa1 p0 p1 ep1_01 a2 a1)
    as ea1_21
      by (generalize (eqas p0 p1 ep_01 ep1_01); intro eqt; rw <- eqt; sp).
  assert (eqb p1 p0 ep_10 a1 a2 ea_12 b1 b2)
    as eb_12 by (generalize (eqbs p1 p0 ep_10 ep a1 a2 ea_12 ea); intro eqt; rw eqt; sp).
  assert (eqb p0 p1 ep_01 a2 a1 ea_21 b2 b1)
    as eb_21
      by (generalize (eqbs_sym p1 p0 ep_10 ep_01 a1 a2 ea_12 ea_21); intro eqt;
          rw <- eqt;
          generalize (tspB p1 p0 ep_10 a1 a2 ea_12); intro tsp;
          onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp).
  assert (eqb1 p0 p1 ep1_01 a2 a1 ea1_21 b2 b1)
    as eb1_21
      by (generalize (eqbs p0 p1 ep_01 ep1_01 a2 a1 ea_21 ea1_21); intro eqt;
          rw <- eqt; sp).

  generalize (tpf6 p0 p1 ep1_01 a2 a1 ea1_21 b2 b1 eb1_21); intro ep2.
  rw <- eqps; rw <- eqps in ep2.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.

  (* last one *)
  rw <- eqps; rw <- eqps in tpf1.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma type_pfamily_computes {o} :
  forall lib TC (ts : cts(o)) T1 T2
         eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2
         P ap A bp ba B cp ca cb C p,
    computes_to_valc lib T1 (TC P ap A bp ba B cp ca cb C p)
    -> type_pfamily lib TC ts T1 T2 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> eq_type_pfamilies TC
    -> p1 = p
       # cp1 = cp # ca1 = ca # cb1 = cb
       # eqCs cp1 ca1 cb1 C1 cp ca cb C.
Proof.
  introv comp tpf eqpf.
  allunfold @type_pfamily; exrepnd; spcast.
  computes_to_eqval.
  apply eqpf in eq; repnd; subst.
  red_eqTs; subst; GC; sp.
Qed.

Lemma type_pfamily_computes2 {o} :
  forall lib TC (ts : cts(o)) T1 T2
         eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2
         P ap A bp ba B cp ca cb C p,
    computes_to_valc lib T2 (TC P ap A bp ba B cp ca cb C p)
    -> type_pfamily lib TC ts T1 T2 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> eq_type_pfamilies TC
    -> p2 = p
       # cp2 = cp # ca2 = ca # cb2 = cb
       # eqCs cp2 ca2 cb2 C2 cp ca cb C.
Proof.
  introv comp tpf eqpf.
  allunfold @type_pfamily; exrepnd; spcast.
  computes_to_eqval.
  apply eqpf in eq; repnd; subst.
  red_eqTs; subst; GC; sp.
Qed.

Ltac sp_pfam_step :=
  match goal with
      [ H1 : computes_to_valc ?lib ?T1 (?TC ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H2 : type_pfamily ?lib ?TC ?ts ?T1 ?T2 ?eqp1 ?eqa1 ?eqb1
                          ?cp1 ?ca1 ?cb1 ?C1
                          ?cp2 ?ca2 ?cb2 ?C2
                          ?p1 ?p2
      |- _ ] =>
      let e := fresh "e" in
      let h := fresh "h" in
      progress (generalize (type_pfamily_computes
                              lib TC ts T1 T2
                              eqp1 eqa1 eqb1
                              cp1 ca1 cb1 C1
                              cp2 ca2 cb2 C2
                              p1 p2
                              P ap A bp ba B cp ca cb C p
                              H1 H2);
                intro e;
                autodimp e h;
                try (complete auto);
                try (complete (apply eq_type_pfamilies_mkc_pw));
                try (complete (apply eq_type_pfamilies_mkc_pm));
                repnd; subst; red_eqTs; subst; GC)

    | [ H1 : computes_to_valc ?lib ?T2 (?TC ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H2 : type_pfamily ?lib ?TC ?ts ?T1 ?T2 ?eqp1 ?eqa1 ?eqb1
                          ?cp1 ?ca1 ?cb1 ?C1
                          ?cp2 ?ca2 ?cb2 ?C2
                          ?p1 ?p2
      |- _ ] =>
      let e := fresh "e" in
      let h := fresh "h" in
      progress (generalize (type_pfamily_computes2
                              lib TC ts T1 T2
                              eqp1 eqa1 eqb1
                              cp1 ca1 cb1 C1
                              cp2 ca2 cb2 C2
                              p1 p2
                              P ap A bp ba B cp ca cb C p
                              H1 H2);
                intro e;
                autodimp e h;
                try (complete auto);
                try (complete (apply eq_type_pfamilies_mkc_pw));
                try (complete (apply eq_type_pfamilies_mkc_pm));
                repnd; subst; red_eqTs; subst; GC)
  end.

Ltac sp_pfam := repeat sp_pfam_step.

Lemma type_pfamily_trans {o} :
  forall lib (ts : cts(o)) T1 T2 T3 TC
         eqp1 eqa1 eqb1
         eqp2 eqa2 eqb2
         eqp eqa eqb
         P ap A bp ba B cp ca cb C p
         P' ap' A' bp' ba' B' cp' ca' cb' C' p'
         cp1 ca1 cb1 C1 p1
         cp2 ca2 cb2 C2 p2
         cp3 ca3 cb3 C3 p3,
    computes_to_valc lib T1 (TC P ap A bp ba B cp ca cb C p)
    -> computes_to_valc lib T2 (TC P' ap' A' bp' ba' B' cp' ca' cb' C' p')
    -> eq_type_pfamilies TC
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> type_pfamily lib TC ts T1 T2
                    eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> type_pfamily lib TC ts T2 T3
                    eqp2 eqa2 eqb2
                    cp2 ca2 cb2 C2
                    cp3 ca3 cb3 C3
                    p2 p3
    -> type_pfamily lib TC ts T1 T3
                    eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp3 ca3 cb3 C3
                    p1 p3.
Proof.
  introv c1 c2 eqpf tspp tspa tspb eqCps tf1 tf2.
  sp_pfam.

  generalize (type_pfamily_sym
                lib TC ts T1 T2 eqp1 eqa1 eqb1
                cp ca cb C
                cp' ca' cb' C'
                p p'
                P ap A bp ba B cp ca cb C p
                eqp eqa eqb
                P' ap' A' bp' ba' B' cp' ca' cb' C'
                eqpf c1 tspp tspa tspb eqCps tf1);
    intro k; repnd; GC; red_eqTs; GC.

  applydup @type_sys_props_sym in tspp as tspp'.
  applydup (type_sys_props_fam_sym lib ts P P') in tspa as tspa'; auto.
  applydup (type_sys_props_fam_fam_sym lib ts P P' eqp ap A ap' A') in tspb as tspb'; auto.

  generalize (type_pfamily_eq_term_equals
                lib TC ts T2 T1 T3
                eqp1 eqa1 eqb1
                cp' ca' cb' C'
                cp ca cb C
                p' p
                eqp2 eqa2 eqb2
                cp' ca' cb' C'
                cp3 ca3 cb3 C3
                p' p3
                P' ap' A' bp' ba' B' cp' ca' cb' C' p'
                P eqp ap A eqa bp ba B eqb
                c2 eqpf tspp' tspa' tspb' k tf2);
    intro j; repnd; GC; red_eqTs; GC.

  clear k.

  allunfold @type_pfamily; exrepnd.
  repeat (ccomputes_to_eqval; apply eqpf in eq; repnd; subst; red_eqTs; subst; GC).
  exists P P3 ap ap3 A A3.
  exists bp bp3 ba ba3 B B3; dands; spcast; auto.


  (* equality of the Ps *)
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum P' P P3 eqp1 eqp2); sp.


  (* equality of the As *)
  intros p1 p2 ep1.
  dup ep1 as ep.
  apply k5 in ep.
  dup ep as ep2.
  apply j11 in ep2.
  assert (eqp p2 p2)
         as e2
         by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym;
             applydup @type_sys_props_implies_term_eq_trans in tspp as trans;
             apply trans with (t2 := p1); sp).
  assert (eqp2 p2 p2) as e22 by (apply j11 in e2; sp).

  generalize (tspa p1 p2 ep); intro tsp.
  generalize (tf5 p1 p2 ep1); intro eq1.
  generalize (tf11 p2 p2 e22); intro eq2.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum (substc p2 ap' A') (substc p1 ap A) (substc p2 ap3 A3) (eqa1 p1 p2 ep1) (eqa2 p2 p2 e22));
    intro k; repeat (autodimp k hyp); sp.


  (* equality of the Bs *)
  introv.
  generalize (tf6 p1 p2 ep a1 a2 ea); intro eq1.

  dup ep as ep12.
  apply k5 in ep12.
  assert (eqp p2 p2)
    as ep22
      by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym;
          applydup @type_sys_props_implies_term_eq_trans in tspp as trans;
          apply trans with (t2 := p1); sp).
  assert (eqp p1 p1)
    as ep11
      by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym;
          applydup @type_sys_props_implies_term_eq_trans in tspp as trans;
          apply trans with (t2 := p2); sp).
  assert (eqp p2 p1)
    as ep21 by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym; sp).
  dup ep22 as ep22'.
  apply j11 in ep22'.

  assert (eqa p1 p2 ep12 a1 a2)
    as ea' by (generalize (k6 p1 p2 ep12 ep); intro e; apply e; clear e; auto).

  assert (eqa2 p2 p2 ep22' a2 a2)
    as ea2
      by (generalize (j14 p2 p2 ep22 ep22'); intro e; apply e; clear e;
          generalize (k9 p1 p2 ep12 ep21); intro e; apply e in ea'; clear e;
          generalize (k8 p2 p1 ep21 ep22); intro e; apply e in ea'; clear e;
          generalize (tspa p2 p2 ep22); intro tsp;
          dup tspa as tsp1;
          apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tsp1; sp;
          apply tsp2 with (t2 := a1); sp;
          apply tsp0; sp).

  generalize (tf12 p2 p2 ep22' a2 a2 ea2); intro eq2.

  generalize (tspb p1 p2 ep12 a1 a2 ea'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum (lsubstc2 bp' p2 ba' a2 B')
                  (lsubstc2 bp p1 ba a1 B)
                  (lsubstc2 bp3 p2 ba3 a2 B3)
                  (eqb1 p1 p2 ep a1 a2 ea)
                  (eqb2 p2 p2 ep22' a2 a2 ea2));
    intro k; repeat (autodimp k hyp); sp.


  (* equality of the Cs *)
  introv eb.

  applydup @type_sys_props_implies_term_eq_sym in tspp as symp.
  applydup @type_sys_props_implies_term_eq_trans in tspp as transp.
  assert (eqp p1 p2) as ep12 by (apply k5; sp).
  assert (eqp2 p2 p2) as ep222 by (apply j11; apply transp with (t2 := p1); sp).
  assert (eqp p2 p2) as ep22 by (apply j11; sp).
  assert (eqp p2 p1) as ep21 by sp.

  assert (eqa p1 p2 ep12 a1 a2)
    as ea' by (generalize (k6 p1 p2 ep12 ep); intro e; apply e; clear e; auto).

  assert (eqa p2 p1 ep21 a2 a1)
    as ea21
      by (generalize (k9 p1 p2 ep12 ep21); intro e; apply e in ea'; clear e; sp;
          generalize (tspa p2 p1 ep21); intro tsp;
          dup tspa as tsp1;
          apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tsp1; sp;
          apply tsp0; sp).

  assert (eqa p2 p2 ep22 a2 a2)
    as ea''
      by (generalize (k8 p2 p1 ep21 ep22); intro e; apply e in ea21; clear e;
          generalize (tspa p2 p2 ep22); intro tsp;
          dup tspa as tsp1;
          apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tsp1; sp;
          apply tsp2 with (t2 := a1); sp;
          apply tsp0; sp).

  assert (eqa2 p2 p2 ep222 a2 a2)
    as ea2 by (generalize (j14 p2 p2 ep22 ep222); intro e; apply e; sp).

  assert (eqb p1 p2 ep12 a1 a2 ea' b1 b2)
    as eb' by (generalize (k7 p1 p2 ep12 ep a1 a2 ea' ea); intro e; apply e in eb; sp).

  assert (eqb2 p2 p2 ep222 a2 a2 ea2 b2 b2)
    as eb''
         by (generalize (j17 p2 p2 ep22 ep222 a2 a2 ea'' ea2); intro e; apply e; clear e;
             generalize (k11 p1 p2 ep12 ep21 a1 a2 ea' ea21); intro e; apply e in eb'; clear e;
             generalize (k10 p2 p1 ep21 ep22 a2 a1 ea21 ea''); intro e; apply e; clear e;
             dup tspb as tsp1;
             apply @type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tsp1; sp;
             apply tsp2 with (t2 := b1); sp;
             apply tsp0; sp).

  generalize (tf7 p1 p2 ep a1 a2 ea b1 b2); intro e1; dest_imp e1 hyp.
  generalize (tf13 p2 p2 ep222 a2 a2 ea2 b2 b2); intro e2; dest_imp e2 hyp.
  apply k5.
  apply k5 in e1.
  apply j11 in e2.
  apply transp with (t2 := lsubstc3 cp' p2 ca' a2 cb' b2 C'); sp.


  (* equality of the ps *)
  apply j11 in tf2.
  apply k5 in tf1.
  apply k5.
  applydup @type_sys_props_implies_term_eq_sym in tspp as sym.
  applydup @type_sys_props_implies_term_eq_trans in tspp as trans.
  apply trans with (t2 := p'); sp.
Qed.

Lemma eq_term_equals_fam_prop1 {o} :
  forall lib (ts : cts(o)) eqp eqa eqp1 eqa1
         P P' ap A ap' A' ap1 A1,
    eq_term_equals eqp eqp1
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> equal_fams ts eqp1 ap1 A1 ap A eqa1
    -> eq_term_equals_fam eqp eqa eqp1 eqa1.
Proof.
  introv eqps tspp tspa eqfamsa.
  introv.

  assert (eqp p' p) as ep' by (apply type_sys_props_implies_term_eq_sym in tspp; sp).
  assert (eqp1 p' p) as ep1' by (apply eqps; sp).

  generalize (tspa p' p ep'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

  generalize (eqfamsa p p' ep1); intro e.
  apply tygs in e; sp.
  generalize (uv (substc p ap1 A1) (eqa1 p p' ep1)); intro eqt; repeat (autodimp eqt hyp).
  apply eq_term_equals_trans with (eq2 := eqa p' p ep'); sp.

  apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspa; sp.
Qed.

Lemma eq_term_equals_fam_fam_prop1 {o} :
  forall lib (ts : cts(o)) eqp eqa eqb eqp1 eqa1 eqb1
         P P'
         ap A ap' A'
         bp ba B bp' ba' B'
         bp1 ba1 B1,
  eq_term_equals eqp eqp1
  -> eq_term_equals_fam eqp eqa eqp1 eqa1
  -> type_sys_props lib ts P P' eqp
  -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
  -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
  -> equal_fams_fams ts eqp1 eqa1 bp1 ba1 B1 bp ba B eqb1
  -> eq_term_equals_fam_fam eqp eqa eqb eqp1 eqa1 eqb1.
Proof.
  introv eqps eqas tspp tspa tspb eqfamsb.
  introv.
  intros a a' ea ea1.

  assert (eqp p' p) as ep' by (apply type_sys_props_implies_term_eq_sym in tspp; sp).
  assert (eqp1 p' p) as ep1' by (apply eqps; sp).

  assert (eqa p' p ep' a' a)
    as ea'
      by (dup tspa as s;
          apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in s; sp;
          generalize (s p p' ep ep'); intro e; apply e;
          apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspa; repnd; sp;
          apply tspa0; sp).

  apply eq_term_equals_trans with (eq2 := eqb p' p ep' a' a ea').

  apply @type_sys_props_fam_fam_implies_eq_fam_fam_sym
  with (P := P)
         (P' := P')
         (ap := ap)
         (A := A)
         (ap' := ap')
         (A' := A') in tspb; sp.

  generalize (eqfamsb p p' ep1 a a' ea1); intro e1.
  generalize (tspb p' p ep' a' a ea'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tygs in e1; sp.
  generalize (uv (lsubstc2 bp1 p ba1 a B1)
                 (eqb1 p p' ep1 a a' ea1)).
  intro eqt; repeat (autodimp eqt hyp).
Qed.

Lemma type_sys_props_fam_uv {o} :
  forall lib (ts : cts(o)) eqp1 eqa1 eqp2 eqa2 ap1 A1 ap2 A2,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> type_sys_props_fam lib ts eqp1 ap1 A1 ap2 A2 eqa1
    -> type_sys_props_fam lib ts eqp2 ap1 A1 ap2 A2 eqa2.
Proof.
  introv eqps eqas tspf.
  introv.
  dup ep as ep'.
  apply eqps in ep'.
  generalize (tspf p p' ep'); intro tsp.
  apply type_sys_props_uv with (eq := eqa1 p p' ep'); auto.
Qed.

Lemma equal_fams_sym {o} :
  forall lib (ts : cts(o)) eqp eqa ap1 A1 ap2 A2 ap' A',
    term_equality_symmetric eqp
    -> type_sys_props_fam lib ts eqp ap2 A2 ap' A' eqa
    -> equal_fams ts eqp ap1 A1 ap2 A2 eqa
    -> equal_fams ts eqp ap2 A2 ap1 A1 eqa.
Proof.
  introv sym tspf ef.
  introv.

  dup ep as ep'.
  apply sym in ep'.

  generalize (ef p2 p1 ep'); intro e.
  generalize (tspf p1 p2 ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  applydup tygs in tygt; auto.
  generalize (dum (substc p1 ap2 A2) (substc p2 ap1 A1) (substc p2 ap' A')
                  (eqa p2 p1 ep') (eqa p1 p2 ep));
    intro k; repeat (dest_imp k hyp); repnd.
  generalize (dum (substc p2 ap' A') (substc p2 ap1 A1) (substc p1 ap2 A2)
                  (eqa p1 p2 ep) (eqa p1 p2 ep));
    intro j; repeat (dest_imp j hyp); repnd.
  apply tygs in j1; sp.
Qed.

Lemma type_sys_props_fam_fam_uv {o} :
  forall lib (ts : cts(o)) eqp1 eqa1 eqb1 eqp2 eqa2 eqb2 bp1 ba1 B1 bp2 ba2 B2,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> type_sys_props_fam_fam lib ts eqp1 eqa1 bp1 ba1 B1 bp2 ba2 B2 eqb1
    -> type_sys_props_fam_fam lib ts eqp2 eqa2 bp1 ba1 B1 bp2 ba2 B2 eqb2.
Proof.
  introv eqps eqas eqbs tspf.
  introv.
  dup ep as ep'.
  apply eqps in ep'.
  dup ea as ea'.
  generalize (eqas p p' ep' ep); intro e; apply e in ea'; clear e.
  generalize (tspf p p' ep' a a' ea'); intro tsp.
  apply type_sys_props_uv with (eq := eqb1 p p' ep' a a' ea'); auto.
  apply eqbs.
Qed.

Lemma equal_fams_fams_sym {o} :
  forall lib (ts : cts(o)) eqp eqa eqb bp1 ba1 B1 bp2 ba2 B2 bp' ba' B',
    term_equality_symmetric eqp
    -> eq_fam_sym eqp eqa
    -> term_equality_symmetric_fam eqp eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp2 ba2 B2 bp' ba' B' eqb
    -> equal_fams_fams ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> equal_fams_fams ts eqp eqa bp2 ba2 B2 bp1 ba1 B1 eqb.
Proof.
  introv symp efs syma tspff eff.
  introv.

  dup ep as ep'.
  apply symp in ep'.

  dup ea as ea'.
  generalize (efs p1 p2 ep ep'); intro e; apply e in ea'; clear e.
  generalize (syma p2 p1 ep'); intro e; apply e in ea'; clear e.

  generalize (eff p2 p1 ep' a2 a1 ea'); intro e.
  generalize (tspff p1 p2 ep a1 a2 ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  applydup tygs in tygt; auto.
  generalize (dum (lsubstc2 bp2 p1 ba2 a1 B2)
                  (lsubstc2 bp1 p2 ba1 a2 B1)
                  (lsubstc2 bp' p2 ba' a2 B')
                  (eqb p2 p1 ep' a2 a1 ea')
                  (eqb p1 p2 ep a1 a2 ea));
    intro k; repeat (dest_imp k hyp); repnd.
  generalize (dum (lsubstc2 bp' p2 ba' a2 B')
                  (lsubstc2 bp1 p2 ba1 a2 B1)
                  (lsubstc2 bp2 p1 ba2 a1 B2)
                  (eqb p1 p2 ep a1 a2 ea)
                  (eqb p1 p2 ep a1 a2 ea));
    intro j; repeat (dest_imp j hyp); repnd.
  apply tygs in j1; sp.
Qed.

Lemma tsp_sym {o} :
  forall lib (ts : cts(o)) P1 P2 eqp p1 p2,
    type_sys_props lib ts P1 P2 eqp
    -> eqp p1 p2
    -> eqp p2 p1.
Proof.
  introv tsp e.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma tsp_fam_sym {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> eqa p1 p2 ep a1 a2
    -> {ep' : eqp p2 p1 , eqa p2 p1 ep' a2 a1}.
Proof.
  introv tspp tspa e.
  generalize (tsp_sym lib ts P1 P2 eqp p1 p2 tspp ep); intro ep'.
  exists ep'.
  generalize (type_sys_props_fam_implies_eq_fam_sym lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa tspp tspa); intro syma.
  generalize (syma p1 p2 ep ep'); intro eq; apply eq; clear eq.
  generalize (tspa p1 p2 ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma tsp_fam_fam_sym {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa bp1 ba1 B1 bp2 ba2 B2 eqb p1 p2 ep a1 a2 ea b1 b2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> eqb p1 p2 ep a1 a2 ea b1 b2
    -> {ep' : eqp p2 p1 , {ea' : eqa p2 p1 ep' a2 a1 , eqb p2 p1 ep' a2 a1 ea' b2 b1}}.
Proof.
  introv tspp tspa tspb e.
  generalize (tsp_fam_sym lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep' ea'].
  exists ep' ea'.
  generalize (type_sys_props_fam_fam_implies_eq_fam_fam_sym
                lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa bp1 ba1 B1 bp2 ba2 B2 eqb tspp tspa tspb);
    intro symb.
  generalize (symb p1 p2 ep ep' a1 a2 ea ea'); intro eq; apply eq; clear eq.
  generalize (tspb p1 p2 ep a1 a2 ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma tsp_refl_right {o} :
  forall lib (ts : cts(o)) P1 P2 eqp p1 p2,
    type_sys_props lib ts P1 P2 eqp
    -> eqp p1 p2
    -> eqp p2 p2.
Proof.
  introv tsp e.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := p1); sp.
Qed.

Lemma tsp_fam_refl_right {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> eqa p1 p2 ep a1 a2
    -> {ep' : eqp p2 p2 , eqa p2 p2 ep' a2 a2}.
Proof.
  introv tspp tspa e.
  generalize (tsp_refl_right lib ts P1 P2 eqp p1 p2 tspp ep); intro ep'.
  exists ep'.
  generalize (tsp_implies_eq_fam_refl_right lib ts eqp ap1 A1 ap2 A2 eqa tspa); intro rr.
  generalize (rr p1 p2 ep ep'); intro eq; apply eq; clear eq.
  generalize (tspa p1 p2 ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := a1); sp.
Qed.

Lemma tsp_fam_fam_refl_right {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa bp1 ba1 B1 bp2 ba2 B2 eqb p1 p2 ep a1 a2 ea b1 b2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> eqb p1 p2 ep a1 a2 ea b1 b2
    -> {ep' : eqp p2 p2 , {ea' : eqa p2 p2 ep' a2 a2 , eqb p2 p2 ep' a2 a2 ea' b2 b2}}.
Proof.
  introv tspp tspa tspb e.
  generalize (tsp_fam_refl_right lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep' ea'].
  exists ep' ea'.
  generalize (tsp_implies_eq_fam_fam_refl_right
                lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb tspb);
    intro rr.
  generalize (rr p1 p2 ep ep' a1 a2 ea ea'); intro eq; apply eq; clear eq.
  generalize (tspb p1 p2 ep a1 a2 ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := b1); sp.
Qed.

(* Similar to type_pfamily_sym2, but here we know what T2 computes to instead of T1 *)
Lemma type_pfamily_sym2 {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2
         P ap A bp ba B cp ca cb C p
         eqp eqa eqb
         P' ap' A' bp' ba' B' cp' ca' cb' C',
    eq_type_pfamilies TC
    -> computes_to_valc lib T2 (TC P ap A bp ba B cp ca cb C p)
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> type_pfamily lib TC ts T1 T2 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> p = p2
       # cp = cp2 # ca = ca2 # cb = cb2
       # eqCs cp ca cb C cp2 ca2 cb2 C2
       (* eqp = eqp1 *)
       # eq_term_equals eqp eqp1
       (* eqa = eqa1 *)
       # eq_term_equals_fam eqp eqa eqp1 eqa1
       (* eqb = eqb1 *)
       # eq_term_equals_fam_fam eqp eqa eqb eqp1 eqa1 eqb1
       (* eqa refl left *)
       # eq_fam_refl_left eqp eqa
       (* eqa sym *)
       # eq_fam_sym eqp eqa
       (* eqb refl left *)
       # eq_fam_fam_refl_left eqp eqa eqb
       (* eqb sym *)
       # eq_fam_fam_sym eqp eqa eqb
       (* type_pfamily sym *)
       # type_pfamily lib TC ts T2 T1 eqp1 eqa1 eqb1
                      cp2 ca2 cb2 C2
                      cp1 ca1 cb1 C1
                      p2 p1.
Proof.
  introv eqtc comp tspP tspA tspB eqC tpf.
  sp_pfam.
  allunfold @type_pfamily; exrepnd.
  try (rw fold_equal_fams in tpf4).
  try (rw fold_equal_fams_fams in tpf5).
  try (rw fold_equal_Cparams in tpf6).
  spcast; computes_to_eqval.
  apply eqtc in eq; repnd; subst; red_eqTs; subst; GC.

  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; GC.
  prove_and x; red_eqTs; GC.


  (* eqp = eqp1 *)
  prove_and eqps.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tygs in tpf3; sp.
  apply uv with (T3 := P1); sp.


  (* eqa = eqa1 *)
  prove_and eqas.
  apply (eq_term_equals_fam_prop1 lib)
  with (ts := ts)
         (P := P)
         (P' := P')
         (ap := ap)
         (A := A)
         (ap' := ap')
         (A' := A')
         (ap1 := ap1)
         (A1 := A1); sp.


  (* eqb = eqb1 *)
  prove_and eqbs.
  apply (eq_term_equals_fam_fam_prop1 lib)
  with (ts := ts)
         (P := P)
         (P' := P')
         (ap := ap)
         (A := A)
         (ap' := ap')
         (A' := A')
         (bp := bp)
         (ba := ba)
         (B := B)
         (bp' := bp')
         (ba' := ba')
         (B' := B')
         (bp1 := bp1)
         (ba1 := ba1)
         (B1 := B1); sp.


  (* eqa refl left *)
  prove_and eqas_refl_l.
  apply tsp_implies_eq_fam_refl_left in tspA; sp.


  (* eqa sym *)
  prove_and eqas_sym.
  apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspA; sp.


  (* eqb refl left *)
  prove_and eqbs_relf_l.
  apply tsp_implies_eq_fam_fam_refl_left in tspB; sp.


  (* eqb sym *)
  prove_and eqbs_sym.
  apply @type_sys_props_fam_fam_implies_eq_fam_fam_sym
        with (P := P) (P' := P') (ap := ap) (A := A) (ap' := ap') (A' := A') in tspB; sp.


  (* type_pfamily sym *)
  exists P P1 ap ap1 A A1.
  exists bp bp1 ba ba1 B B1.
  try (rw fold_equal_fams).
  try (rw fold_equal_fams_fams).
  try (rw fold_equal_Cparams).

  prove_and c1; spcast; GC; try (complete (spcast; sp)).
  prove_and c2; spcast; GC; try (complete (spcast; sp)).

  prove_and eP.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tygs; sp.

  prove_and eqA.
  apply (equal_fams_sym lib) with (ap' := ap') (A' := A'); sp.
  apply type_sys_props_implies_term_eq_sym in tspP.
  apply term_equality_symmetric_eq_term_equals with (eq := eqp); sp.
  apply @type_sys_props_fam_uv with (eqp1 := eqp) (eqa1 := eqa); sp.

  prove_and eqB.
  apply (equal_fams_fams_sym lib) with (bp' := bp') (ba' := ba') (B' := B'); sp.
  apply type_sys_props_implies_term_eq_sym in tspP.
  apply term_equality_symmetric_eq_term_equals with (eq := eqp); sp.
  apply @type_sys_props_fam_uv with (eqp2 := eqp1) (eqa2 := eqa1) in tspA; sp.
  apply @type_sys_props_fam_implies_eq_fam_sym with (P := P) (P' := P') in tspA; sp.
  apply type_sys_props_uv with (eq := eqp); sp.
  apply @type_sys_props_fam_uv with (eqp2 := eqp1) (eqa2 := eqa1) in tspA; sp.
  apply @type_sys_props_fam_implies_sym_trans_respeq with (P := P) (P' := P') in tspA; sp.
  apply type_sys_props_uv with (eq := eqp); sp.
  apply @type_sys_props_fam_fam_uv with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.

  prove_and eqCps.

  introv eb.
  dup tspP as tspp1.
  apply type_sys_props_uv with (eq' := eqp1) in tspp1; sp.
  dup tspA as tspa1.
  apply @type_sys_props_fam_uv with (eqp2 := eqp1) (eqa2 := eqa1) in tspa1; sp.
  dup tspB as tspb1.
  apply @type_sys_props_fam_fam_uv with (eqp2 := eqp1) (eqa2 := eqa1) (eqb2 := eqb1) in tspb1; sp.
  apply (tsp_sym lib) with (ts := ts) (P1 := P) (P2 := P'); auto.
  dup eb as eb'.
  apply (tsp_fam_fam_sym lib)
        with
        (ts := ts) (P1 := P) (P2 := P') (eqp := eqp1)
        (ap1 := ap) (A1 := A) (ap2 := ap') (A2 := A') (p1 := p0) (p2 := p2)
        (bp1 := bp) (ba1 := ba) (B1 := B) (bp2 := bp') (ba2 := ba') (B2 := B')
        in eb'; auto.
  exrepnd.
  apply tpf6 with (ep := ep') (ea := ea'); sp.

  (* last one *)
  rw <- eqps; rw <- eqps in tpf1.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
Qed.

Lemma equal_fams_trans {o} :
  forall lib (ts : cts(o)) eqp eqa eqp' eqa' P1 P2 ap1 A1 ap A ap2 A2 ap' A',
    eq_term_equals eqp eqp'
    -> type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> equal_fams ts eqp ap1 A1 ap A eqa
    -> equal_fams ts eqp' ap A ap2 A2 eqa'
    -> equal_fams ts eqp ap1 A1 ap2 A2 eqa.
Proof.
  introv eqps tspp tspa f1 f2.
  introv.
  generalize (f1 p1 p2 ep); intro e1.
  generalize (tsp_refl_right lib ts P1 P2 eqp p1 p2 tspp ep); intro ep'.
  dup ep' as ep''.
  apply eqps in ep''.
  generalize (f2 p2 p2 ep''); intro e2.
  generalize (tspa p2 p2 ep'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum (substc p2 ap A) (substc p1 ap1 A1) (substc p2 ap2 A2) (eqa p1 p2 ep) (eqa' p2 p2 ep'')); intro k.
  repeat (dest_imp k hyp); try (complete (apply tygs; auto)); repnd.
Qed.

Lemma equal_fams_fams_trans {o} :
  forall lib (ts : cts(o)) eqp eqa eqb eqp' eqa' eqb' P1 P2 ap1 A1 ap2 A2 bp1 ba1 B1 bp ba B bp2 ba2 B2 bp' ba' B',
    eq_term_equals eqp eqp'
    -> eq_term_equals_fam eqp eqa eqp' eqa'
    -> type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_fams_fams ts eqp eqa bp1 ba1 B1 bp ba B eqb
    -> equal_fams_fams ts eqp' eqa' bp ba B bp2 ba2 B2 eqb'
    -> equal_fams_fams ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb.
Proof.
  introv eqps eqas tspp tspa tspb f1 f2.
  introv.
  generalize (f1 p1 p2 ep a1 a2 ea); intro e1.
  generalize (tsp_fam_refl_right lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep' ea'].
  dup ep' as ep''.
  apply eqps in ep''.
  dup ea' as ea''.
  apply (eqas p2 p2 ep' ep'') in ea''.
  generalize (f2 p2 p2 ep'' a2 a2 ea''); intro e2.
  generalize (tspb p2 p2 ep' a2 a2 ea'); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum (lsubstc2 bp p2 ba a2 B)
                  (lsubstc2 bp1 p1 ba1 a1 B1)
                  (lsubstc2 bp2 p2 ba2 a2 B2)
                  (eqb p1 p2 ep a1 a2 ea)
                  (eqb' p2 p2 ep'' a2 a2 ea'')); intro k.
  repeat (dest_imp k hyp); try (complete (apply tygs; auto)); repnd.
Qed.

Lemma equal_Cparams_trans {o} :
  forall lib (ts : cts(o)) P1 P2 ap1 A1 ap2 A2 bp1 ba1 B1 bp2 ba2 B2
         eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
         cp1 ca1 cb1 C1
         cp ca cb C
         cp2 ca2 cb2 C2,
    eq_term_equals eqp1 eqp2
    -> eq_term_equals_fam eqp1 eqa1 eqp2 eqa2
    -> eq_term_equals_fam_fam eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
    -> type_sys_props lib ts P1 P2 eqp1
    -> type_sys_props_fam lib ts eqp1 ap1 A1 ap2 A2 eqa1
    -> type_sys_props_fam_fam lib ts eqp1 eqa1 bp1 ba1 B1 bp2 ba2 B2 eqb1
    -> equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp ca cb C
    -> equal_Cparams eqp2 eqa2 eqb2 cp ca cb C cp2 ca2 cb2 C2
    -> equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp2 ca2 cb2 C2.
Proof.
  introv eqps eqas eqbs tspp tspa tspb ecs1 ecs2.
  introv eb.
  generalize (ecs1 p p' ep a a' ea b b' eb); intro e1.
  generalize (tsp_fam_fam_refl_right
                lib ts P1 P2 eqp1 ap1 A1 ap2 A2 eqa1 bp1 ba1 B1 bp2 ba2 B2 eqb1 p p' ep a a' ea b b'
                tspp tspa tspb eb); intro k.
  destruct k as [ep' k].
  destruct k as [ea' eb'].
  dup ep' as ep''.
  dup ea' as ea''.
  dup eb' as eb''.
  apply eqps in ep''.
  apply (eqas p' p' ep' ep'') in ea''.
  apply (eqbs p' p' ep' ep'' a' a' ea' ea'') in eb''.
  generalize (ecs2 p' p' ep'' a' a' ea'' b' b' eb''); intro e2.
  apply eqps in e2.
  apply type_sys_props_implies_term_eq_trans in tspp.
  apply tspp with (t2 := lsubstc3 cp p' ca a' cb b' C); sp.
Qed.

(* This is like type_pfamily_trans, but we only know what T2 computes to *)
Lemma type_pfamily_trans2 {o} :
  forall lib (ts : cts(o)) T1 T2 T3 TC
         eqp1 eqa1 eqb1
         eqp2 eqa2 eqb2
         eqp eqa eqb
         P ap A bp ba B cp ca cb C p
         P' ap' A' bp' ba' B' cp' ca' cb' C'
         cp1 ca1 cb1 C1 p1
         cp2 ca2 cb2 C2 p2
         cp3 ca3 cb3 C3 p3,
    computes_to_valc lib T2 (TC P ap A bp ba B cp ca cb C p)
    -> eq_type_pfamilies TC
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> type_pfamily lib TC ts T1 T2
                    eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> type_pfamily lib TC ts T2 T3
                    eqp2 eqa2 eqb2
                    cp2 ca2 cb2 C2
                    cp3 ca3 cb3 C3
                    p2 p3
    -> (type_pfamily lib TC ts T1 T3
                     eqp1 eqa1 eqb1
                     cp1 ca1 cb1 C1
                     cp3 ca3 cb3 C3
                     p1 p3
        # equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp3 ca3 cb3 C3
        # eqp1 p1 p3).
Proof.
  introv c eqpf tspp tspa tspb eqCps tf1 tf2.
  sp_pfam.

  generalize (type_pfamily_sym2
                lib TC ts T1 T2
                eqp1 eqa1 eqb1
                cp1 ca1 cb1 C1
                cp ca cb C
                p1 p
                P ap A bp ba B cp ca cb C p
                eqp eqa eqb
                P' ap' A' bp' ba' B' cp' ca' cb' C'
                eqpf c tspp tspa tspb eqCps tf1);
    intro k; repnd; GC; red_eqTs; GC.

  generalize (type_pfamily_eq_term_equals
                lib TC ts T2 T1 T3
                eqp1 eqa1 eqb1 cp ca cb C cp1 ca1 cb1 C1 p p1
                eqp2 eqa2 eqb2 cp ca cb C cp3 ca3 cb3 C3 p p3
                P ap A bp ba B cp ca cb C p
                P' eqp ap' A' eqa bp' ba' B' eqb c eqpf tspp tspa tspb k tf2);
    intro j; repnd; GC; red_eqTs; GC.

  clear k.

  allunfold @type_pfamily; exrepnd.
  repeat (ccomputes_to_eqval; apply eqpf in eq; repnd; subst; red_eqTs; subst; GC).
  try (rw fold_equal_fams in tf11).
  try (rw fold_equal_fams in tf5).
  try (rw fold_equal_fams_fams in tf12).
  try (rw fold_equal_fams_fams in tf6).
  try (fold (equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp ca cb C) in tf13).
  try (fold (equal_Cparams eqp2 eqa2 eqb2 cp ca cb C cp3 ca3 cb3 C3) in tf7).

  dands.

  exists P1 P3 ap1 ap3 A1 A3.
  exists bp1 bp3 ba1 ba3 B1 B3; dands; spcast; auto;
  try (rw fold_equal_fams);
  try (rw fold_equal_fams_fams);
  try (fold (equal_Cparams eqp1 eqa1 eqb1 cp1 ca1 cb1 C1 cp3 ca3 cb3 C3)).


  (* equality of the Ps *)
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (dum P P1 P3 eqp1 eqp2); sp.


  (* equality of the As *)
  apply (equal_fams_trans lib) with (P1 := P) (P2 := P') (ap := ap) (A := A) (ap' := ap') (A' := A') (eqp' := eqp2) (eqa' := eqa2); sp.
  apply type_sys_props_uv with (eq := eqp); sp.
  apply @type_sys_props_fam_uv with (eqp1 := eqp) (eqa1 := eqa); sp.



  (* equality of the Bs *)
  apply (equal_fams_fams_trans lib)
        with
        (eqp' := eqp2) (eqa' := eqa2) (eqb' := eqb2)
        (P1 := P) (P2 := P') (ap1 := ap) (A1 := A) (ap2 := ap') (A2 := A')
        (bp := bp) (ba := ba) (B := B) (bp' := bp') (ba' := ba') (B' := B'); sp.
  apply type_sys_props_uv with (eq := eqp); sp.
  apply @type_sys_props_fam_uv with (eqp1 := eqp) (eqa1 := eqa); sp.
  apply @type_sys_props_fam_fam_uv with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); sp.


  (* equality of the Cs *)
  auto.
  generalize (equal_Cparams_trans
                lib ts P P' ap A ap' A' bp ba B bp' ba' B'
                eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
                cp1 ca1 cb1 C1
                cp ca cb C
                cp3 ca3 cb3 C3); intro k.
  repeat (autodimp k hyp).
  apply type_sys_props_uv with (eq := eqp); auto.
  apply @type_sys_props_fam_uv with (eqp1 := eqp) (eqa1 := eqa); auto.
  apply @type_sys_props_fam_fam_uv with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); auto.


  (* equality of the ps *)
  apply j11 in tf2.
  apply k5 in tf1.
  apply k5.
  applydup @type_sys_props_implies_term_eq_sym in tspp as sym.
  applydup @type_sys_props_implies_term_eq_trans in tspp as trans.
  apply trans with (t2 := p); sp.


  (* equal_Cparams *)
  auto.
  generalize (equal_Cparams_trans
                lib ts P P' ap A ap' A' bp ba B bp' ba' B'
                eqp1 eqa1 eqb1 eqp2 eqa2 eqb2
                cp1 ca1 cb1 C1
                cp ca cb C
                cp3 ca3 cb3 C3); intro k; repeat (autodimp k hyp); sp.
  apply type_sys_props_uv with (eq := eqp); auto.
  apply @type_sys_props_fam_uv with (eqp1 := eqp) (eqa1 := eqa); auto.
  apply @type_sys_props_fam_fam_uv with (eqp1 := eqp) (eqa1 := eqa) (eqb1 := eqb); auto.

  (* finally, trans of the eqps *)
  applydup @type_sys_props_implies_term_eq_trans in tspp as trans.
  apply k5.
  apply trans with (t2 := p); sp.
  apply k5; sp.
  apply j11; sp.
Qed.

Lemma type_pfamily_refl_right {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp1 eqa1 eqb1
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2
         P ap A bp ba B cp ca cb C p
         eqp eqa eqb
         P' ap' A' bp' ba' B' cp' ca' cb' C',
    eq_type_pfamilies TC
    -> computes_to_valc lib T1 (TC P ap A bp ba B cp ca cb C p)
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp ca cb C cp' ca' cb' C'
    -> type_pfamily lib TC ts T1 T2 eqp1 eqa1 eqb1
                    cp1 ca1 cb1 C1
                    cp2 ca2 cb2 C2
                    p1 p2
    -> (type_pfamily lib TC ts T2 T2 eqp1 eqa1 eqb1
                     cp2 ca2 cb2 C2
                     cp2 ca2 cb2 C2
                     p2 p2
       # equal_Cparams eqp1 eqa1 eqb1 cp2 ca2 cb2 C2 cp2 ca2 cb2 C2
       # eqp1 p2 p2).
Proof.
  introv eqpf c tspp tspa tspb eqcs tpf.
  sp_pfam.

  generalize (type_pfamily_sym
                lib TC ts T1 T2 eqp1 eqa1 eqb1 cp ca cb C cp2 ca2 cb2 C2 p p2
                P ap A bp ba B cp ca cb C p
                eqp eqa eqb
                P' ap' A' bp' ba' B' cp' ca' cb' C'
                eqpf c tspp tspa tspb eqcs tpf);
    intro k; repnd; subst; GC; red_eqTs; subst; GC.

  generalize (type_pfamily_trans2
                lib ts T2 T1 T2 TC
                eqp1 eqa1 eqb1
                eqp1 eqa1 eqb1
                eqp eqa eqb
                P ap A bp ba B cp ca cb C p
                P' ap' A' bp' ba' B' cp' ca' cb' C'
                cp2 ca2 cb2 C2 p2
                cp ca cb C p
                cp2 ca2 cb2 C2 p2
                c eqpf tspp tspa tspb eqcs k tpf); sp.
Qed.

Lemma type_pfamily_implies_equal_Cparams {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2,
    type_pfamily TC lib ts T1 T2 eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2.
Proof.
  introv k.
  destruct k; sp.
Qed.

Lemma type_pfamily_implies_params {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2,
    type_pfamily TC lib ts T1 T2 eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 p1 p2
    -> eqp p1 p2.
Proof.
  introv k.
  destruct k; sp.
Qed.

Lemma equal_fams_refl {o} :
  forall lib (ts : cts(o)) eqp eqa ap1 A1 ap2 A2,
    term_equality_symmetric eqp
    -> term_equality_transitive eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> equal_fams ts eqp ap1 A1 ap1 A1 eqa.
Proof.
  introv symp transp tspa.
  introv.
  assert (eqp p2 p2) as ep2 by (apply transp with (t2 := p1); sp).
  generalize (tspa p1 p2 ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tspa p2 p2 ep2); intro tsp2.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (dum (substc p2 ap2 A2) (substc p1 ap1 A1) (substc p2 ap1 A1)
                  (eqa p1 p2 ep) (eqa p2 p2 ep2)); intro k.
  repeat (dest_imp k hyp).
  apply tygs2; sp.
Qed.

Lemma equal_fams_cequivc {o} :
  forall lib (ts : cts(o)) eqp eqa P P' ap1 A1 ap2 A2 ap A,
    bcequivc lib [ap1] A1 [ap2] A2
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap A eqa
    -> equal_fams ts eqp ap1 A1 ap2 A2 eqa.
Proof.
  introv bceq tspp tspa.
  introv.
  assert (ts (substc p1 ap1 A1) (substc p2 ap1 A1) (eqa p1 p2 ep))
    as e1
      by (revert p1 p2 ep; rw @fold_equal_fams;
          apply (equal_fams_refl lib) with (ap2 := ap) (A2 := A); sp;
          try (complete (apply type_sys_props_implies_term_eq_sym in tspp; sp));
          try (complete (apply type_sys_props_implies_term_eq_trans in tspp; sp))).

  assert (eqp p2 p2)
    as ep2
      by (applydup @type_sys_props_implies_term_eq_sym in tspp as sym;
          applydup @type_sys_props_implies_term_eq_trans in tspp as trans;
          apply trans with (t2 := p1); sp).

  generalize (tspa p2 p2 ep2); intro tsp.
  generalize (bcequivc1 lib ap1 ap2 A1 A2 bceq p2); intro ceq.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tyvr (substc p2 ap1 A1) (substc p2 ap2 A2)); intro k.
  repeat (autodimp k hyp).
  generalize (dum (substc p2 ap1 A1) (substc p1 ap1 A1) (substc p2 ap2 A2)
                  (eqa p1 p2 ep) (eqa p2 p2 ep2)); sp.
Qed.

Lemma equal_fams_fams_refl {o} :
  forall lib (ts : cts(o)) eqp eqa eqb P1 P2 ap1 A1 ap2 A2 bp1 ba1 B1 bp2 ba2 B2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> equal_fams_fams ts eqp eqa bp1 ba1 B1 bp1 ba1 B1 eqb.
Proof.
  introv tspp tspa tspb.
  introv.
  generalize (tsp_fam_refl_right
                lib ts P1 P2 eqp
                ap1 A1 ap2 A2 eqa
                p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep' ea'].
  generalize (tspb p1 p2 ep a1 a2 ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tspb p2 p2 ep' a2 a2 ea'); intro tsp2.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  generalize (dum (lsubstc2 bp2 p2 ba2 a2 B2)
                  (lsubstc2 bp1 p1 ba1 a1 B1)
                  (lsubstc2 bp1 p2 ba1 a2 B1)
                  (eqb p1 p2 ep a1 a2 ea)
                  (eqb p2 p2 ep' a2 a2 ea')); intro k.
  repeat (dest_imp k hyp).
  apply tygs2; sp.
Qed.

Lemma bcequivc2 {o} :
  forall lib v1 u1 t1 v2 u2 t2,
    @bcequivc o lib [v1,u1] t1 [v2,u2] t2
    -> forall v u,
         cequivc lib (lsubstc2 v1 v u1 u t1) (lsubstc2 v2 v u2 u t2).
Proof.
  unfold bcequivc, cequivc, get_cvterm, substc.
  introv Hbc.
  intros v u.
  destruct_cterms; allsimpl.
  unfold csubst; simpl.
  apply blift_cequiv_approx in Hbc; repnd.
  allrw @isprog_eq.
  allrw <- @isprog_vars_isprogrambt.
  apply approxbt_lsubst_prog with (lnt:=[x0,x]) in Hbc;  spcls; [| allsimpl; repdors; spcf].
  apply approxbt_lsubst_prog with (lnt:=[x0,x]) in Hbc0; spcls; [| allsimpl; repdors; spcf].
  unfold subst. allsimpl.
  split; spc.
Qed.

Lemma bcequivc3 {o} :
  forall lib v1 u1 w1 t1 v2 u2 w2 t2,
    @bcequivc o lib [v1,u1,w1] t1 [v2,u2,w2] t2
    -> forall v u w,
         cequivc lib (lsubstc3 v1 v u1 u w1 w t1) (lsubstc3 v2 v u2 u w2 w t2).
Proof.
  unfold bcequivc, cequivc, get_cvterm, substc.
  introv Hbc.
  intros v u w.
  destruct_cterms; allsimpl.
  unfold csubst; simpl.
  apply blift_cequiv_approx in Hbc; repnd.
  allrw @isprog_eq.
  allrw <- @isprog_vars_isprogrambt.
  apply approxbt_lsubst_prog with (lnt:=[x1,x0,x]) in Hbc;  spcls; [| allsimpl; repdors; spcf].
  apply approxbt_lsubst_prog with (lnt:=[x1,x0,x]) in Hbc0; spcls; [| allsimpl; repdors; spcf].
  unfold subst. allsimpl.
  split; spc.
Qed.

Lemma equal_fams_fams_cequivc {o} :
  forall lib (ts : cts(o)) eqp eqa P P' ap A ap' A' bp1 ba1 B1 bp2 ba2 B2 bp ba B eqb,
    bcequivc lib [bp1, ba1] B1 [bp2, ba2] B2
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp ba B eqb
    -> equal_fams_fams ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb.
Proof.
  introv bceq tspp tspa tspb.
  introv.

  generalize (equal_fams_fams_refl
                lib ts eqp eqa eqb P P' ap A ap' A'
                bp1 ba1 B1 bp ba B tspp tspa tspb);
    intro eqfamsrefl.

  generalize (tsp_fam_refl_right
                lib ts P P' eqp
                ap A ap' A' eqa
                p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep2 ea2].

  generalize (bcequivc2 lib bp1 ba1 B1 bp2 ba2 B2 bceq p2 a2); intro ceq.
  generalize (eqfamsrefl p1 p2 ep a1 a2 ea); intro e1.

  generalize (tspb p2 p2 ep2 a2 a2 ea2); intro tsp.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tyvr(lsubstc2 bp1 p2 ba1 a2 B1) (lsubstc2 bp2 p2 ba2 a2 B2));
    intro e2; repeat (autodimp e2 hyp).
  generalize (dum (lsubstc2 bp1 p2 ba1 a2 B1)
                  (lsubstc2 bp1 p1 ba1 a1 B1)
                  (lsubstc2 bp2 p2 ba2 a2 B2)
                  (eqb p1 p2 ep a1 a2 ea)
                  (eqb p2 p2 ep2 a2 a2 ea2)); sp.
Qed.

Lemma eq_term_equals_fam_refl {o} :
  forall lib (ts : cts(o)) eqp ap1 A1 ap2 A2 eqa,
    type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
   -> eq_term_equals_fam eqp eqa eqp eqa.
Proof.
  introv tspa.
  introv.
  generalize (tspa p p' ep); intro tsp1.
  generalize (tspa p p' ep1); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  apply uv2 with (T3 := substc p' ap2 A2); sp.
Qed.

Lemma eq_term_equals_fam_fam_refl {o} :
  forall lib (ts : cts(o)) (eqp : per) (eqa : per-fam(eqp)) bp1 ba1 B1 bp2 ba2 B2 eqb,
    type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
   -> eq_term_equals_fam_fam eqp eqa eqb eqp eqa eqb.
Proof.
  introv tspb.
  intros p p' ep ep' a a' ea ea'.
  generalize (tspb p p' ep a a' ea); intro tsp1.
  generalize (tspb p p' ep' a a' ea'); intro tsp2.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
  onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
  apply uv2 with (T3 := lsubstc2 bp2 p' ba2 a' B2); sp.
Qed.

Lemma equal_Cparams_refl {o} :
  forall lib (ts : cts(o)) eqp eqa eqb
         P1 P2 ap1 A1 ap2 A2 bp1 ba1 B1 bp2 ba2 B2
         cp1 ca1 cb1 C1 cp2 ca2 cb2 C2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp1 ca1 cb1 C1.
Proof.
  introv tspp tspa tspb eqcs.
  generalize (equal_Cparams_trans
                lib ts P1 P2 ap1 A1 ap2 A2 bp1 ba1 B1 bp2 ba2 B2
                eqp eqa eqb eqp eqa eqb
                cp1 ca1 cb1 C1
                cp2 ca2 cb2 C2
                cp1 ca1 cb1 C1); intro k.
  repeat (autodimp k hyp).
  apply eq_term_equals_fam_refl in tspa; sp.
  apply eq_term_equals_fam_fam_refl in tspb; sp.
  apply equal_Cparams_sym; sp.

  apply type_sys_props_implies_term_eq_sym in tspp; auto.
  apply type_sys_props_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) in tspa; sp.
  apply type_sys_props_fam_fam_implies_sym_trans_respeq with (P := P1) (P' := P2) (ap := ap1) (A := A1) (ap' := ap2) (A' := A2) in tspb; sp.
  apply type_sys_props_fam_implies_eq_fam_sym with (P := P1) (P' := P2) in tspa; sp.
  apply type_sys_props_fam_fam_implies_eq_fam_fam_sym with (P := P1) (P' := P2) (ap := ap1) (A := A1) (ap' := ap2) (A' := A2) in tspb; sp.
Qed.

Lemma equal_Cparams_cequivc {o} :
  forall lib (ts : cts(o)) eqp eqa eqb
         P P' ap A ap' A' bp ba B bp' ba' B'
         cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 cp ca cb C,
    bcequivc lib [cp1, ca1, cb1] C1 [cp2, ca2, cb2] C2
    -> type_sys_props lib ts P P' eqp
    -> type_sys_props_fam lib ts eqp ap A ap' A' eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp ba B bp' ba' B' eqb
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp ca cb C
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp2 ca2 cb2 C2.
Proof.
  introv bceq tspp tspa tspb eqcs.
  generalize (equal_Cparams_refl
                lib ts eqp eqa eqb
                P P' ap A ap' A' bp ba B bp' ba' B'
                cp1 ca1 cb1 C1 cp ca cb C);
    intro k; repeat (autodimp k hyp).
  intros p1 p2 ep a1 a2 ea b1 b2 eb.
  generalize (k p1 p2 ep a1 a2 ea b1 b2 eb); intro e1.

  generalize (tsp_fam_fam_refl_right
                lib ts P P' eqp
                ap A ap' A' eqa
                bp ba B bp' ba' B' eqb
                p1 p2 ep a1 a2 ea b1 b2 tspp tspa tspb eb); intro j.
  destruct j as [ep2 j].
  destruct j as [ea2 eb2].

  generalize (bcequivc3 lib cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 bceq p2 a2 b2); intro ceq.

  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tevr (lsubstc3 cp1 p2 ca1 a2 cb1 b2 C1)
                   (lsubstc3 cp2 p2 ca2 a2 cb2 b2 C2)); intro j.
  repeat (dest_imp j hyp).
  apply tet with (t2 := lsubstc3 cp1 p1 ca1 a1 cb1 b1 C1); sp.
  spcast; sp.
  apply tet with (t2 := lsubstc3 cp1 p2 ca1 a2 cb1 b2 C1); sp.
Qed.

Lemma type_pfamily_cequivc {o} :
  forall lib TC (ts : cts(o)) T1 T2 eqp eqa eqb
         P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
         P ap A bp ba B cp ca cb C p,
    computes_to_valc lib T1 (TC P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1)
    -> computes_to_valc lib T2 (TC P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2)
    -> cequivc lib P1 P2
    -> bcequivc lib [ap1] A1 [ap2] A2
    -> bcequivc lib [bp1, ba1] B1 [bp2, ba2] B2
    -> bcequivc lib [cp1, ca1, cb1] C1 [cp2, ca2, cb2] C2
    -> cequivc lib p1 p2
    -> type_sys_props lib ts P1 P eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap A eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp ba B eqb
    -> equal_Cparams eqp eqa eqb cp1 ca1 cb1 C1 cp ca cb C
    -> eqp p1 p
    -> type_pfamily
         lib TC ts T1 T2
         eqp eqa eqb
         cp1 ca1 cb1 C1
         cp2 ca2 cb2 C2
         p1 p2.
Proof.
  introv c1 c2cP cA cB cC cpp.
  intros tspp tspa tspb eqcs eqps.
  unfold type_pfamily.
  exists P1 P2.
  exists ap1 ap2 A1 A2.
  exists bp1 bp2 ba1 ba2 B1 B2; dands; try (complete (spcast; sp)).

  (* equality of the Ps *)
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tyvr P1 P2); sp.

  (* equality of the As *)
  rw @fold_equal_fams.
  apply (equal_fams_cequivc lib) with (P := P1) (P' := P) (ap := ap) (A := A); sp.

  (* equality of the Bs *)
  rw @fold_equal_fams_fams.
  apply (equal_fams_fams_cequivc lib) with (P := P1) (P' := P) (ap := ap1) (A := A1) (ap' := ap) (A' := A) (bp := bp) (ba := ba) (B := B); sp.

  (* equality of the Cs *)
  rw @fold_equal_Cparams.
  generalize (equal_Cparams_cequivc
                lib ts eqp eqa eqb
                P1 P ap1 A1 ap A bp1 ba1 B1 bp ba B
                cp1 ca1 cb1 C1 cp2 ca2 cb2 C2 cp ca cb C); sp.

  (* equality of the ps *)
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  generalize (tevr p1 p2); intro k.
  repeat (dest_imp k hyp).
  apply tet with (t2 := p); sp.
  spcast; sp.
Qed.

Ltac dtsprops T :=
  let tmp := fresh "tmp" in
  let Tuv := fresh T "uv"   in
  let Ttys := fresh T "tys"   in
  let Ttyt := fresh T "tyt"   in
  let Ttyst := fresh T "tyst"  in
  let Ttyvr := fresh T "tyvr"  in
  let Ttes := fresh T "tes"   in
  let Ttet := fresh T "tet"   in
  let Ttevr := fresh T "tevr"  in
  let Ttygs := fresh T "tygs"  in
  let Ttygt := fresh T "tygt"  in
  let Ttymt := fresh T "tymt"  in
    unfold type_sys_props in T;
  destruct T   as [ Tuv   tmp ];
  destruct tmp as [ Ttys  tmp ];
  destruct tmp as [ Ttyt  tmp ];
  destruct tmp as [ Ttyst tmp ];
  destruct tmp as [ Ttyvr tmp ];
  destruct tmp as [ Ttes  tmp ];
  destruct tmp as [ Ttet  tmp ];
  destruct tmp as [ Ttevr tmp ];
  destruct tmp as [ Ttygs tmp ];
  destruct tmp as [ Ttygt Ttymt ].

Lemma tsp_refl_left {o} :
  forall lib (ts : cts(o)) P1 P2 eqp p1 p2,
    type_sys_props lib ts P1 P2 eqp
    -> eqp p1 p2
    -> eqp p1 p1.
Proof.
  introv tsp e.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := p2); sp.
Qed.

Lemma tsp_fam_refl_left {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> eqa p1 p2 ep a1 a2
    -> {ep' : eqp p1 p1 , eqa p1 p1 ep' a1 a1}.
Proof.
  introv tspp tspa e.
  generalize (tsp_refl_left lib ts P1 P2 eqp p1 p2 tspp ep); intro ep'.
  exists ep'.
  generalize (tsp_implies_eq_fam_refl_left lib ts eqp ap1 A1 ap2 A2 eqa tspa); intro rl.
  generalize (rl p1 p2 ep ep'); intro eq; apply eq; clear eq.
  generalize (tspa p1 p2 ep); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := a2); sp.
Qed.

Lemma tsp_fam_fam_refl_left {o} :
  forall lib (ts : cts(o)) P1 P2 eqp ap1 A1 ap2 A2 eqa bp1 ba1 B1 bp2 ba2 B2 eqb p1 p2 ep a1 a2 ea b1 b2,
    type_sys_props lib ts P1 P2 eqp
    -> type_sys_props_fam lib ts eqp ap1 A1 ap2 A2 eqa
    -> type_sys_props_fam_fam lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb
    -> eqb p1 p2 ep a1 a2 ea b1 b2
    -> {ep' : eqp p1 p1 , {ea' : eqa p1 p1 ep' a1 a1 , eqb p1 p1 ep' a1 a1 ea' b1 b1}}.
Proof.
  introv tspp tspa tspb e.
  generalize (tsp_fam_refl_left lib ts P1 P2 eqp ap1 A1 ap2 A2 eqa p1 p2 ep a1 a2 tspp tspa ea); intro k.
  destruct k as [ep' ea'].
  exists ep' ea'.
  generalize (tsp_implies_eq_fam_fam_refl_left
                lib ts eqp eqa bp1 ba1 B1 bp2 ba2 B2 eqb tspb);
    intro rl.
  generalize (rl p1 p2 ep ep' a1 a2 ea ea'); intro eq; apply eq; clear eq.
  generalize (tspb p1 p2 ep a1 a2 ea); intro tsp.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum; sp.
  apply tet with (t2 := b2); sp.
Qed.
