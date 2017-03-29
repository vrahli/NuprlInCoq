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


Require Export rules_useful.
Require Export per_props_w.


Ltac rename_pfamily h :=
  match goal with
    | [ H : type_pfamily _  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
        rename H into h
  end.

Lemma tequality_mkc_pw {o} :
  forall lib
         P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    @tequality o lib
      (mkc_pw P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1)
      (mkc_pw P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2)
    <=>
    (tequality lib P1 P2
     # (forall p1 p2,
        equality lib p1 p2 P1
        -> tequality lib (substc p1 ap1 A1) (substc p2 ap2 A2))
     # (forall p1 p2,
          equality lib p1 p2 P1
          -> forall a1 a2,
               equality lib a1 a2 (substc p1 ap1 A1)
               -> tequality lib (lsubstc2 bp1 p1 ba1 a1 B1)
                            (lsubstc2 bp2 p2 ba2 a2 B2))
     # (forall p1 p2,
          equality lib p1 p2 P1
          -> forall a1 a2,
               equality lib a1 a2 (substc p1 ap1 A1)
               -> forall b1 b2,
                    equality lib b1 b2 (lsubstc2 bp1 p1 ba1 a1 B1)
                    -> equality lib (lsubstc3 cp1 p1 ca1 a1 cb1 b1 C1)
                                (lsubstc3 cp2 p2 ca2 a2 cb2 b2 C2)
                                P1)
     # equality lib p1 p2 P1).
Proof.
  introv; split; intro e; repnd.

  - unfold tequality in e; exrepnd.
    unfold nuprl in e0.
    inversion e0; try not_univ.
    allunfold @per_pw; exrepnd.
    rename_pfamily h; allunfold @type_pfamily; exrepnd; spcast; allfold @nuprl.
    computes_to_value_isvalue.
    dands.

    + allapply @tequality_if_nuprl; sp.

    + introv eqinp.
      generalize (equality_eq1 lib P0 P3 p1 p2 eqp); intro i; dest_imp i hyp.
      rw <- i in eqinp.
      generalize (h4 p1 p2 eqinp); intro n.
      allapply @tequality_if_nuprl; sp.

    + introv eqinp eqina.
      generalize (equality_eq1 lib P0 P3 p1 p2 eqp); intro i; dest_imp i hyp.
      rw <- i in eqinp.
      generalize (h4 p1 p2 eqinp); intro na.
      generalize (equality_eq1 lib (substc p1 ap0 A0)
                               (substc p2 ap3 A3)
                               a1 a2
                               (eqa p1 p2 eqinp));
        intro j; dest_imp j hyp.
      rw <- j in eqina.
      generalize (h5 p1 p2 eqinp a1 a2 eqina); intro nb.
      allapply @tequality_if_nuprl; sp.

    + introv eqinp eqina eqinb.
      generalize (equality_eq1 lib P0 P3 p1 p2 eqp); intro i; dest_imp i hyp.
      rw <- i in eqinp.
      generalize (h4 p1 p2 eqinp); intro na.
      generalize (equality_eq1 lib (substc p1 ap0 A0)
                               (substc p2 ap3 A3)
                               a1 a2
                               (eqa p1 p2 eqinp));
        intro j; dest_imp j hyp.
      rw <- j in eqina.
      generalize (h5 p1 p2 eqinp a1 a2 eqina); intro nb.
      generalize (equality_eq1 lib (lsubstc2 bp0 p1 ba0 a1 B0)
                               (lsubstc2 bp3 p2 ba3 a2 B3)
                               b1 b2
                               (eqb p1 p2 eqinp a1 a2 eqina));
        intro k; dest_imp k hyp.
      rw <- k in eqinb.
      generalize (h6 p1 p2 eqinp a1 a2 eqina b1 b2); intro nc; dest_imp nc hyp.
      generalize (equality_eq1 lib P0 P3
                               (lsubstc3 cp0 p1 ca0 a1 cb0 b1 C0)
                               (lsubstc3 cp3 p2 ca3 a2 cb3 b2 C3)
                               eqp);
        intro l; dest_imp l hyp.
      rw l in nc; sp.

    + generalize (equality_eq1 lib P0 P3 p0 p3 eqp); intro i; dest_imp i hyp.
      rw i in h1; sp.

  - unfold tequality.
    unfold tequality in e0; exrepnd.
    rename eq into eqp.

    generalize (choice_teq1 lib P1 eqp ap1 A1 ap2 A2); intro neqa.
    dest_imp neqa hyp; try (complete (allapply @nuprl_refl; sp)).
    dest_imp neqa hyp; exrepnd.
    rename f into eqa.

    generalize (choice_teq2 lib eqp eqa P1 ap1 A1 bp1 ba1 B1 bp2 ba2 B2); intro neqb.
    dest_imp neqb hyp; try (complete (allapply @nuprl_refl; sp)).
    dest_imp neqb hyp.
    introv.
    assert (eqp p3 p3)
           as eqp0
           by (apply (equality_eq_refl lib) with (A := P1) (B := P2) (b := p0); sp;
               apply (equality_eq_sym lib) with (A := P1) (B := P2); sp).
    generalize (neqa0 p0 p3 ep); intro k1.
    generalize (neqa0 p3 p3 eqp0); intro k2.
    apply nuprl_trans with (t2 := substc p3 ap2 A2) (eq2 := eqa p3 p3 eqp0); sp.
    apply nuprl_sym; sp.
    dest_imp neqb hyp; exrepnd.
    rename f into eqb.

    exists (pweq lib eqp eqa eqb
                 cp1 ca1 cb1 C1
                 p1).
    apply CL_pw; unfold per_pw.
    exists eqp eqa eqb p1 p2.
    exists cp1 cp2 ca1 ca2 cb1 cb2 C1 C2; sp.
    unfold type_pfamily.
    exists P1 P2 ap1 ap2 A1 A2.
    exists bp1 bp2 ba1 ba2 B1 B2; dands;
    try (complete sp);
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_pw))).

    introv eqinb.
    generalize (equality_eq1 lib P1 P2 p0 p3 eqp); intro i; dest_imp i hyp.
    duplicate ep as ep'.
    apply i in ep; clear i.
    generalize (equality_eq1 lib (substc p0 ap1 A1) (substc p3 ap2 A2) a1 a2 (eqa p0 p3 ep'));
      intro i; dest_imp i hyp.
    duplicate ea as ea'.
    apply i in ea; clear i.
    generalize (equality_eq1 lib (lsubstc2 bp1 p0 ba1 a1 B1)
                             (lsubstc2 bp2 p3 ba2 a2 B2)
                             b1 b2
                             (eqb p0 p3 ep' a1 a2 ea'));
      intro i; dest_imp i hyp.
    duplicate eqinb as eb'.
    apply i in eqinb; clear i.
    generalize (e3 p0 p3 ep a1 a2 ea b1 b2 eqinb); intro k.
    generalize (equality_eq1 lib P1 P2
                             (lsubstc3 cp1 p0 ca1 a1 cb1 b1 C1)
                             (lsubstc3 cp2 p3 ca2 a2 cb2 b2 C2)
                             eqp); intro i; dest_imp i hyp.
    apply i; sp.

    generalize (equality_eq1 lib P1 P2 p1 p2 eqp); intro i; dest_imp i hyp.
    apply i; sp.
Qed.

Lemma pweq_fun {o} :
  forall lib
         f1 f2
         (eqp : per) (eqa : per-fam(eqp)) (eqb : per-fam-fam(eqp,eqa))
         P ap A bp ba B cp ca cb C
         p (ep : eqp p p) a1 a2 (ea : eqa p p ep a1 a2)
         vb,
    !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
    (* P as equality eqp *)
    -> @nuprl o lib P P eqp
    (* A as equality eqa *)
    -> (forall p p' (ep : eqp p p'),
          nuprl lib (substc p ap A)
                (substc p' ap A)
                (eqa p p' ep))
    (* B as equality eqb *)
    -> (forall p p' (ep : eqp p p') a a' (ea : eqa p p' ep a a'),
          nuprl lib (lsubstc2 bp p ba a B)
                (lsubstc2 bp p' ba a' B)
                (eqb p p' ep a a' ea))
    (* C function into P *)
    -> (forall p p' (ep : eqp p p') a a' (ea : eqa p p' ep a a') b b',
          eqb p p' ep a a' ea b b'
          -> eqp (lsubstc3 cp p ca a cb b C)
                 (lsubstc3 cp p' ca a' cb b' C))
    (* hypothesis *)
    -> (forall b1 b2,
          eqb p p ep a1 a2 ea b1 b2
          -> pweq lib eqp eqa eqb
                  cp ca cb C
                  (lsubstc3 cp p ca a1 cb b1 C)
                  (mkc_apply f1 b1)
                  (mkc_apply f2 b2))
    (* conclusion *)
    -> equality lib f1 f2
                (mkc_function
                   (lsubstc2 bp p ba a1 B)
                   vb
                   (mkc_pw_vs [vb]
                              P ap A bp ba B cp ca cb C
                              (lsubstc3v3 cp p ca a1 cb vb C))).
Proof.
  introv nivb np fna fnb fnc F.
  rw @equality_in_function; dands.

  generalize (fnb p p ep a1 a2 ea); intro nb.
  exists (eqb p p ep a1 a2 ea).
  allapply @nuprl_refl; sp.

  intros b b' eqinb.
  repeat (rw @substc_mkc_pw_vs; simpl; try (complete sp)).
  apply @tequality_mkc_pw; dands; try (complete sp).

  exists eqp; sp.

  introv eqinp.
  generalize (equality_eq1 lib P P p1 p2 eqp); intro i; dest_imp i hyp.
  applydup i in eqinp as eqinp'.
  generalize (fna p1 p2 eqinp'); intro n.
  exists (eqa p1 p2 eqinp'); sp.

  introv eqinp eqina.
  generalize (equality_eq1 lib P P p1 p2 eqp); intro i; dest_imp i hyp.
  applydup i in eqinp as eqinp'.
  generalize (equality_eq1 lib (substc p1 ap A) (substc p2 ap A)
                           a0 a3
                           (eqa p1 p2 eqinp')); intro j; dest_imp j hyp.
  applydup j in eqina as eqina'.
  generalize (fnb p1 p2 eqinp' a0 a3 eqina'); intro n.
  exists (eqb p1 p2 eqinp' a0 a3 eqina'); sp.

  introv eqip eqia eqib.
  generalize (equality_eq1 lib P P p1 p2 eqp); intro i; dest_imp i hyp.
  applydup i in eqip as eqip'; clear i.
  generalize (equality_eq1 lib (substc p1 ap A) (substc p2 ap A)
                           a0 a3
                           (eqa p1 p2 eqip')); intro j; dest_imp j hyp.
  applydup j in eqia as eqia'; clear j.
  generalize (equality_eq1 lib (lsubstc2 bp p1 ba a0 B) (lsubstc2 bp p2 ba a3 B)
                           b1 b2
                           (eqb p1 p2 eqip' a0 a3 eqia')); intro k; dest_imp k hyp.
  applydup k in eqib as eqib'; clear k.
  generalize (fnc p1 p2 eqip' a0 a3 eqia' b1 b2 eqib'); intro n.
  exists eqp; sp.

  assert (eqa p p ep a1 a1) as ea'.
  generalize (fna p p ep); intro na.
  apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a2); sp.

  generalize (equality_eq1 lib (lsubstc2 bp p ba a1 B) (lsubstc2 bp p ba a1 B)
                           b b'
                           (eqb p p ep a1 a1 ea')); intro k; dest_imp k hyp.
  applydup k in eqinb as eqinb'; clear k.
  generalize (fnc p p ep a1 a1 ea' b b' eqinb'); intro n.
  exists eqp; sp.

  intros b b' eqinb.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply @equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1) as ea'.
  generalize (fna p p ep); intro na.
  apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a2); sp.

  generalize (equality_eq1 lib (lsubstc2 bp p ba a1 B) (lsubstc2 bp p ba a1 B)
                           b b
                           (eqb p p ep a1 a1 ea')); intro k; dest_imp k hyp.
  apply @equality_refl in eqinb.
  applydup k in eqinb as eqinb'; clear k.
  generalize (fnc p p ep a1 a1 ea' b b eqinb'); sp.

  apply F.

  generalize (equality_eq1 lib (lsubstc2 bp p ba a1 B) (lsubstc2 bp p ba a2 B)
                           b b'
                           (eqb p p ep a1 a2 ea)); intro k; dest_imp k hyp.
  apply k; sp.
Qed.

Lemma tequality_mkc_pw_implies {o} :
  forall lib
         P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
         p3 p4,
    @tequality o lib
      (mkc_pw P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1)
      (mkc_pw P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2)
    -> equality lib p3 p4 P1
    -> tequality lib
         (mkc_pw P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p3)
         (mkc_pw P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p4).
Proof.
  introv teq eq.
  apply @tequality_mkc_pw in teq; repnd.
  apply @tequality_mkc_pw; sp.
Qed.


Lemma simple_csubst_pw {o} :
  forall P ap A bp ba B cp ca cb C p sub,
    disjoint (@dom_csub o sub) (free_vars P)
    -> disjoint (remove_nvars [ap] (dom_csub sub)) (free_vars A)
    -> disjoint (remove_nvars [bp,ba] (dom_csub sub)) (free_vars B)
    -> disjoint (remove_nvars [cp,ca,cb] (dom_csub sub)) (free_vars C)
    -> csubst (mk_pw P ap A bp ba B cp ca cb C p) sub
       = mk_pw P ap A bp ba B cp ca cb C (csubst p sub).
Proof.
  introv disj1 disj2 disj3 disj4.
  unfold csubst.
  change_to_lsubst_aux4.
  simpl.

  rw @lsubst_aux_sub_filter3;
    try (complete (rw remove_nvars_nil_l; sp)).
  rw @lsubst_aux_sub_filter3; sp.
  rw @lsubst_aux_sub_filter3; sp.
  rw @lsubst_aux_sub_filter3; sp.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma csubst_lsubst_pw_C_vars {o} :
  forall C cp ca cb q a b t,
    !LIn q (@bound_vars o C)
    -> !LIn a (bound_vars C)
    -> !LIn b (bound_vars C)
    -> !(b = q)
    -> !(b = a)
    -> (!LIn b [cp,ca,cb] -> !LIn b (free_vars C))
    -> csubst (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
              [(b, t)]
       = (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm t)]).
Proof.
  introv bc1 bc2 bc3 bc4 bc5 bc6.
  unfold csubst; simpl.

  rw @simple_lsubst_lsubst; simpl;
  try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; sp)).

  assert (lsubst (mk_var q) [(b, get_cterm t)] = mk_var q)
    as eq1 by (unfold lsubst; simpl; boolvar; sp).
  assert (lsubst (mk_var a) [(b, get_cterm t)] = mk_var a)
    as eq2 by (unfold lsubst; simpl; boolvar; sp).
  assert (lsubst (mk_var b) [(b, get_cterm t)] = get_cterm t)
    as eq3 by (unfold lsubst; simpl; boolvar; sp).
  rw eq1; rw eq2; rw eq3; clear eq1 eq2 eq3.

  assert ([(cp, mk_var q), (ca, mk_var a), (cb, get_cterm t), (b, get_cterm t)]
          = [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm t)] ++ [(b, get_cterm t)])
    as eq by (simpl; sp); rw eq; clear eq.

  apply simple_lsubst_app2; simpl.

  introv i; sp; cpx; simpl; try (rw disjoint_singleton_l); sp.
  rw @free_vars_cterm; sp.

  introv i; sp; cpx.

  introv i; sp; cpx; subst.
  allrw not_over_or; sp.
Qed.

Lemma cover_vars_upto_pw {o} :
  forall P ap A bp ba B cp ca cb C p sub vs,
    cover_vars_upto (@mk_pw o P ap A bp ba B cp ca cb C p) sub vs
    <=> cover_vars_upto P sub vs
        # cover_vars_upto A (csub_filter sub [ap]) (ap :: vs)
        # cover_vars_upto B (csub_filter sub [bp,ba]) (bp :: ba :: vs)
        # cover_vars_upto C (csub_filter sub [cp,ca,cb]) (cp :: ca :: cb :: vs)
        # cover_vars_upto p sub vs.
Proof.
  introv; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.

  allrw subvars_prop; simpl; split; sp; discover; splst; sp;
  allrw in_app_iff; allrw in_remove_nvars; allsimpl; sp;
  try (complete (destruct (eq_var_dec ap x); sp;
                 try (complete (right; right; sp))));
  try (complete (destruct (eq_var_dec bp x); destruct (eq_var_dec ba x); sp;
                 try (complete (right; right; right; sp))));
  try (complete (destruct (eq_var_dec cp x); destruct (eq_var_dec ca x); destruct (eq_var_dec cb x); sp;
                 try (complete (right; right; right; right; sp)))).
Qed.
