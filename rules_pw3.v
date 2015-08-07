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


Require Import rules_pw_useful.
Require Import pweq_lemmas.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


(* Same as rules_pw.v but where I'm planning on not using the second sequent
 * by strenghtening the induction hypothesis of param_w_ind3
 * *)




Ltac rename_per h :=
  match goal with
    | [ H : per_pw _ _ _ _ _ |- _ ] => rename H into h
  end.

Lemma all_and_split :
  forall T F G H,
    (forall t1 t2 : T, F t1 t2 -> G t1 t2 # H t1 t2)
    -> (forall t1 t2 : T, F t1 t2 -> G t1 t2)
         # (forall t1 t2 : T, F t1 t2 -> H t1 t2).
Proof.
  introv h; dands; introv j; discover; sp.
Qed.

Lemma all_and_split2 :
  forall T U F G H J,
    (forall t1 t2 : T, F t1 t2 -> forall u1 u2 : U, G t1 t2 u1 u2 -> H t1 t2 u1 u2 # J t1 t2 u1 u2)
    -> (forall t1 t2 : T, F t1 t2 -> forall u1 u2 : U, G t1 t2 u1 u2 -> H t1 t2 u1 u2)
         # (forall t1 t2 : T, F t1 t2 -> forall u1 u2 : U, G t1 t2 u1 u2 -> J t1 t2 u1 u2).
Proof.
  introv h; dands; introv j; sp; generalize (h t1 t2 j u1 u2); sp.
Qed.

Lemma equality_in_pw_v1 {o} :
  forall lib t1 t2 P ap A bp ba B cp ca cb C p,
    @equality o lib t1 t2 (mkc_pw P ap A bp ba B cp ca cb C p)
    <=> {a1, a2, f1, f2 : CTerm
         , {vb : NVar
         , t1 ===>(lib) (mkc_sup a1 f1)
         # t2 ===>(lib) (mkc_sup a2 f2)
         # member lib p P
         # equality lib a1 a2 (substc p ap A)
         # !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
         # equality lib f1 f2 (mkc_function (lsubstc2 bp p ba a1 B)
                                        vb
                                        (mkc_pw_vs
                                           [vb]
                                           P ap A bp ba B cp ca cb C
                                           (lsubstc3v3 cp p ca a1 cb vb C)))
         # (forall p p',
              equality lib p p' P
              -> tequality lib (substc p ap A) (substc p' ap A)
                 # forall a a',
                     equality lib a a' (substc p ap A)
                     -> tequality lib (lsubstc2 bp p ba a B) (lsubstc2 bp p' ba a' B)
                        # forall b b',
                            equality lib b b' (lsubstc2 bp p ba a B)
                            -> equality lib (lsubstc3 cp p ca a cb b C) (lsubstc3 cp p' ca a' cb b' C) P)
           }}.
Proof.
  introv; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; try not_univ.
    rename_per h.
    allunfold @per_pw; exrepnd.
    allunfold @type_pfamily; exrepnd.
    allfold (@nuprl o lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    destruct h as [ ep a1 f1 a2 f2 ea c1 c2 I ].
    exists a1 a2 f1 f2.

    assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp1, ca1, cb1] C1))})
           as ev
           by (exists (fresh_var (bound_vars (get_cvterm [cp1, ca1, cb1] C1)));
               apply fresh_var_not_in);
      exrepnd.

    exists v; dands; try (complete sp).

    exists eqp; sp.

    exists (eqa p1 p1 ep); sp.

    apply @pweq_fun with (eqp := eqp) (eqa := eqa) (eqb := eqb) (ep := ep) (a2 := a2) (ea := ea);
      try (complete sp).

    introv eip.
    generalize (equality_eq lib P1 p p' eqp h4); intro e.
    applydup e in eip as k.
    dands.

    generalize (h5 p p' k); intro n.
    exists (eqa p p' k); apply nuprl_refl in n; sp.

    introv eia.
    generalize (equality_eq1 lib (substc p ap1 A1) (substc p' ap1 A1) a a' (eqa p p' k)
                             (h5 p p' k)); intro e'.
    applydup e' in eia as k'.
    dands.

    generalize (h6 p p' k a a' k'); intro n.
    exists (eqb p p' k a a' k'); sp.

    introv eib.

    generalize (equality_eq1 lib
                  (lsubstc2 bp1 p ba1 a B1)
                  (lsubstc2 bp1 p' ba1 a' B1)
                  b b'
                  (eqb p p' k a a' k')
                  (h6 p p' k a a' k')); intro e''.
    applydup e'' in eib as k''.
    generalize (h7 p p' k a a' k' b b' k''); intro j.
    exists eqp; sp.

  - exrepnd.
    apply all_and_split in e0; repnd.
    apply all_and_split2 in e0; repnd.

    unfold member, equality in e3; exrepnd.
    rename eq into eqp.

    generalize (choice_teq1 lib P eqp ap A ap A e3 e7); intro k1; exrepnd.
    rename f into eqa.

    generalize (choice_teq2 lib eqp eqa P ap A bp ba B bp ba B e3 k0 e8); intro j; exrepnd.
    rename f into eqb.

    apply equality_in_pw.

    exists eqp eqa eqb; dands; try (complete sp).
    introv eb.

    generalize (eq_equality1 lib p0 p' P eqp ep e3); intro ep'.
    generalize (eq_equality2 lib a a' (substc p0 ap A) (substc p' ap A) (eqa p0 p' ep) ea (k0 p0 p' ep)); intro ea'.
    generalize (eq_equality2 lib b b'
                             (lsubstc2 bp p0 ba a B)
                             (lsubstc2 bp p' ba a' B)
                             (eqb p0 p' ep a a' ea)
                             eb
                             (j0 p0 p' ep a a' ea)); intro eb'.

    generalize (e0 p0 p' ep' a a' ea' b b' eb'); intro eq.
    generalize (equality_eq1 lib P P
                             (lsubstc3 cp p0 ca a cb b C)
                             (lsubstc3 cp p' ca a' cb b' C)
                             eqp e3); intro e.
    apply e; sp.

    generalize (equality_eq1 lib (substc p ap A) (substc p ap A) a1 a2 (eqa p p e9) (k0 p p e9)); intro e.
    applydup e in e4 as ea.

    apply @pweq_cons with (ep := e9) (a1 := a1) (f1 := f1) (a2 := a2) (f2 := f2) (ea := ea); try (complete sp).
    introv eb.
    rw @equality_in_function in e6; repnd.

    generalize (equality_eq1 lib (lsubstc2 bp p ba a1 B)
                             (lsubstc2 bp p ba a1 B)
                             b1 b2
                             (eqb p p e9 a1 a2 ea)); intro k.

    generalize (j0 p p e9 a1 a2 ea); intro n.
    apply nuprl_refl in n.
    autodimp k hyp.

    applydup k in eb as eib.
    generalize (e6 b1 b2 eib); intro eq.

    rw @substc_mkc_pw_vs in eq; try (complete sp).

    apply equality_in_pw in eq; exrepnd.
    apply @pweq_implies with (eqp1 := eqp0) (eqa1 := eqa0) (eqb1 := eqb0); auto.

    generalize (nuprl_uniquely_valued lib P eqp0 eqp); sp.

    introv.
    generalize (k0 p0 p' ep1); intro n1.
    generalize (eq2 p0 p' ep); intro n2.
    apply nuprl_refl in n1; apply nuprl_refl in n2.
    generalize (nuprl_uniquely_valued lib (substc p0 ap A) (eqa0 p0 p' ep) (eqa p0 p' ep1)); sp.

    intros p1 p2 ep0 ep.
    intros a a' ea0 ea'.
    generalize (j0 p1 p2 ep a a' ea'); intro n1; apply nuprl_refl in n1.
    generalize (eq3 p1 p2 ep0 a a' ea0); intro n2; apply nuprl_refl in n2.
    generalize (nuprl_uniquely_valued lib (lsubstc2 bp p1 ba a B) (eqb0 p1 p2 ep0 a a' ea0) (eqb p1 p2 ep a a' ea')); sp.
Qed.

Lemma equality_in_pw_v2 {o} :
  forall lib vb t1 t2 P ap A bp ba B cp ca cb C p,
    !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
    -> (equality lib t1 t2 (mkc_pw P ap A bp ba B cp ca cb C p)
        <=> {a1, a2, f1, f2 : @CTerm o
             , t1 ===>(lib) (mkc_sup a1 f1)
             # t2 ===>(lib) (mkc_sup a2 f2)
             # member lib p P
             # equality lib a1 a2 (substc p ap A)
             # equality lib f1 f2 (mkc_function (lsubstc2 bp p ba a1 B)
                                             vb
                                            (mkc_pw_vs
                                               [vb]
                                               P ap A bp ba B cp ca cb C
                                               (lsubstc3v3 cp p ca a1 cb vb C)))
             # (forall p p',
                  equality lib p p' P
                  -> tequality lib (substc p ap A) (substc p' ap A)
                     # forall a a',
                         equality lib a a' (substc p ap A)
                         -> tequality lib (lsubstc2 bp p ba a B) (lsubstc2 bp p' ba a' B)
                            # forall b b',
                                equality lib b b' (lsubstc2 bp p ba a B)
                                -> equality lib (lsubstc3 cp p ca a cb b C) (lsubstc3 cp p' ca a' cb b' C) P)
            }).
Proof.
  introv nvb; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; try not_univ.
    rename_per h.
    allunfold @per_pw; exrepnd.
    allunfold @type_pfamily; exrepnd.
    allfold (@nuprl o lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    destruct h as [ ep a1 f1 a2 f2 ea c1 c2 I ].
    exists a1 a2 f1 f2.
    dands; try (complete sp).

    exists eqp; sp.

    exists (eqa p1 p1 ep); sp.

    apply @pweq_fun with (eqp := eqp) (eqa := eqa) (eqb := eqb) (ep := ep) (a2 := a2) (ea := ea);
      try (complete sp).

    introv eip.
    generalize (equality_eq lib P1 p p' eqp h4); intro e.
    applydup e in eip as k.
    dands.

    generalize (h5 p p' k); intro n.
    exists (eqa p p' k); apply nuprl_refl in n; sp.

    introv eia.
    generalize (equality_eq1 lib (substc p ap1 A1) (substc p' ap1 A1) a a' (eqa p p' k)
                             (h5 p p' k)); intro e'.
    applydup e' in eia as k'.
    dands.

    generalize (h6 p p' k a a' k'); intro n.
    exists (eqb p p' k a a' k'); sp.

    introv eib.

    generalize (equality_eq1
                  lib (lsubstc2 bp1 p ba1 a B1)
                  (lsubstc2 bp1 p' ba1 a' B1)
                  b b'
                  (eqb p p' k a a' k')
                  (h6 p p' k a a' k')); intro e''.
    applydup e'' in eib as k''.
    generalize (h7 p p' k a a' k' b b' k''); intro j.
    exists eqp; sp.

  - exrepnd.
    apply all_and_split in e1; repnd.
    apply all_and_split2 in e1; repnd.

    unfold member, equality in e3; exrepnd.
    rename eq into eqp.

    generalize (choice_teq1 lib P eqp ap A ap A e3 e6); intro k1; exrepnd.
    rename f into eqa.

    generalize (choice_teq2 lib eqp eqa P ap A bp ba B bp ba B e3 k0 e7); intro j; exrepnd.
    rename f into eqb.

    apply equality_in_pw.

    exists eqp eqa eqb; dands; try (complete sp).
    introv eb.

    generalize (eq_equality1 lib p0 p' P eqp ep e3); intro ep'.
    generalize (eq_equality2 lib a a' (substc p0 ap A) (substc p' ap A) (eqa p0 p' ep) ea (k0 p0 p' ep)); intro ea'.
    generalize (eq_equality2 lib b b'
                             (lsubstc2 bp p0 ba a B)
                             (lsubstc2 bp p' ba a' B)
                             (eqb p0 p' ep a a' ea)
                             eb
                             (j0 p0 p' ep a a' ea)); intro eb'.

    generalize (e1 p0 p' ep' a a' ea' b b' eb'); intro eq.
    generalize (equality_eq1 lib P P
                             (lsubstc3 cp p0 ca a cb b C)
                             (lsubstc3 cp p' ca a' cb b' C)
                             eqp e3); intro e.
    apply e; sp.

    generalize (equality_eq1 lib (substc p ap A) (substc p ap A) a1 a2 (eqa p p e8) (k0 p p e8)); intro e.
    applydup e in e4 as ea.

    apply @pweq_cons with (ep := e8) (a1 := a1) (f1 := f1) (a2 := a2) (f2 := f2) (ea := ea); try (complete sp).
    introv eb.
    rw @equality_in_function in e5; repnd.

    generalize (equality_eq1 lib (lsubstc2 bp p ba a1 B)
                             (lsubstc2 bp p ba a1 B)
                             b1 b2
                             (eqb p p e8 a1 a2 ea)); intro k.

    generalize (j0 p p e8 a1 a2 ea); intro n.
    apply nuprl_refl in n.
    autodimp k hyp.

    applydup k in eb as eib.
    generalize (e5 b1 b2 eib); intro eq.

    rw @substc_mkc_pw_vs in eq; try (complete sp).

    apply equality_in_pw in eq; exrepnd.
    apply @pweq_implies with (eqp1 := eqp0) (eqa1 := eqa0) (eqb1 := eqb0); auto.

    generalize (nuprl_uniquely_valued lib P eqp0 eqp); sp.

    introv.
    generalize (k0 p0 p' ep1); intro n1.
    generalize (eq2 p0 p' ep); intro n2.
    apply nuprl_refl in n1; apply nuprl_refl in n2.
    generalize (nuprl_uniquely_valued lib (substc p0 ap A) (eqa0 p0 p' ep) (eqa p0 p' ep1)); sp.

    intros p1 p2 ep0 ep.
    intros a a' ea0 ea'.
    generalize (j0 p1 p2 ep a a' ea'); intro n1; apply nuprl_refl in n1.
    generalize (eq3 p1 p2 ep0 a a' ea0); intro n2; apply nuprl_refl in n2.
    generalize (nuprl_uniquely_valued lib (lsubstc2 bp p1 ba a B) (eqb0 p1 p2 ep0 a a' ea0) (eqb p1 p2 ep a a' ea')); sp.
Qed.

(* end hide *)

(**

  Let us now prove the truth of rules about the parametrized W type.

*)


(* [19] ============ pW INDUCTION ============ *)

(**

  The parametrized W induction rule can be stated as follows:
<<
   H, w : pW(P;ap.A;bp,ba.B;cp,ca,cb.C;p) |- Q(p)

     By pWinduction a f v

     H, q : P
        a : A(q)
        f : b:B(q,a) -> pW(P;ap.A;bp,ba.B;cp,ca,cb.C;C(q,a,b))
        v : b:B(q,a) -> Q[w\f(b)](C(q,a,b))
      |- Q[w\sup(a,f)](q)
>>
 *)

Definition rule_pw_induction {o}
             (H : @barehypotheses o)
             (Q P A B C p : NTerm)
             (i : nat)
             (ap bp ba cp ca cb w b a f v q : NVar) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp w (mk_pw P ap A bp ba B cp ca cb C p)))
                   (mk_conclax (mk_apply Q p)))
    [ mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp q P))
                          (mk_hyp a (lsubst A [(ap,mk_var q)])))
                    (mk_hyp f (mk_function
                                 (lsubst B [(bp,mk_var q),(ba,mk_var a)])
                                 b
                                 (mk_pw P ap A bp ba B cp ca cb C
                                        (lsubst C [(cp,mk_var q),(ca,mk_var a),(cb,mk_var b)])))))
              (mk_hyp v (mk_function
                           (lsubst B [(bp,mk_var q),(ba,mk_var a)])
                           b
                           (mk_apply
                              (lsubst Q [(w,mk_apply (mk_var f) (mk_var b))])
                              (lsubst C [(cp,mk_var q),(ca,mk_var a),(cb,mk_var b)])))))
        (mk_conclax (mk_apply (lsubst Q [(w,mk_sup (mk_var a) (mk_var f))]) (mk_var q)))
    ]
    [sarg_var a, sarg_var f, sarg_var v].

Lemma rule_pw_induction_true {o} :
  forall (lib : library)
         (H : @barehypotheses o)
         (Q P A B C p : NTerm)
         (i : nat)
         (ap bp ba cp ca cb w b a f v q : NVar)
         (bc1 : disjoint (free_vars p) (bound_vars A))
         (bc2 : disjoint (free_vars p) (bound_vars B))
         (bc3 : !LIn a (bound_vars B))
         (bv4 : !(ba = bp))
         (bc5 : !LIn q (bound_vars A))
         (bc6 : !LIn q (bound_vars B))
         (bc7 : !LIn b (w :: q :: a :: f :: v :: vars_hyps H))
         (bc8 : !LIn q (bound_vars C))
         (bc9 : !LIn a (bound_vars C))
         (bc10 : !LIn b (bound_vars C))
         (bc11 : !LIn b (bound_vars Q))
         (bc12 : !LIn f (bound_vars Q))
         (bc13 : !LIn q (bound_vars Q))
         (bc14 : !LIn w [q,a,f,v])
         (bc15 : !LIn a (bound_vars Q)),
    rule_true lib (rule_pw_induction H Q P A B C p i ap bp ba cp ca cb w b a f v q).
Proof.
  unfold rule_pw_induction, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc
                         (snoc (snoc (snoc H (mk_hyp q P))
                                     (mk_hyp a (lsubst A [(ap, mk_var q)])))
                               (mk_hyp f
                                       (mk_function
                                          (lsubst B [(bp, mk_var q), (ba, mk_var a)]) b
                                          (mk_pw P ap A bp ba B cp ca cb C
                                                 (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))))
                         (mk_hyp v
                                 (mk_function
                                    (lsubst B [(bp, mk_var q), (ba, mk_var a)])
                                    b
                                    (mk_apply
                                       (lsubst Q [(w,mk_apply (mk_var f) (mk_var b))])
                                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))))
                      (mk_conclax (mk_apply (lsubst Q [(w,mk_sup (mk_var a) (mk_var f))]) (mk_var q))))
                   (inl eq_refl));
    simpl; intros hyp1; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hyp w (mk_pw P ap A bp ba B cp ca cb C p))))).

  (* We prove some simple facts on our sequents *)
  assert (!LIn w (free_vars p)
          # !(a = q)
          # !(f = q)
          # !(v = q)
          # !(f = a)
          # !(v = a)
          # !(v = f)
          # !(b = q)
          # !(b = a)
          # !(b = f)
          # !LIn q (free_vars P)
          # !LIn a (free_vars P)
          # !LIn f (free_vars P)
          # !LIn v (free_vars P)
          # !LIn q (free_vars p)
          # !LIn a (free_vars p)
          # !LIn f (free_vars p)
          # !LIn v (free_vars p)
          # (q <> ap -> !LIn q (free_vars A))
          # (a <> ap -> !LIn a (free_vars A))
          # (f <> ap -> !LIn f (free_vars A))
          # (v <> ap -> !LIn v (free_vars A))
          # (!LIn q [bp, ba] -> !LIn q (free_vars B))
          # (!LIn a [bp, ba] -> !LIn a (free_vars B))
          # (!LIn f [bp, ba] -> !LIn f (free_vars B))
          # (!LIn v [bp, ba] -> !LIn v (free_vars B))
          # (!LIn q [cp, ca, cb] -> !LIn q (free_vars C))
          # (!LIn a [cp, ca, cb] -> !LIn a (free_vars C))
          # (!LIn f [cp, ca, cb] -> !LIn f (free_vars C))
          # (!LIn v [cp, ca, cb] -> !LIn v (free_vars C))
          # !LIn b (free_vars p)
          # !LIn b (free_vars P)
          # (b <> ap -> !LIn b (free_vars A))
          # (!LIn b [bp, ba] -> !LIn b (free_vars B))
          # (!LIn b [cp, ca, cb] -> !LIn b (free_vars C))
          # !LIn b (free_vars Q)
          # !LIn q (free_vars Q)
          # !LIn f (free_vars Q)
          # !LIn a (free_vars Q)
          # !LIn v (free_vars Q)
          # !LIn w (vars_hyps H)
          # !LIn q (vars_hyps H)
          # !LIn a (vars_hyps H)
          # !LIn f (vars_hyps H)
          # !LIn v (vars_hyps H)) as vhyps.

  clear hyp1.
  dwfseq.

  sp;
    try (complete (assert (LIn q (remove_nvars [ap] (free_vars A)))
                          by (rw in_remove_nvars; rw in_single_iff; auto);
                   discover; auto));
    try (complete (assert (LIn a (remove_nvars [ap] (free_vars A)))
                          by (rw in_remove_nvars; rw in_single_iff; auto);
                   discover; auto));
    try (complete (assert (LIn f (remove_nvars [ap] (free_vars A)))
                          by (rw in_remove_nvars; rw in_single_iff; auto);
                   discover; auto));
    try (complete (assert (LIn v (remove_nvars [ap] (free_vars A)))
                          by (rw in_remove_nvars; rw in_single_iff; auto);
                   discover; auto));
    try (complete (assert (LIn b (remove_nvars [ap] (free_vars A)))
                          by (rw in_remove_nvars; rw in_single_iff; auto);
                   discover; auto));
    try (complete (assert (LIn q (remove_nvars [bp, ba] (free_vars B)))
                          by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn a (remove_nvars [bp, ba] (free_vars B)))
                          by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn f (remove_nvars [bp, ba] (free_vars B)))
                          by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn v (remove_nvars [bp, ba] (free_vars B)))
                          by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn b (remove_nvars [bp, ba] (free_vars B)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn q (remove_nvars [cp, ca, cb] (free_vars C)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn a (remove_nvars [cp, ca, cb] (free_vars C)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn f (remove_nvars [cp, ca, cb] (free_vars C)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn v (remove_nvars [cp, ca, cb] (free_vars C)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (assert (LIn b (remove_nvars [cp, ca, cb] (free_vars C)))
                    by (rw in_remove_nvars; auto);
                   discover; auto));
    try (complete (discover; rw in_snoc in h; repdors; subst; auto)).

  destruct vhyps as [ niwp vhyps ].
  destruct vhyps as [ neaq vhyps ].
  destruct vhyps as [ nefq vhyps ].
  destruct vhyps as [ nevq vhyps ].
  destruct vhyps as [ nefa vhyps ].
  destruct vhyps as [ neva vhyps ].
  destruct vhyps as [ nevf vhyps ].
  destruct vhyps as [ nebq vhyps ].
  destruct vhyps as [ neba vhyps ].
  destruct vhyps as [ nebf vhyps ].
  destruct vhyps as [ niqP vhyps ].
  destruct vhyps as [ niaP vhyps ].
  destruct vhyps as [ nifP vhyps ].
  destruct vhyps as [ nivP vhyps ].
  destruct vhyps as [ niqp vhyps ].
  destruct vhyps as [ niap vhyps ].
  destruct vhyps as [ nifp vhyps ].
  destruct vhyps as [ nivp vhyps ].
  destruct vhyps as [ niqA vhyps ].
  destruct vhyps as [ niaA vhyps ].
  destruct vhyps as [ nifA vhyps ].
  destruct vhyps as [ nivA vhyps ].
  destruct vhyps as [ niqB vhyps ].
  destruct vhyps as [ niaB vhyps ].
  destruct vhyps as [ nifB vhyps ].
  destruct vhyps as [ nivB vhyps ].
  destruct vhyps as [ niqC vhyps ].
  destruct vhyps as [ niaC vhyps ].
  destruct vhyps as [ nifC vhyps ].
  destruct vhyps as [ nivC vhyps ].
  destruct vhyps as [ nibp vhyps ].
  destruct vhyps as [ nibP vhyps ].
  destruct vhyps as [ nibA vhyps ].
  destruct vhyps as [ nibB vhyps ].
  destruct vhyps as [ nibC vhyps ].
  destruct vhyps as [ nibQ vhyps ].
  destruct vhyps as [ niqQ vhyps ].
  destruct vhyps as [ nifQ vhyps ].
  destruct vhyps as [ niaQ vhyps ].
  destruct vhyps as [ nivQ vhyps ].
  destruct vhyps as [ niwH vhyps ].
  destruct vhyps as [ niqH vhyps ].
  destruct vhyps as [ niaH vhyps ].
  destruct vhyps as [ nifH nivH ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_snoc in sim; exrepnd; subst; allsimpl.
  lsubst_tac.
  rw @member_eq.
  clear pC1 pC2 pt1 pt2 c2 c3.

(*
  duplicate sim1 as eqinpw.
  apply equality_in_pw in sim1; exrepnd.

  assert (eqp (lsubstc p wp s1a cvp) (lsubstc p wp s2a c))
         as eqps.
  (* begin proof of assert *)
  generalize (eqh (snoc s2a (w,t2))); intro imp.
  dest_imp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a s2a t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_pw in imp0; repnd.
  generalize (equality_eq1
                (lsubstc P wP s1a0 cvP)
                (lsubstc P wP s1a0 cvP)
                (lsubstc p wp s1a0 cvp)
                (lsubstc p wp s2a0 c)
                eqp); intro k; dest_imp k hyp.
  apply k; sp.
  (* end proof of assert *)
*)

  (* we use param_w_ind *)
  revert_dependents s2a.
  generalize (param_w_ind3
                lib (lsubstc P wP s1a cvP)
                ap
                (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                bp ba
                (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                cp ca cb
                (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)
                (fun p1 p2 t1 t2 =>
                   forall p3,
                     equality lib p1 p3 (lsubstc P wP s1a cvP)
                     -> forall t3,
                          equality lib t1 t3
                                   (mkc_pw (lsubstc P wP s1a cvP) ap
                                           (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA) bp ba
                                           (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB) cp ca cb
                                           (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)
                                           p1)
                          -> forall s2a,
                               similarity lib s1a s2a H
                               -> forall (c1 : cover_vars Q (snoc s1a (w, t1)))
                                         (c0 : cover_vars Q (snoc s2a (w, t3)))
                                         (c : cover_vars p s2a),
                                    tequality
                                      lib (mkc_apply (lsubstc Q w1 (snoc s1a (w, t1)) c1) p1)
                                      (mkc_apply (lsubstc Q w1 (snoc s2a (w, t3)) c0) p3)
                                      # member lib mkc_axiom
                                      (mkc_apply (lsubstc Q w1 (snoc s1a (w, t1)) c1) p1)));
    intros h.


  (* we prove that Q preserves cequivc *)
  autodimp h hyp.
  intros p1 p2.
  introv ceq1 ceq2 cl.
  introv eip eiw sim.
  intros c2 c3 c.
  assert (cover_vars Q (snoc s1a (w, t0)))
         as cov1
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w,t4)); auto;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; auto).

  assert (equality lib t0 t6
                   (mkc_pw (lsubstc P wP s1a cvP)
                           ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                           bp ba (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                           cp ca cb (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)
                           p1))
         as eiw2
         by (apply @equality_respects_cequivc_left with (t1 := t4); auto;
             apply cequivc_sym; auto).

  generalize (cl p3 eip t6 eiw2 s2a sim cov1 c3 c); clear cl; intro cl; repnd.

  assert (cequivc
            lib (mkc_apply (lsubstc Q w1 (snoc s1a (w, t0)) cov1) p1)
            (mkc_apply (lsubstc Q w1 (snoc s1a (w, t4)) c2) p1))
         as cequiv1.
  (* begin proof of assert *)
  apply implies_cequivc_apply; auto.
  unfold cequivc; simpl.
  unfold csubst.
  allrw @csub2sub_snoc.
  apply cequiv_lsubst.

  apply isprogram_lsubst.
  apply wf_apply_iff in wfct; repnd; rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; inj; allapply @in_csub2sub; auto.
  introv k; rw @cover_vars_eq in c1; rw subvars_prop in c1; apply c1 in k.
  splst in k; splst; auto.

  apply isprogram_lsubst.
  apply wf_apply_iff in wfct; repnd; rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; inj; allapply @in_csub2sub; auto.
  introv k; rw @cover_vars_eq in c1; rw subvars_prop in c1; apply c1 in k.
  splst in k; splst; auto.

  apply cequiv_subst_snoc; auto.
  apply cequiv_subst_csub2sub_refl.
  (* end proof of assert *)

(*
  assert (cequivc
            (mkc_apply (lsubstc Q w1 (snoc s2a (w, t3)) cov2) p2)
            (mkc_apply (lsubstc Q w1 (snoc s2a (w, t5)) c3) p2))
         as cequivc2.
  (* begin proof of assert *)
  apply implies_cequivc_apply; try (complete sp).
  unfold cequivc; simpl.
  unfold csubst.
  allrw @csub2sub_snoc.
  apply cequiv_lsubst.

  apply isprogram_lsubst.
  apply wf_apply_iff in wfct; repnd; rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; cpx; allapply @in_csub2sub; sp.
  introv k; rw @cover_vars_eq in c3; rw subvars_prop in c3; apply c3 in k.
  splst in k; splst; sp.

  apply isprogram_lsubst.
  apply wf_apply_iff in wfct; repnd; rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; cpx; allapply @in_csub2sub; sp.
  introv k; rw @cover_vars_eq in c3; rw subvars_prop in c3; apply c3 in k.
  splst; splst in k; sp.

  apply cequiv_subst_snoc; sp.
  apply cequiv_subst_csub2sub_refl.
  (* end proof of assert *)
*)

  dands.

  apply tequality_respects_cequivc_left
        with (T1 := mkc_apply (lsubstc Q w1 (snoc s1a (w, t0)) cov1) p1);
    try (complete sp).
(*  apply tequality_respects_cequivc_right
        with (T2 := mkc_apply (lsubstc Q w1 (snoc s2a (w, t6)) c3) p2);
    try (complete sp).*)

  apply @cequivc_preserving_equality
        with (A := mkc_apply (lsubstc Q w1 (snoc s1a (w, t0)) cov1) p1);
    try (complete sp).


  (* we prove the induction case *)
  autodimp h hyp.
  introv bcvb eqinp eqina eqinf ind.
  introv eip eiw sim c; introv.
  simpl in bcvb.

  applydup (@equality_in_pw_v2 o lib vb) in eiw as eiw'; exrepnd.
  clear eiw'1.
  uncast.
  apply computes_to_valc_isvalue_eq in eiw'0.
  symmetry in eiw'0; eqconstr eiw'0; try (complete apply_iscvalue).


  (* we use hyp1 to prove that *)
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) (v, lam_axiom))
                   (snoc (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3)) (v, lam_axiom)));
    clear hyp1; intro hyp1.


  (* first we prove the hyps_functionality *)
  autodimp hyp1 hyp.
  introv sim'.

  (* we destruct the similarity hyp *)
  rw @similarity_snoc in sim'; simpl in sim'; exrepnd; cpx.
  rw @similarity_snoc in sim'3; simpl in sim'3; exrepnd; cpx.
  rw @similarity_snoc in sim'4; simpl in sim'4; exrepnd; cpx.
  rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; cpx.
  lsubst_tac.

(*
  (* this is going to be useful *)
  assert (cover_vars p s2a1)
         as cvp2
         by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  assert (eqp (lsubstc p wp s1a0 cvp) (lsubstc p wp s2a1 cvp2))
         as eqps2.
  (* begin proof of assert *)
  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_pw in imp0; repnd; clear_irr.
  generalize (equality_eq1
                (lsubstc P wP s1a p6)
                (lsubstc P wP s1a p6)
                (lsubstc p wp s1a cvp)
                (lsubstc p wp s2a0 cvp2)
                eqp); intro k; autodimp k hyp.
  apply k; sp.
  (* end proof of assert *)
*)

  (* we destruct the eq_hyps concl *)
  assert (cover_vars
            (mk_function
               (lsubst B [(bp, mk_var q), (ba, mk_var a)])
               b
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))
            (snoc (snoc (snoc s2a1 (q, t9)) (a, t7)) (f, t5)))
         as cv
         by (apply cover_vars_change_sub with (sub1 := snoc (snoc (snoc s1a0 (q,t8)) (a, t6)) (f, t0)); auto;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; auto).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc (snoc s1a0 (q, t8)) (a, t6)) (f, t0))
         (snoc (snoc (snoc s2a1 (q, t9)) (a, t7)) (f, t5))
         (@lam_axiom o) t4
         w2 p4 cv; sp.

  assert (cover_vars
            (mk_function (lsubst B [(bp, mk_var q), (ba, mk_var a)]) b
                         (mk_pw P ap A bp ba B cp ca cb C
                                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))
            (snoc (snoc s2a1 (q, t9)) (a, t7)))
         as cv1
         by (apply cover_vars_change_sub with (sub1 := snoc (snoc s1a0 (q, t8)) (a, t6)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc s1a0 (q, t8)) (a, t6))
         (snoc (snoc s2a1 (q, t9)) (a, t7))
         t0 t5
         w3 p5 cv1; sp.

  assert (cover_vars (lsubst A [(ap, mk_var q)]) (snoc s2a1 (q, t9)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (q, t8)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a0 (q, t8)) (snoc s2a1 (q, t9))
         t6 t7 w4 p6 cv2; sp.

  assert (cover_vars P s2a1)
         as cv3
         by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a0 s2a1 t8 t9 wP p7 cv3; sp.


  (* the base eq_hyps is easy *)
  apply @hyps_functionality_init_seg_snoc2 with (t' := t2) (w := w0) (c := p0) in eqh; sp.
  lsubst_tac; sp.


  (* the tequality of the P's comes from eqh *)
  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_pw in imp0; repnd; sp.


  (* the tequality of the A's comes from eqh *)
  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_pw in imp0; repnd.
  generalize (imp2 t8 t9); intro teq.
  autodimp teq hyp.

  assert (substc t8 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
          = lsubstc (lsubst A [(ap, mk_var q)]) w4 (snoc s1a (q, t8)) p6)
         as eq1.
  (* begin proof of assert *)
  revert_dependents w4.
  revert_dependents p6.
  revert_dependents cv2.
  rw @fold_subst.
  introv cv2 eia.
  symmetry.
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq1; clear eq1.

  assert (substc t9 ap (lsubstc_vars A wA (csub_filter s2a0 [ap]) [ap] cvA0)
          = lsubstc (lsubst A [(ap, mk_var q)]) w4 (snoc s2a0 (q, t9)) cv2)
         as eq2.
  (* begin proof of assert *)
  revert_dependents w4.
  revert_dependents p6.
  revert_dependents cv2.
  rw @fold_subst.
  introv eia.
  symmetry.
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq2; sp.


  (* we now prove the tequality of b:B(p,a)->pW(C(p,a,b)) *)
  lsubst_tac.
  rw @tequality_function; dands.

  (* 1st we prove that the domain is functional *)
  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_pw in imp0; repnd.
  generalize (imp4 t8 t9); intro teq.
  autodimp teq hyp.
  generalize (teq t6 t7); clear teq; intro teq.
  autodimp teq hyp.
  revert sim'3.
  revert_dependents w4.
  revert_dependents p6.
  rw @fold_subst; introv e.

  assert (lsubstc (subst A ap (mk_var q)) w4 (snoc s1a (q, t8)) p6
          = substc t8 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq; sp.

  assert (lsubstc2 bp t8 ba t6
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s1a (q, t8)) (a, t6)) c5) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t8 t6 wB s1a cvB q a w6 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  assert (lsubstc2 bp t9 ba t7
                   (lsubstc_vars B wB (csub_filter s2a0 [bp, ba]) [bp, ba] cvB0)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s2a0 (q, t9)) (a, t7)) c7) as eq2.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t9 t7 wB s2a0 cvB0 q a w6 c7); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq1; rw <- eq2; sp.


  (* then we prove that the co-domain is functional *)
  introv eb.
  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  duplicate imp0 as teqinpw.
  lsubst_tac.


  assert (substc a0 b
                 (lsubstc_vars
                    (mk_pw P ap A bp ba B cp ca cb C
                           (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w8
                    (csub_filter (snoc (snoc s1a (q, t8)) (a, t6)) [b]) [b] c6)
          = mkc_pw (lsubstc P wP s1a p7)
                   ap
                   (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                   bp ba
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                   cp ca cb
                   (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                 [cp, ca, cb] cvC)
                   (lsubstc3 cp t8 ca t6 cb a0
                             (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                           [cp, ca, cb] cvC)))
         as eq1.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])
            (snoc (snoc s1a (q, t8)) (a, t6)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a0 b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s1a (q, t8)) (a, t6))
                cvc w8 c6); intro eq.
  rw <- eq; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a0)]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (simpl; sp));
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp)).

  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a0).
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc; rw eq; introv; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)])
                  wp0 (snoc (snoc s1a (q, t8)) (a, t6)) cvp1
          = lsubstc3 cp t8 ca t6 cb a0
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)


  assert (substc a' b
                 (lsubstc_vars
                    (mk_pw P ap A bp ba B cp ca cb C
                           (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w8
                    (csub_filter (snoc (snoc s2a0 (q, t9)) (a, t7)) [b]) [b] c8)
          = mkc_pw (lsubstc P wP s2a0 cvP)
                   ap
                   (lsubstc_vars A wA (csub_filter s2a0 [ap]) [ap] cvA0)
                   bp ba
                   (lsubstc_vars B wB (csub_filter s2a0 [bp, ba]) [bp, ba] cvB0)
                   cp ca cb
                   (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb])
                                 [cp, ca, cb] cvC0)
                   (lsubstc3 cp t9 ca t7 cb a'
                             (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb])
                                           [cp, ca, cb] cvC0)))
         as eq2.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])
            (snoc (snoc s2a0 (q, t9)) (a, t7)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a' b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s2a0 (q, t9)) (a, t7))
                cvc w8 c8); intro eq.
  rw <- eq; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a')]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (simpl; sp));
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp)).

  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a').
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc; rw eq; introv; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a')])
                  wp0 (snoc (snoc s2a0 (q, t9)) (a, t7)) cvp1
          = lsubstc3 cp t9 ca t7 cb a'
                     (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb]) [cp, ca, cb] cvC0))
         as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw eq1; rw eq2; clear eq1 eq2.

  apply @tequality_mkc_pw_implies
        with
        (p1 := lsubstc p wp s1a cvp)
        (p2 := lsubstc p wp s2a0 cvp0); sp.

  apply @tequality_mkc_pw in teqinpw; repnd.
  generalize (teqinpw3 t8 t9); intro eq.
  autodimp eq hyp.
  generalize (eq t6 t7); clear eq; intro eq.
  autodimp eq hyp.
  assert (lsubstc (lsubst A [(ap, mk_var q)]) w4 (snoc s1a (q, t8)) p6
          = substc t8 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA))
         as eq
         by (apply lsubstc_subst_snoc_eq;
             try (complete sp);
             try (complete (allapply @similarity_dom; repnd; allrw; sp))).
  rw <- eq; sp.
  generalize (eq a0 a'); clear eq; intro eq.
  autodimp eq hyp.
  generalize (lsubstc2_lsubstc_var bp ba B t8 t6 wB s1a cvB q a w6 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).

  (* we now prove that the squashed function is functional using hyp2 and eqh *)
  lsubst_tac.

  generalize (eqh (snoc s2a1 (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a1 t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply @tequality_mkc_pw in imp0; repnd.

  rw @tequality_function; dands.

  generalize (imp4 t8 t9); intro teq.
  autodimp teq hyp.
  generalize (teq t6 t7); clear teq; intro teq.
  autodimp teq hyp.
  revert sim'3.
  revert_dependents w4.
  revert_dependents p6.
  rw @fold_subst; introv e.

  assert (lsubstc (subst A ap (mk_var q)) w4 (snoc s1a (q, t8)) p6
          = substc t8 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq; sp.

  assert (!LIn f (free_vars (lsubst B [(bp, mk_var q), (ba, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                B [(bp, mk_var q), (ba, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors; try (complete sp).
  (* end proof of assert *)

  (* nifB1 allows lsubst_tac to make progress *)
  lsubst_tac.

  assert (lsubstc2 bp t8 ba t6
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s1a (q, t8)) (a, t6)) c5) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t8 t6 wB s1a cvB q a w6 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  assert (lsubstc2 bp t9 ba t7
                   (lsubstc_vars B wB (csub_filter s2a0 [bp, ba]) [bp, ba] cvB0)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s2a0 (q, t9)) (a, t7)) c9) as eq2.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t9 t7 wB s2a0 cvB0 q a w6 c9); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq1; rw <- eq2; sp.


  (* now we use hyp2 *)
  introv eib.

  assert (!LIn f (free_vars (lsubst B [(bp, mk_var q), (ba, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                B [(bp, mk_var q), (ba, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors; try (complete sp).
  (* end proof of assert *)

  (* nifB1 allows lsubst_tac to make progress *)
  lsubst_tac.

  assert (lsubstc2 bp t8 ba t6
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s1a (q, t8)) (a, t6)) c5) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t8 t6 wB s1a cvB q a w6 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq1 in eib; clear eq1.

  assert (cover_vars Q (snoc s1a (w, mkc_apply t0 a0)))
         as cv1
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w, mkc_sup t6 t0)); sp;
             splst; sp).

  assert (cover_vars Q (snoc s2a0 (w, mkc_apply t5 a')))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w, mkc_sup t6 t0)); sp;
             repeat (rw @dom_csub_snoc); simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  assert (equality
            lib (lsubstc3 cp t8 ca t6 cb a0
                      (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
            (lsubstc3 cp t9 ca t7 cb a'
                      (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb]) [cp, ca, cb] cvC0))
            (lsubstc P wP s1a p7))
         as eCs.
  (* begin proof of assert *)
  apply imp5; auto.
  assert (lsubstc (subst A ap (mk_var q)) w4 (snoc s1a (q, t8)) p6
          = substc t8 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)) as eq.
  (* - begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* - end proof of assert *)
  rw <- eq; sp.
  (* end proof of assert *)

  assert (equality lib (mkc_apply t0 a0) (mkc_apply t5 a')
                   (mkc_pw (lsubstc P wP s1a p7) ap
                           (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA) bp ba
                           (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB) cp ca cb
                           (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)
                           (lsubstc3 cp t8 ca t6 cb a0
                                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                                   [cp, ca, cb] cvC))))
         as eaps.
  (* begin proof of assert *)
  rw @equality_in_function in sim'2; repnd.
  assert (lsubstc2 bp t8 ba t6
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w6
                    (snoc (snoc s1a (q, t8)) (a, t6)) c5) as eq1.
  (* - begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t8 t6 wB s1a cvB q a w6 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* - end proof of assert *)
  rw eq1 in eib.
  generalize (sim'2 a0 a' eib); intro e.

  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])
            (snoc (snoc s1a (q, t8)) (a, t6)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a0 b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s1a (q, t8)) (a, t6))
                cvc w8 c6); intro eq.
  rw <- eq in e; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a0)]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (simpl; sp));
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp)).

  revert dependent wfc; revert dependent cvc; rw eq; introv; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a0).
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc; rw eq; introv; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)])
                  wp0 (snoc (snoc s1a (q, t8)) (a, t6)) cvp1
          = lsubstc3 cp t8 ca t6 cb a0
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  generalize (ind a0 a' eib
                  (lsubstc3 cp t9 ca t7 cb a'
                            (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb]) [cp, ca, cb] cvC0))
                  eCs
                  (mkc_apply t5 a')
                  eaps
                  s2a0
                  sim'6
                  cv1
                  cv2
                  cvp0); intro teq; repnd.

(*
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a (q, (lsubstc3
                                          cp t7 ca t5 cb a0
                                          (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                                        [cp, ca, cb] cvC))))
                         (w, mkc_apply t0 a0))
                   (snoc (snoc s2a0 (q, (lsubstc3
                                           cp t8 ca t6 cb a'
                                           (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb])
                                                         [cp, ca, cb] cvC0))))
                         (w, mkc_apply t4 a'))); clear hyp2; intro hyp2.

  (* we prove the hyps_functionality part of hyp2 *)
  autodimp hyp2 hyp.
  introv sim''.
  rw @similarity_snoc in sim''; simpl in sim''; exrepnd; subst; cpx.
  rw @similarity_snoc in sim''3; simpl in sim''3; exrepnd; subst; cpx.

  assert (cover_vars (mk_pw P ap A bp ba B cp ca cb C (mk_var q))
                     (snoc s2a2 (q, t11)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := (snoc s1a0
                                                             (q,
                                                              lsubstc3 cp t7 ca t5 cb a0
                                                                       (lsubstc_vars C wC (csub_filter s1a0 [cp, ca, cb])
                                                                                     [cp, ca, cb] cvC)))); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a0
               (q,
                lsubstc3 cp t7 ca t5 cb a0
                         (lsubstc_vars C wC (csub_filter s1a0 [cp, ca, cb])
                                       [cp, ca, cb] cvC)))
         (snoc s2a2 (q, t11))
         (mkc_apply t0 a0)
         t2
         w0 p0 cv2.
  sp; proof_irr.

  assert (cover_vars P s2a2)
         as cv3
         by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  auto.
  exists s1a0 s2a2
         (lsubstc3 cp t7 ca t5 cb a0
                   (lsubstc_vars C wC (csub_filter s1a0 [cp, ca, cb]) [cp, ca, cb] cvC))
         t11
         wP p8 cv3.
  sp; proof_irr.

  generalize (eqh (snoc s2a2 (w, t10))); intro imp.
  autodimp imp hyp.

  rw @similarity_snoc; simpl.
  exists s1a0 s2a2 t9 t10 w8 p1; sp.
  lsubst_tac; auto.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.

  generalize (eqh (snoc s2a2 (w, t10))); intro imp.
  autodimp imp hyp.

  rw @similarity_snoc; simpl.
  exists s1a0 s2a2 t9 t10 w8 p1; sp.
  lsubst_tac; auto.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac; auto.
  apply @tequality_mkc_pw in imp6; repnd; auto.

  generalize (eqh (snoc s2a2 (w, t10))); intro imp.
  autodimp imp hyp.

  rw @similarity_snoc; simpl.
  exists s1a0 s2a2 t9 t10 w8 p1; sp.
  lsubst_tac; auto.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  lsubstc_snoc_vs.
  apply @tequality_mkc_pw_implies
        with (p1 := lsubstc p wp s1a cvp) (p2 := lsubstc p wp s2a1 cvp1); auto.

  (* we prove the similarity part of hyp2 *)
  autodimp hyp2 hyp.

  assert (wf_term (mk_pw P ap A bp ba B cp ca cb C (mk_var q)))
    as wfpw by (apply wf_pw; sp).

  assert (cover_vars (mk_pw P ap A bp ba B cp ca cb C (mk_var q))
                     (snoc s1a
                           (q,
                            lsubstc3 cp t7 ca t5 cb a0
                                     (lsubstc_vars C wC
                                                   (csub_filter s1a [cp, ca, cb])
                                                   [cp, ca, cb] cvC))))
    as cvpw.
  apply cover_vars_pw; sp;
  try (complete (apply cover_vars_snoc_weak; sp));
  try (complete (apply cover_vars_upto_snoc_weak; sp));
  try (complete (apply cover_vars_upto_csub_filter_snoc_weak; sp));
  try (complete (apply cover_vars_var; splst; sp)).

  rw @similarity_snoc; simpl.
  exists (snoc s1a
               (q,
                lsubstc3 cp t7 ca t5 cb a0
                         (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)))
         (snoc s2a0
               (q,
                lsubstc3 cp t8 ca t6 cb a'
                         (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb])
                                       [cp, ca, cb] cvC0)))
         (mkc_apply t0 a0)
         (mkc_apply t4 a')
         wfpw cvpw; sp.

  rw @similarity_snoc; simpl.
  exists s1a s2a0
         (lsubstc3 cp t7 ca t5 cb a0
                   (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
         (lsubstc3 cp t8 ca t6 cb a'
                   (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb]) [cp, ca, cb] cvC0))
         wP p6; sp.

  generalize (imp5 t7 t8); intro eic.
  autodimp eic hyp.
  generalize (eic t5 t6); clear eic; intro eic.
  autodimp eic hyp.

  assert (lsubstc (subst A ap (mk_var q)) w4 (snoc s1a (q, t7)) p5
          = substc t7 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw <- eq; sp.

  generalize (eic a0 a'); clear eic; intro eic.
  autodimp eic hyp.

  assert (!LIn f (free_vars (lsubst B [(bp, mk_var q), (ba, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                B [(bp, mk_var q), (ba, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors; try (complete sp).
  (* end proof of assert *)

  (* nifB1 allows lsubst_tac to make progress *)
  lsubst_tac.

  assert (lsubstc2 bp t7 ba t5
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w5
                    (snoc (snoc s1a (q, t7)) (a, t5)) c7) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B t7 t5 wB s1a cvB q a w5 c7); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq1; sp.

  lsubst_tac.
  lsubstc_snoc_vs.
  duplicate sim'2 as eqif.
  rw @equality_in_function in eqif; repnd.
  generalize (eqif a0 a'); intro eif.
  autodimp eif hyp.

  assert (!LIn f (free_vars (lsubst B [(bp, mk_var q), (ba, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                B [(bp, mk_var q), (ba, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors; try (complete sp).
  (* end proof of assert *)

  (* nifB1 allows lsubst_tac to make progress *)
  lsubst_tac; sp.

  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])
            (snoc (snoc s1a (q, t7)) (a, t5)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a0 b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s1a (q, t7)) (a, t5))
                cvc w9 c8); intro eq.
  rw <- eq in eif; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a0)]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp)).

  revert wfc cvc eif; rw eq; introv eif; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a0).
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc eif; rw eq; introv eif; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)])
                  wp1 (snoc (snoc s1a (q, t7)) (a, t5)) cvp1
          = lsubstc3 cp t7 ca t5 cb a0
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq in eif; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)


  (* now we can start using hyp2 *)
  exrepnd.
  lsubst_tac.
  lsubstc_snoc_vs.
  (* from hyp0 *)
  apply @tequality_in_uni_implies_tequality in hyp0;
    try (complete (rw <- member_member_iff in hyp1;
                   apply member_in_uni in hyp1; sp)).
*)

  assert (substc a0 b
                 (lsubstc_vars
                    (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                              (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w7
                    (csub_filter (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0)) [b])
                    [b] c4)
          = mkc_apply (lsubstc Q w1 (snoc s1a (w, mkc_apply t0 a0)) cv1)
                      (lsubstc3 cp t8 ca t6 cb a0
                                (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                              [cp, ca, cb] cvC)))
         as eq1.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])
            (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a0 b
                (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                          (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0))
                cvc w7 c4); intro eq.
  rw <- eq; clear eq.

  revert wfc cvc.
  rw @csubst_mk_apply.
  rw @fold_subst; introv.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a0).
  introv eq.
  repeat (autodimp eq hyp).
  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_subst_pw_Q Q w f b a0).
  intro eq; repeat (autodimp eq hyp); try (complete (repeat (rw not_over_or in bc7); sp)).
  revert wfc cvc; rw eq; introv; clear eq.

  assert (!LIn f (free_vars (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)]))) as nifC1.
  (* - begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; allrw @free_vars_cterm; simpl; intro k; repdors; try (complete sp).
  (* - end proof of assert *)

  lsubst_tac.
  proof_irr; GC.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)])
                  w9 (snoc (snoc s1a (q, t8)) (a, t6)) c11
          = lsubstc3 cp t8 ca t6 cb a0
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubstc (subst Q w (mk_apply (mk_var f) (get_cterm a0))) w0
                  (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0)) c9
          = lsubstc Q w1 (snoc s1a (w, mkc_apply t0 a0)) cv1)
         as eq; try (complete (rw eq; auto)).

  assert (wf_term (mk_apply (mk_var f) (get_cterm a0))) as wa by (apply wf_apply; eauto with wf).

  assert (cover_vars (mk_apply (mk_var f) (get_cterm a0))
                     (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0)))
         as ca1
         by (apply cover_vars_apply; sp;apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0)) [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,mkc_sup t6 t0)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w, mkc_sup t6 t0)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp).

  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm a0))
                w Q w0
                (snoc (snoc (snoc s1a (q, t8)) (a, t6)) (f, t0))
                c9 wa ca1 w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq.
  (* NOTE: lsubstc_cterm should go into lsubst_tac *)
  allrw.
  generalize (simple_substc2 (mkc_apply t0 a0) w Q s1a w1 cv1 c16).
  intro eq1.
  autodimp eq1 hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)


  assert (substc a' b
                 (lsubstc_vars
                    (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                              (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w7
                    (csub_filter (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5)) [b])
                    [b] c8)
          = mkc_apply (lsubstc Q w1 (snoc s2a0 (w, mkc_apply t5 a')) cv2)
                      (lsubstc3 cp t9 ca t7 cb a'
                                (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb])
                                              [cp, ca, cb] cvC0)))
         as eq2.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])
            (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a' b
                (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                          (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5))
                cvc w7 c8); intro eq.
  rw <- eq; clear eq.

  revert wfc cvc.
  rw @csubst_mk_apply.
  rw @fold_subst; introv.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a').
  introv eq.
  repeat (autodimp eq hyp).
  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_subst_pw_Q Q w f b a').
  intro eq; repeat (autodimp eq hyp); try (complete (repeat (rw not_over_or in bc7); sp)).
  revert wfc cvc; rw eq; introv; clear eq.

  assert (!LIn f (free_vars (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a')]))) as nifC1.
  (* - begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint
                C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a')]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; allrw @free_vars_cterm; simpl; intro k; repdors; try (complete sp).
  (* - end proof of assert *)

  lsubst_tac.
  proof_irr; GC.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a')])
                  w9 (snoc (snoc s2a0 (q, t9)) (a, t7)) c11
          = lsubstc3 cp t9 ca t7 cb a'
                     (lsubstc_vars C wC (csub_filter s2a0 [cp, ca, cb]) [cp, ca, cb] cvC0))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubstc (subst Q w (mk_apply (mk_var f) (get_cterm a'))) w0
                  (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5)) c9
          = lsubstc Q w1 (snoc s2a0 (w, mkc_apply t5 a')) cv2)
         as eq; try (complete (rw eq; auto)).

  assert (wf_term (mk_apply (mk_var f) (get_cterm a'))) as wa by (apply wf_apply; eauto with wf).

  assert (cover_vars (mk_apply (mk_var f) (get_cterm a'))
                     (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5)))
         as ca1
         by (apply cover_vars_apply; sp;apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5)) [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,mkc_sup t6 t0)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w, mkc_sup t6 t0)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).

  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm a'))
                w Q w0
                (snoc (snoc (snoc s2a0 (q, t9)) (a, t7)) (f, t5))
                c9 wa ca1 w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq.
  (* NOTE: lsubstc_cterm should go into lsubst_tac *)
  allrw.
  generalize (simple_substc2 (mkc_apply t5 a') w Q s2a0 w1 cv2 c16).
  intro e.
  autodimp e hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw eq1; rw eq2; clear eq1 eq2.
  auto.


  (* now we prove the similarity result *)
  autodimp hyp1 hyp.

  assert (wf_term
            (mk_function
               (lsubst B [(bp, mk_var q), (ba, mk_var a)])
               b
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))))
         as wfsq.
  (* begin proof of assert *)
  apply wf_function_iff; dands.
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  apply wf_apply_iff; dands;
  apply lsubst_preserves_wf_term; sp;
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  (* end proof of assert *)

  assert (cover_vars
            (mk_function
               (lsubst B [(bp, mk_var q), (ba, mk_var a)])
               b
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))
            (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)))
         as cvsq.
  (* begin proof of assert *)
  apply cover_vars_function; dands.
  apply cover_vars_lsubst_if; simpl.
  dup cvB as z.
  unfold cover_vars_upto in z.
  prove_subvars z; allsimpl.
  splst; splst in x; sp.
  introv k; sp; cpx.
  apply cover_vars_var; repeat (rw @dom_csub_snoc); repeat (rw in_snoc); sp.
  apply cover_vars_var; repeat (rw @dom_csub_snoc); repeat (rw in_snoc); sp.
  apply cover_vars_upto_apply; sp.
  apply cover_vars_upto_lsubst_if; simpl.
  dup c0 as z.
  rw @cover_vars_eq in z.
  prove_subvars z.
  splst; splst in x; sp.
  destruct (eq_var_dec b v0); sp; right; right; sp.
  introv j; sp; cpx.
  apply cover_vars_upto_apply; sp.
  apply cover_vars_upto_var; simpl.
  splst.
  destruct (eq_var_dec b f); sp; right; sp.
  apply cover_vars_upto_var; simpl; sp.
  apply cover_vars_upto_lsubst_if.
  dup cvC as z.
  unfold cover_vars_upto in z.
  prove_subvars z.
  splst; splst in x; sp.
  destruct (eq_var_dec b v0); sp.
  introv k; allsimpl; sp; cpx.
  apply cover_vars_upto_var; simpl; sp.
  splst.
  destruct (eq_var_dec b q); sp; right; sp.
  apply cover_vars_upto_var; simpl; sp.
  splst.
  destruct (eq_var_dec b a); sp; right; sp.
  apply cover_vars_upto_var; simpl; sp.
  splst.
  (* end proof of assert *)

  rw @similarity_snoc; simpl.
  exists (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
         (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3))
         (@lam_axiom o)
         (@lam_axiom o)
         wfsq cvsq; sp.

  assert (wf_term
            (mk_function
               (lsubst B [(bp, mk_var q), (ba, mk_var a)])
               b
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))))
         as wff.
  (* begin proof of assert *)
  apply wf_function_iff; dands.
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  apply wf_pw; sp.
  apply lsubst_preserves_wf_term; sp;
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  (* end proof of assert *)

  assert (cover_vars
            (mk_function
               (lsubst B [(bp, mk_var q), (ba, mk_var a)])
               b
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])))
            (snoc (snoc s1a (q, p1)) (a, a1))) as cvf.
  (* begin proof of assert *)
  apply cover_vars_function; sp.
  apply cover_vars_lsubst_if; simpl.
  dup cvB as z.
  unfold cover_vars_upto in z.
  prove_subvars z; allsimpl.
  splst; splst in x; sp.
  introv k; sp; cpx.
  apply cover_vars_var; splst; sp.
  apply cover_vars_var; splst; sp.
  apply cover_vars_upto_pw; sp.
  dup cvP as z.
  rw @cover_vars_eq in z; unfold cover_vars_upto; prove_subvars z; splst.
  destruct (eq_var_dec b v0); sp; right; sp.
  dup cvA as z.
  unfold cover_vars_upto in z; unfold cover_vars_upto; prove_subvars z; splst; splst in x; sp.
  destruct (eq_var_dec ap v0); destruct (eq_var_dec b v0); sp.
  dup cvB as z.
  unfold cover_vars_upto in z; unfold cover_vars_upto; prove_subvars z; splst; splst in x; sp.
  destruct (eq_var_dec bp v0); destruct (eq_var_dec ba v0); destruct (eq_var_dec b v0); sp.
  dup cvC as z.
  unfold cover_vars_upto in z; unfold cover_vars_upto; prove_subvars z; splst; splst in x; sp.
  destruct (eq_var_dec cp v0); destruct (eq_var_dec ca v0); destruct (eq_var_dec cb v0); destruct (eq_var_dec b v0); sp.
  apply cover_vars_upto_lsubst_if; simpl.
  dup cvC as z.
  unfold cover_vars_upto in z.
  prove_subvars z; splst; splst in x; sp.
  destruct (eq_var_dec b v0); sp; right; right; sp.
  introv j; sp; cpx.
  apply cover_vars_upto_var; simpl.
  splst.
  destruct (eq_var_dec b q); sp; right; sp.
  apply cover_vars_upto_var; simpl.
  splst.
  destruct (eq_var_dec b a); sp; right; sp.
  apply cover_vars_upto_var; simpl.
  splst; sp.
  (* end proof of assert *)

  rw @similarity_snoc; simpl.
  exists (snoc (snoc s1a (q, p1)) (a, a1))
         (snoc (snoc s2a (q, p3)) (a, a3))
         f1 f3
         wff cvf; sp.

  assert (wf_term (lsubst A [(ap, mk_var q)])) as wfa.
  (* begin proof of assert *)
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  (* end proof of assert *)

  assert (cover_vars (lsubst A [(ap, mk_var q)]) (snoc s1a (q, p1))) as cva.
  (* begin proof of assert *)
  apply cover_vars_lsubst_if; simpl.
  dup cvA as z.
  unfold cover_vars_upto in z; prove_subvars z; splst; splst in x; sp.
  introv j; sp; cpx.
  apply cover_vars_var; simpl.
  splst; sp.
  (* end proof of assert *)

  rw @similarity_snoc; simpl.
  exists (snoc s1a (q, p1)) (snoc s2a (q, p3)) a1 a3 wfa cva; sp.

  rw @similarity_snoc; simpl.
  exists s1a s2a p1 p3 wP cvP; sp.


  (* from eqina *)
  assert (lsubstc (lsubst A [(ap, mk_var q)]) wfa (snoc s1a (q, p1)) cva
          = substc p1 ap (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA))
         as eq
         by (apply lsubstc_subst_snoc_eq;
             try (complete sp);
             try (complete (allapply @similarity_dom; repnd; allrw; sp))).
  rw eq; sp.


  (* from eqinf *)
  lsubst_tac.
  dup eiw'5 as z.

  assert (lsubstc2 bp p1 ba a1
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w2
                    (snoc (snoc s1a (q, p1)) (a, a1)) c3) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B p1 a1 wB s1a cvB q a w2 c3); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)
  rw <- eq1; clear eq1.

  rw @equality_in_function3 in z; repnd.
  rw @equality_in_function3; dands.

  auto.

  introv eib.
  generalize (z a0 a' eib); intro eipw; repnd; proof_irr; clear z.

  generalize (substc_mkc_pw_vs
                p1 a1 a0 vb
                (lsubstc P wP s1a cvP)
                ap
                (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                bp ba
                (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                cp ca cb
                (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                              [cp, ca, cb] cvC)); intro e1.
  autodimp e1 hyp.
  rw e1 in eipw0; rw e1 in eipw; clear e1.

  generalize (substc_mkc_pw_vs
                p1 a1 a' vb
                (lsubstc P wP s1a cvP)
                ap
                (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                bp ba
                (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                cp ca cb
                (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                              [cp, ca, cb] cvC)); intro e2.
  autodimp e2 hyp.
  rw e2 in eipw0; clear e2.

  assert (substc a0 b
                 (lsubstc_vars
                    (mk_pw P ap A bp ba B cp ca cb C
                           (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w3
                    (csub_filter (snoc (snoc s1a (q, p1)) (a, a1)) [b]) [b] c4)
          = mkc_pw (lsubstc P wP s1a cvP)
                   ap
                   (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                   bp ba
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                   cp ca cb
                   (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                 [cp, ca, cb] cvC)
                   (lsubstc3 cp p1 ca a1 cb a0
                             (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                           [cp, ca, cb] cvC)))
         as eq1.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a0)])
            (snoc (snoc s1a (q, p1)) (a, a1)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a0 b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s1a (q, p1)) (a, a1))
                cvc w3 c4); intro eq.
  rw <- eq; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a0)]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp));
    try (complete (simpl; sp)).

  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a0).
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc; rw eq; introv; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a0)])
                  wp0 (snoc (snoc s1a (q, p1)) (a, a1)) cvp0
          = lsubstc3 cp p1 ca a1 cb a0
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)


  assert (substc a' b
                 (lsubstc_vars
                    (mk_pw P ap A bp ba B cp ca cb C
                           (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])) w3
                    (csub_filter (snoc (snoc s1a (q, p1)) (a, a1)) [b]) [b] c4)
          = mkc_pw (lsubstc P wP s1a cvP)
                   ap
                   (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA)
                   bp ba
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
                   cp ca cb
                   (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                 [cp, ca, cb] cvC)
                   (lsubstc3 cp p1 ca a1 cb a'
                             (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                           [cp, ca, cb] cvC)))
         as eq2.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_pw P ap A bp ba B cp ca cb C
                      (lsubst C
                              [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, a')])
            (snoc (snoc s1a (q, p1)) (a, a1)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                a' b
                (mk_pw P ap A bp ba B cp ca cb C
                       (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc s1a (q, p1)) (a, a1))
                cvc w3 c4); intro eq.
  rw <- eq; clear eq.

  generalize (simple_csubst_pw
                P ap A bp ba B cp ca cb C
                (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)])
                [(b, a')]); intro eq.
  simpl in eq.
  repeat (rw disjoint_remove_nvars_l in eq).
  repeat (rw disjoint_singleton_l in eq).
  repeat (rw in_remove_nvars in eq).
  repeat (autodimp eq hyp);
    try (complete (rw in_single_iff; destruct (eq_var_dec b ap); sp));
    try (complete (simpl; sp)).

  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b a').
  introv eq.
  repeat (autodimp eq hyp).

  revert wfc cvc; rw eq; introv; clear eq.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm a')])
                  wp0 (snoc (snoc s1a (q, p1)) (a, a1)) cvp0
          = lsubstc3 cp p1 ca a1 cb a'
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw eq1; rw eq2.
  sp.


  (* from ind *)
  assert (!LIn f (free_vars (lsubst B [(bp, mk_var q), (ba, mk_var a)])))
         as niffvB.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint B [(bp, mk_var q), (ba, mk_var a)]); introv eqv.
  rw eqvars_prop in eqv.
  apply eqv in k; splst in k.
  revert k.
  boolvar; simpl; intro k; sp;
  try (complete (apply nifB in k1; sp));
  try (complete (apply nifB in p4; sp));
  try (complete (apply nifB in p5; sp)).
  (* end proof of assert *)

  lsubst_tac.
(*  apply @equality_in_mkc_squash; dands; spcast;
  try (complete (apply computes_to_valc_refl; apply iscvalue_mkc_axiom)).*)

  assert (lsubstc2 bp p1 ba a1
                   (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)
          = lsubstc (lsubst B [(bp, mk_var q), (ba, mk_var a)]) w2
                    (snoc (snoc s1a (q, p1)) (a, a1)) c5) as eq1.
  (* begin proof of assert *)
  generalize (lsubstc2_lsubstc_var bp ba B p1 a1 wB s1a cvB q a w2 c5); intro k.
  repeat (autodimp k hyp); try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)
  rw <- eq1; clear eq1.

(*  exists (mkc_lam (cnewvar mkc_axiom) (mk_cv [cnewvar mkc_axiom] mkc_axiom)).*)
  rw @equality_in_function3; dands.

(*  apply inhabited_implies_tequality in eqinf.
  apply @tequality_function in eqinf; repnd; sp.*)
  rw @equality_in_function3 in eiw'5; repnd; auto.

  intros b1 b2 eib.

  assert (cover_vars Q (snoc s1a (w, mkc_apply f1 b1)))
         as cv1
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w, mkc_sup a1 f1)); sp;
             splst; sp).

  assert (cover_vars Q (snoc s1a (w, mkc_apply f1 b2)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w, mkc_sup a1 f1)); sp;
             splst; sp).

  assert (equality lib
            (lsubstc3 cp p1 ca a1 cb b1
                      (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
            (lsubstc3 cp p1 ca a1 cb b2
                      (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
            (lsubstc P wP s1a cvP))
         as eCs.
  (* begin proof of assert *)
  apply @equality_in_pw_v1 in eiw; exrepnd.
  generalize (eiw0 p1 p1 eiw'3); intro k; repnd.
  apply @equality_refl in eiw'4.
  generalize (k a1 a1 eiw'4); clear k; intro k; repnd.
  generalize (k b1 b2 eib); clear k; intro k; repnd.
  auto.
  (* end proof of assert *)

  assert (equality lib (mkc_apply f1 b1) (mkc_apply f1 b2)
                   (mkc_pw (lsubstc P wP s1a cvP) ap
                           (lsubstc_vars A wA (csub_filter s1a [ap]) [ap] cvA) bp ba
                           (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB) cp ca cb
                           (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC)
                           (lsubstc3 cp p1 ca a1 cb b1
                                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                                   [cp, ca, cb] cvC))))
         as eqaps.
  (* begin proof of assert *)
  apply @equality_refl in eiw'5.
  rw @equality_in_function3 in eiw'5; repnd.
  generalize (eiw'5 b1 b2 eib); clear eiw'5; intro eqw; repnd.
  rw @substc_mkc_pw_vs in eqw; try (complete sp).
  (* end proof of assert *)

  assert (similarity lib s1a s1a H) as simref by (allapply @similarity_refl; auto).

  generalize (ind b1 b2 eib
                  (lsubstc3 cp p1 ca a1 cb b2
                            (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
                  eCs
                  (mkc_apply f1 b2)
                  eqaps
                  s1a
                  simref
                  cv1 cv2 cvp); intro k; repnd.

  assert (mkc_apply
            (lsubstc Q w1 (snoc s1a (w, mkc_apply f1 b1)) cv1)
            (lsubstc3 cp p1 ca a1 cb b1
                      (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                    [cp, ca, cb] cvC))
          = substc b1 b
                   (lsubstc_vars
                      (mk_apply
                         (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                      w3
                      (csub_filter (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) [b])
                      [b]
                      c4)) as eq1.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, b1)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, b1)])
            (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                b1 b
                (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                          (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
                cvc w3 c4); intro eq.
  rw <- eq; clear eq.

  revert wfc cvc.
  rw @csubst_mk_apply.
  rw @fold_subst; introv.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b b1).
  introv eq.
  repeat (autodimp eq hyp).
  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_subst_pw_Q Q w f b b1).
  intro eq; repeat (autodimp eq hyp); try (complete (repeat (rw not_over_or in bc7); sp)).
  revert wfc cvc; rw eq; introv; clear eq.

  assert (!LIn f (free_vars (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b1)]))) as nifC1.
  (* - begin proof of assert *)
  intro j.
  generalize (eqvars_free_vars_disjoint
                C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b1)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in j.
  rw in_app_iff in j; rw in_remove_nvars in j; simpl in j.
  revert j; boolvar; simpl; allrw @free_vars_cterm; simpl; intro j; repdors; try (complete sp).
  (* - end proof of assert *)

  lsubst_tac.
  proof_irr; GC.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b1)])
                  w5 (snoc (snoc s1a (q, p1)) (a, a1)) c8
          = lsubstc3 cp p1 ca a1 cb b1
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubstc (subst Q w (mk_apply (mk_var f) (get_cterm b1))) w4
                  (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) c6
          = lsubstc Q w1 (snoc s1a (w, mkc_apply f1 b1)) cv1)
         as eq; try (complete (rw eq; auto)).

  assert (wf_term (mk_apply (mk_var f) (get_cterm b1))) as wa by (apply wf_apply; eauto with wf).

  assert (cover_vars (mk_apply (mk_var f) (get_cterm b1))
                     (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)))
         as ca1
         by (apply cover_vars_apply; sp;apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv j; splst in j; rw @dom_csub_app; splst; sp).

  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b1))
                w Q w4
                (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
                c6 wa ca1 w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq.
  rw eq.
  generalize (simple_substc2 (mkc_apply f1 b1) w Q s1a w1 cv1 c13).
  intro eq1.
  autodimp eq1 hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw <- eq1.

(*
  assert (cover_vars Q (snoc s1a (w, mkc_apply f1 b2)))
         as cv'
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w, mkc_apply f1 b1)); sp;
             splst; sp).
*)

  assert (mkc_apply
            (lsubstc Q w1 (snoc s1a (w, mkc_apply f1 b2)) cv2)
            (lsubstc3 cp p1 ca a1 cb b2
                      (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                    [cp, ca, cb] cvC))
          = substc b2 b
                   (lsubstc_vars
                      (mk_apply
                         (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                      w3
                      (csub_filter (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) [b])
                      [b]
                      c4)) as eq2.

  (* begin proof of assert *)
  assert (wf_term
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, b2)])) as wfc by (apply wf_term_csubst; sp).

  assert (cover_vars
            (csubst
               (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                         (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
               [(b, b2)])
            (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)))
    as cvc by (rw @cover_vars_csubst3; simpl; sp).

  generalize (simple_substc
                b2 b
                (mk_apply (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                          (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, mk_var b)]))
                wfc
                (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
                cvc w3 c4); intro eq.
  rw <- eq; clear eq.

  revert wfc cvc.
  rw @csubst_mk_apply.
  rw @fold_subst; introv.

  generalize (csubst_lsubst_pw_C_vars C cp ca cb q a b b2).
  introv eq.
  repeat (autodimp eq hyp).
  revert wfc cvc; rw eq; introv; clear eq.

  generalize (csubst_subst_pw_Q Q w f b b2).
  intro eq; repeat (autodimp eq hyp); try (complete (repeat (rw not_over_or in bc7); sp)).
  revert wfc cvc; rw eq; introv; clear eq.

  assert (!LIn f (free_vars (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b2)]))) as nifC1.
  (* - begin proof of assert *)
  intro j.
  generalize (eqvars_free_vars_disjoint
                C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b2)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in j.
  rw in_app_iff in j; rw in_remove_nvars in j; simpl in j.
  revert j; boolvar; simpl; allrw @free_vars_cterm; simpl; intro j; repdors; try (complete sp).
  (* - end proof of assert *)

  lsubst_tac.
  proof_irr; GC.

  assert (lsubstc (lsubst C [(cp, mk_var q), (ca, mk_var a), (cb, get_cterm b2)])
                  w5 (snoc (snoc s1a (q, p1)) (a, a1)) c8
          = lsubstc3 cp p1 ca a1 cb b2
                     (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb]) [cp, ca, cb] cvC))
    as eq; try (complete (rw eq; auto)).
  symmetry.
  apply lsubstc3_lsubstc_var1; try (complete sp);
  allapply @similarity_dom; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubstc (subst Q w (mk_apply (mk_var f) (get_cterm b2))) w4
                  (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) c6
          = lsubstc Q w1 (snoc s1a (w, mkc_apply f1 b2)) cv2)
         as eq; try (complete (rw eq; auto)).

  assert (wf_term (mk_apply (mk_var f) (get_cterm b2))) as wa by (apply wf_apply; eauto with wf).

  assert (cover_vars (mk_apply (mk_var f) (get_cterm b2))
                     (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)))
         as ca1
         by (apply cover_vars_apply; sp;apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv j; splst in j; rw @dom_csub_app; splst; sp).

  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b2))
                w Q w4
                (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
                c6 wa ca1 w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq.
  rw eq.
  generalize (simple_substc2 (mkc_apply f1 b2) w Q s1a w1 cv2 c13).
  intro eq'.
  autodimp eq' hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw <- eq2.

  clear eq1 eq2.


  dands; auto.

  generalize (cequivc_app_lam_axiom lib b1); intro ceq1.
  generalize (cequivc_app_lam_axiom lib b2); intro ceq2.

  apply @equality_respects_cequivc_left
        with (t1 := mkc_axiom);
    try (complete sp);
    try (complete (apply @cequivc_sym; sp)).

  apply @equality_respects_cequivc_right
        with (t2 := mkc_axiom);
    try (complete sp);
    try (complete (apply @cequivc_sym; sp)).


(*
  assert (equality b2 b2
                   (lsubstc2 bp p1 ba a1
                             (lsubstc_vars B wB (csub_filter s1a [bp, ba]) [bp, ba] cvB)))
         as eib2
         by (apply @equality_sym in eib; apply @equality_refl in eib; sp).

  generalize (ind b2 b2 eib2 cv' cv2); intro j; repnd.

  apply @tequality_trans
        with (t2 := mkc_apply (lsubstc Q w1 (snoc s2a (w, mkc_apply f2 b2)) cv2)
                              (lsubstc3 cp p2 ca a2 cb b2
                                        (lsubstc_vars C wC (csub_filter s1a [cp, ca, cb])
                                                      [cp, ca, cb] cvC)));
    auto; try (complete (apply @tequality_sym; auto)).

  assert (cequivc (mkc_apply (mkc_lam (cnewvar mkc_axiom)
                                      (mk_cv [cnewvar mkc_axiom] mkc_axiom))
                             b1) mkc_axiom)
         as ceq1
         by (generalize (cequivc_beta (cnewvar mkc_axiom) (mk_cv [cnewvar mkc_axiom] mkc_axiom) b1);
             intro ceq;
             rw @substc_cnewvar in ceq; sp).

  assert (cequivc (mkc_apply (mkc_lam (cnewvar mkc_axiom)
                                      (mk_cv [cnewvar mkc_axiom] mkc_axiom))
                             b2) mkc_axiom)
         as ceq2
         by (generalize (cequivc_beta (cnewvar mkc_axiom) (mk_cv [cnewvar mkc_axiom] mkc_axiom) b2);
             intro ceq;
             rw @substc_cnewvar in ceq; sp).

  apply @equality_respects_cequivc_left with (t1 := mkc_axiom);
    try (complete (apply @cequivc_sym; sp)).

  apply @equality_respects_cequivc_right with (t2 := mkc_axiom);
    try (complete (apply @cequivc_sym; sp)).

  sp.
*)


  (* now we can use hyp1 *)
  exrepnd.
  lsubst_tac.


  assert (lsubstc (lsubst Q [(w, mk_sup (mk_var a) (mk_var f))])
                  w2
                  (snoc (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) (v, lam_axiom))
                  c3
          = lsubstc Q w1 (snoc s1a (w, mkc_sup a1 f1)) c0)
         as eq1.

  (* begin proof of assert *)
  assert (wf_term (mk_sup (mk_var a) (@mk_var o f))) as wsup by (apply wf_sup; eauto with wf).

  assert (cover_vars (mk_sup (mk_var a) (mk_var f))
                     (snoc (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1))
                           (v, lam_axiom)))
         as cvsup
         by (apply cover_vars_sup; sp; apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter
               (snoc (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) (v, lam_axiom))
               [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).

  generalize (simple_lsubstc_subst
                (mk_sup (mk_var a) (mk_var f))
                w Q w2
                (snoc (snoc (snoc (snoc s1a (q, p1)) (a, a1)) (f, f1)) (v, lam_axiom))
                c3 wsup cvsup w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw disjoint_cons_l; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  unfold subst in eq; rw eq.
  generalize (simple_substc2 (mkc_sup a1 f1) w Q s1a w1 c0 c21).
  intro e.
  autodimp e hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw eq1 in hyp0; rw eq1 in hyp1; clear eq1.


  assert (cover_vars Q (snoc s2a (w, mkc_sup a3 f3)))
         as cv3
         by (apply cover_vars_change_sub with (sub1 := snoc s2a (w, t3)); sp;
             splst; sp).

  assert (lsubstc (lsubst Q [(w, mk_sup (mk_var a) (mk_var f))])
                  w2
                  (snoc (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3)) (v, lam_axiom))
                  c5
          = lsubstc Q w1 (snoc s2a (w, mkc_sup a3 f3)) cv3)
         as eq2.

  (* begin proof of assert *)
  assert (wf_term (mk_sup (mk_var a) (@mk_var o f))) as wsup by (apply wf_sup; eauto with wf).

  assert (cover_vars (mk_sup (mk_var a) (mk_var f))
                     (snoc (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3))
                           (v, lam_axiom)))
         as cvsup
         by (apply cover_vars_sup; sp; apply cover_vars_var; splst; sp).

  assert (cover_vars_upto
            Q
            (csub_filter
               (snoc (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3)) (v, lam_axiom))
               [w])
            [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t3)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s2a (w,t3)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).

  generalize (simple_lsubstc_subst
                (mk_sup (mk_var a) (mk_var f))
                w Q w2
                (snoc (snoc (snoc (snoc s2a (q, p3)) (a, a3)) (f, f3)) (v, lam_axiom))
                c5 wsup cvsup w1 cvuq).
  introv eq.
  autodimp eq hyp.
  simpl; rw disjoint_cons_l; rw disjoint_singleton_l; sp.
  lsubst_tac.
  lsubstc_snoc_vs.
  unfold subst in eq; rw eq.
  generalize (simple_substc2 (mkc_sup a3 f3) w Q s2a w1 cv3 c21).
  intro e.
  autodimp e hyp.
  allapply @similarity_dom; repnd; allrw; sp.
  (* end proof of assert *)

  rw eq2 in hyp0; clear eq2.

  sp.


  assert (cequivc lib (lsubstc Q w1 (snoc s2a (w, mkc_sup a3 f3)) cv3)
                  (lsubstc Q w1 (snoc s2a (w, t3)) c2))
         as ceq.
  (* begin proof of assert *)
  unfold cequivc; simpl.
  unfold csubst.
  apply @cequiv_lsubst.
  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; allapply @in_csub2sub; auto.
  introv k; clear hyp0; rw @cover_vars_eq in cv3;
    rw subvars_prop in cv3; apply cv3 in k;
    splst in k; splst; repdors; sp;
    revert k0; allapply @similarity_dom; repnd; allrw; sp.
  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; allapply @in_csub2sub; auto.
  introv k; clear hyp0; rw @cover_vars_eq in cv3;
    rw subvars_prop in cv3; apply cv3 in k;
    splst in k; splst; repdors; sp;
    revert k0; allapply @similarity_dom; repnd; allrw; sp.
  allrw @csub2sub_snoc.
  apply @cequiv_subst_snoc; sp.
  apply @cequiv_subst_csub2sub_refl.
  rw @fold_cequivc.
  apply @cequivc_sym.
  apply computes_to_valc_implies_cequivc; sp.
  (* end proof of assert *)

  apply @tequality_respects_cequivc_right
        with (T2 := mkc_apply (lsubstc Q w1 (snoc s2a (w, mkc_sup a3 f3)) cv3) p3);
    try (complete sp).
  apply sp_implies_cequivc_apply; sp.


  (* !! where is that coming from? *)
  try (apply iscvalue_mkc_sup).


  (* !! where is that coming from? *)
  simpl; sp.


  (* ---- Finally, we conclude *)
  introv sim; introv.
  dup sim1 as eiw.
  apply @equality_in_pw_v1 in eiw; exrepnd.

  generalize (eqh (snoc s2a (w,t2))); intro imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a s2a t1 t2 w0 p0; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply @tequality_mkc_pw in imp0; repnd.

  generalize (h (lsubstc p wp s1a0 cvp)
                (lsubstc p wp s1a0 cvp)
                t0 t3
                eiw3
                sim1
                (lsubstc p wp s2a0 c)
                imp0
                t3 sim1 s2a0 sim c1 c0 c).
  sp.
Qed.

(* begin hide *)

(* end hide *)