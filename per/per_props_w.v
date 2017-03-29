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

  Authors: Vincent Rahli

 *)


Require Export per_props_function.
Require Export list. (* WTF?? *)


Lemma equality_in_w {p} :
  forall lib (s1 s2 : @CTerm p) A v B,
    equality lib s1 s2 (mkc_w A v B)
    <=>
    {eqa : per
     , {eqb : (forall a a' : CTerm, forall e : eqa a a', per)
        , nuprl lib A A eqa
        # (forall a a' : CTerm,
           forall e : eqa a a',
             nuprl lib (substc a v B) (substc a' v B) (eqb a a' e))
        # weq lib eqa eqb s1 s2}}.
Proof.
  introv; sp_iff Case; introv e.

  - unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    allunfold @per_w; allunfold @type_family; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    exists eqa eqb; sp.
    allunfold @eq_term_equals; discover; sp.

  - exrepnd.
    exists (weq lib eqa eqb); sp.
    apply CL_w.
    exists eqa eqb; sp.
    exists A A v v B B; sp; spcast; computes_to_value_refl.
Qed.

(**

  Using the Coq induction principle we obtain for [weq], we can prove
  the following induction principle for our W types.  The then use
  this principle to prove the [rule_w_induction] rule below.

*)

Lemma w_ind_eq {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> CTerm -> [U]),
    (forall t1 t2 t3 t4, cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q t1 t2 -> Q t3 t4)
    -> (forall a1 a2 f1 f2,
          equality lib a1 a2 A
          -> equality lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1) (mkc_apply f2 b2))
          -> Q (mkc_sup a1 f1) (mkc_sup a2 f2))
    -> (forall w1 w2, equality lib w1 w2 (mkc_w A va B) -> Q w1 w2).
Proof.
  introv ceq ind e.
  rw @equality_in_w in e; exrepnd.
  induction e1; spcast.
  apply ceq with (t1 := mkc_sup a f) (t2 := mkc_sup a' f');
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa a' a')
         as e'
         by (eapply equality_eq_refl; eauto;
             eapply equality_eq_sym; eauto).

  apply ind; try (complete (exists eqa; sp)).

  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb a a' e); sp.
  generalize (e2 a a' e); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  introv eq.
  allrw @substc_cnewvar.
  exists (weq lib eqa eqb); sp.
  apply CL_w; unfold per_w; unfold type_family.
  exists eqa eqb; sp.
  exists A A va va B B; sp; spcast; apply computes_to_valc_refl; apply iscvalue_mkc_w.

  (* 3 *)
  introv eq.
  allrw @substc_cnewvar.
  rw @equality_in_w.
  exists eqa eqb; sp.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).

  (* 4 *)
  introv eq.
  apply_hyp; sp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).
Qed.

(* begin hide *)

Lemma w_ind_eq2 {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> [U]),
    (forall t1 t2, cequivc lib t1 t2 -> Q t1 -> Q t2)
    -> (forall a1 a2 f1 f2,
          equality lib a1 a2 A
          -> equality lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1))
          -> Q (mkc_sup a1 f1))
    -> (forall w1 w2, equality lib w1 w2 (mkc_w A va B) -> Q w1).
Proof.
  introv ceq ind e.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)).
  intro h.
  dest_imp h hyp.
  introv c1 c2 q1.
  apply ceq with (t1 := t1); sp.
  apply h with (w2 := w2); sp.
Qed.

Lemma w_ind {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> Prop),
    (forall t t', cequivc lib t t' -> Q t -> Q t')
    -> (forall a f,
          member lib a A
          -> member lib f (mkc_fun (substc a va B) (mkc_w A va B))
          -> Q (mkc_sup a f))
    -> (forall w, member lib w (mkc_w A va B) -> Q w).
Proof.
  introv ceq ind m.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)); intro i.
  apply i with (w2 := w); sp.
  apply ceq with (t := t1); sp.
  apply ind; allapply @equality_refl; sp.
Qed.

Lemma equality_in_pw {o} :
  forall lib (s1 s2 : @CTerm o) P ap A bp ba B cp ca cb C p,
    equality lib s1 s2 (mkc_pw P ap A bp ba B cp ca cb C p)
    <=>
    {eqp : per
     , {eqa : (forall p p' : CTerm, forall ep : eqp p p', per)
     , {eqb : (forall p p' : CTerm,
               forall ep : eqp p p',
               forall a a' : CTerm,
               forall ea : eqa p p' ep a a',
                 per)
        , nuprl lib P P eqp
        # (forall p p' : CTerm,
           forall ep : eqp p p',
             nuprl lib (substc p ap A) (substc p' ap A) (eqa p p' ep))
        # (forall p p' : CTerm,
           forall ep : eqp p p',
           forall a a' : CTerm,
           forall ea : eqa p p' ep a a',
             nuprl lib (lsubstc2 bp p ba a B)
                   (lsubstc2 bp p' ba a' B)
                   (eqb p p' ep a a' ea))
        # (forall p p',
           forall ep : eqp p p',
           forall a a',
           forall ea : eqa p p' ep a a',
           forall b b',
           forall eb : eqb p p' ep a a' ea b b',
             eqp (lsubstc3 cp p ca a cb b C)
                 (lsubstc3 cp p' ca a' cb b' C))
        # eqp p p
        # pweq lib eqp eqa eqb cp ca cb C p s1 s2}}}.
Proof.
  introv; sp_iff Case; introv e.

  - unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    allunfold @per_pw; allunfold @type_pfamily; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl o).
    exists eqp eqa eqb; sp.
    allunfold @eq_term_equals; discover; sp.

  - exrepnd.
    exists (pweq lib eqp eqa eqb cp ca cb C p); sp.
    apply CL_pw.
    exists eqp eqa eqb p p; sp.
    exists cp cp ca ca cb cb C C; sp.
    exists P P ap ap A A bp bp.
    exists ba ba B B; sp; spcast; computes_to_value_refl.
Qed.

Lemma isprog_vars_lsubstc3v3 {p} :
  forall v1 u1 v2 u2 v3 u3 (t : @CVTerm p [v1,v2,v3]),
    isprog_vars
      [u3]
      (lsubst (get_cvterm [v1;v2;v3] t)
              [(v1,get_cterm u1),(v2,get_cterm u2),(v3,mk_var u3)]).
Proof.
  introv.
  destruct_cterms.
  rw @isprog_vars_eq; simpl; dands.

  generalize (eqvars_free_vars_disjoint x1 [(v1, x0), (v2, x), (v3, mk_var u3)]);
    introv eqv.
  rw eqvars_prop in eqv.
  rw subvars_prop; introv k.
  rw in_single_iff.
  apply eqv in k; clear eqv.
  apply isprog_vars_eq in i1; repnd.
  rw in_app_iff in k; rw in_remove_nvars in k; repdors; repnd.

  simpl in k0; repeat (rw not_over_or in k0); repnd.
  rw subvars_prop in i2.
  apply i2 in k1; simpl in k1; sp.

  revert k; simpl; boolvar; simpl;
  allrw in_app_iff; allrw in_single_iff; allrw in_remove_nvar; repnd;
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl;
  intro k; repdors; try (complete sp).

  apply isprog_vars_eq in i1; repnd.
  apply lsubst_wf_iff; sp.
  unfold wf_sub, sub_range_sat; simpl; introv k; repdors; cpx;
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Definition lsubstc3v3 {p} (v1 : NVar) (u1 : @CTerm p)
                      (v2 : NVar) (u2 : CTerm)
                      (v3 : NVar) (u3 : NVar)
                      (t : CVTerm [v1;v2;v3]) : CVTerm [u3] :=
  exist (isprog_vars [u3])
        (lsubst (get_cvterm [v1;v2;v3] t)
                [(v1,get_cterm u1),(v2,get_cterm u2),(v3,mk_var u3)])
        (isprog_vars_lsubstc3v3 v1 u1 v2 u2 v3 u3 t).

Lemma lsubst_mk_pw {o} :
  forall (P : @NTerm o) ap A bp ba B cp ca cb C p sub,
    prog_sub sub
    -> isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp;ba] B
    -> isprog_vars [cp;ca;cb] C
    -> isprog_vars (dom_sub sub) p
    -> lsubst (mk_pw P ap A bp ba B cp ca cb C p) sub
       = mk_pw P ap A bp ba B cp ca cb C (lsubst p sub).
Proof.
  introv ps iP iA iB iC ip.
  change_to_lsubst_aux4.
  simpl.
  allrw @fold_nobnd.
  rw @fold_pw; simpl.
  allrw @sub_filter_nil_r.

  assert (lsubst_aux P sub = P) as eqP.
  apply lsubst_aux_trivial; introv i; discover; dands; try (complete sp).
  intro j.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  rw iP0 in j; sp.
  rw eqP.

  assert (lsubst_aux A (sub_filter sub [ap]) = A) as eqA.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iA; repnd.
  rw subvars_prop in iA0; apply iA0 in j; sp.
  rw eqA.

  assert (lsubst_aux B (sub_filter sub [bp,ba]) = B) as eqB.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iB; repnd.
  rw subvars_prop in iB0; apply iB0 in j; sp.
  rw eqB.

  assert (lsubst_aux C (sub_filter sub [cp,ca,cb]) = C) as eqC.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iC; repnd.
  rw subvars_prop in iC0; apply iC0 in j; sp.
  rw eqC.

  sp.
Qed.

Ltac cpx2 :=
  match goal with
    | [ H1 : closed ?x, H2 : LIn ?v (free_vars ?x) |- _ ] =>
        rewrite H1 in H2; simpl in H2; complete (destruct H2)
  end.

Lemma substc_mkc_pw_vs {o} :
  forall (p : @CTerm o) a b v P ap A bp ba B cp ca cb C,
    !LIn v (bound_vars (get_cvterm [cp;ca;cb] C))
    -> substc b v
              (mkc_pw_vs [v] P ap A bp ba B cp ca cb C
                         (lsubstc3v3 cp p ca a cb v C))
       = mkc_pw P ap A bp ba B cp ca cb C (lsubstc3 cp p ca a cb b C).
Proof.
  introv niv.
  destruct_cterms; simpl.
  apply cterm_eq; simpl.
  unfold csubst, subst; simpl.
  rw @lsubst_mk_pw;
    try (complete sp);
    try (complete (unfold prog_sub, sub_range_sat; simpl; sp; cpx; rw @isprogram_eq; sp)).

  rw @simple_lsubst_lsubst; simpl.

  assert (lsubst x2 [(v, x0)] = x2) as eq.
  rw @lsubst_trivial; allsimpl; try (complete sp); introv k; repdors; cpx.
  allrw @isprog_eq; dands; try (complete sp); allunfold @isprogram; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubst x1 [(v, x0)] = x1) as eq.
  rw @lsubst_trivial; allsimpl; try (complete sp); introv k; repdors; cpx.
  allrw @isprog_eq; dands; try (complete sp); allunfold @isprogram; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubst (mk_var v) [(v, x0)] = x0) as eq.
  change_to_lsubst_aux4; simpl; boolvar; sp.
  rw eq; clear eq.

  assert (lsubst x3 [(cp, x2), (ca, x1), (cb, x0), (v, x0)]
          = lsubst x3 [(cp, x2), (ca, x1), (cb, x0)]) as eq.
  clear niv.
  generalize (in_deq NVar deq_nvar v [cp,ca,cb]); intro k; destruct k as [k | k]; simpl in k.
  (* v in list *)
  assert ([(cp, x2), (ca, x1), (cb, x0), (v, x0)] = snoc [(cp, x2), (ca, x1), (cb, x0)] (v, x0)) as e by sp.
  rw e; clear e.
  rw @lsubst_snoc_dup; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; sp.
  allrw @isprog_eq; sp.
  (* v not in list *)
  allrw not_over_or; repnd.
  allrw @isprog_vars_eq; repnd.
  allrw subvars_prop; allsimpl.
  rw @simple_lsubst_trim.
  symmetry.
  rw @simple_lsubst_trim.
  simpl; boolvar; try (complete sp); discover; repdors; try subst; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl; try (complete sp).
  rw eq; sp.

  introv k; repdors; cpx; try (complete sp);
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; sp; simpl.
  rw disjoint_singleton_l.
  exact niv.

  introv k; repdors; cpx; try (complete sp); allrw @isprog_eq; sp.

  clear niv; simpl; rw @isprog_vars_eq; simpl; sp.

  rw @isprog_vars_eq in i3; repnd.
  rw subvars_prop in i6.
  generalize (eqvars_free_vars_disjoint x3 [(cp, x2), (ca, x1), (cb, mk_var v)]); intro eqv.
  rw subvars_prop; introv j; rw eqvars_prop in eqv; apply eqv in j.
  rw in_single_iff.
  rw in_app_iff in j; rw in_remove_nvars in j; repdors; repnd.
  simpl in j0; repeat (rw not_over_or in j0); repnd; discover; allsimpl; sp.
  apply in_sub_free_vars in j; exrepnd.
  revert j0; simpl; boolvar; simpl; introv k; repdors; cpx;
  allrw @isprog_eq; allunfold @isprogram; repnd; try cpx2.

  allrw @isprog_eq; allrw @isprog_vars_eq; allunfold @isprogram; repnd.
  apply lsubst_wf_iff; sp.
  unfold wf_sub, sub_range_sat; simpl; introv k; repdors; cpx.
Qed.

Lemma param_w_ind {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> [U]),
    (forall p t1 t2 t3 t4, cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p t1 t2 -> Q p t3 t4)
    -> (forall p a1 a2 f1 f2 vb,
       equality lib a1 a2 (substc p ap A)
       -> equality lib f1 f2 (mkc_function
                            (lsubstc2 bp p ba a1 B)
                            vb
                            (mkc_pw_vs [vb]
                                       P ap A bp ba B cp ca cb C
                                       (lsubstc3v3 cp p ca a1 cb vb C)))
       -> (forall b1 b2,
             equality lib b1 b2 (lsubstc2 bp p ba a1 B)
             -> Q (lsubstc3 cp p ca a1 cb b1 C)
                  (mkc_apply f1 b1)
                  (mkc_apply f2 b2))
       -> Q p
            (mkc_sup a1 f1)
            (mkc_sup a2 f2))
    -> (forall p w1 w2,
          equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p)
          -> Q p w1 w2).
Proof.
  introv ceq ind e.
  apply equality_in_pw in e; exrepnd.
  induction e0; spcast.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (apply (nuprl_uniquely_valued lib) with (t := lsubstc2 bp p ba a1 B); sp;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (apply (nuprl_uniquely_valued lib) with (t := lsubstc2 bp p ba a1 B); sp;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.
Qed.

(* Not as useful as 3 because we don't have any constraint on vb *)
Lemma param_w_ind2 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]),
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
       equality lib p1 p2 P
       -> equality lib a1 a2 (substc p1 ap A)
       -> equality lib f1 f2 (mkc_function
                            (lsubstc2 bp p1 ba a1 B)
                            vb
                            (mkc_pw_vs [vb]
                                       P ap A bp ba B cp ca cb C
                                       (lsubstc3v3 cp p1 ca a1 cb vb C)))
       -> (forall b1 b2,
             equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
             -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                  (lsubstc3 cp p2 ca a2 cb b2 C)
                  (mkc_apply f1 b1)
                  (mkc_apply f2 b2))
       -> Q p1
            p2
            (mkc_sup a1 f1)
            (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             eapply equality_eq_sym; eauto).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* This version is the most useful one so far *)
Lemma param_w_ind3 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]),
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (lsubstc3 cp p2 ca a2 cb b2 C)
                     (mkc_apply f1 b1)
                     (mkc_apply f2 b2))
          -> Q p1
               p2
               (mkc_sup a1 f1)
               (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* slightly better than 3 because we can provide a list of variables that
 * v has to be disjoint with *)
Lemma param_w_ind4 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]) vs,
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb vs
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (lsubstc3 cp p2 ca a2 cb b2 C)
                     (mkc_apply f1 b1)
                     (mkc_apply f2 b2))
          -> Q p1
               p2
               (mkc_sup a1 f1)
               (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C) ++ vs)})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C) ++ vs));
             apply fresh_var_not_in); exrepnd.

  allrw in_app_iff.

  apply ind with (vb := v);
    try (complete sp);
    try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* Useless *)
Lemma param_w_ind5 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> [U]),
    (forall p t1 t2,
       cequivc lib t1 t2 -> Q p t1 -> Q p t2)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> equality lib p1 p2 P
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (mkc_apply f1 b1))
          -> Q p1
               (mkc_sup a1 f1))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 w1).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0 as [ p t1 t2 ep a1 f1 a2 f2 ea c1 c2 i r ]; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v) (p2 := p2) (a2 := a2) (f2 := f2);
    try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eib eip.
  apply r with (b2 := b') (p2 := lsubstc3 cp p2 ca a2 cb b' C).
  unfold equality in eib; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eib; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eib; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

Lemma weq_implies {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> forall t1 t2,
         weq lib eqa1 eqb1 t1 t2
         -> weq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqia eqib weq1.
  induction weq1.

  assert (eqa2 a a') as ea2 by (allrw <-; sp).

  apply @weq_cons
        with
        (a  := a)
        (f  := f)
        (a' := a')
        (f' := f')
        (e  := ea2);
    try (complete sp).

  introv eia.

  apply_hyp.
  generalize (eqib a a' e ea2); intro eqt; allrw; sp.
Qed.

Lemma eq_term_equals_weq {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> eq_term_equals (weq lib eqa1 eqb1)
                      (weq lib eqa2 eqb2).
Proof.
  introv eqia eqib.
  unfold eq_term_equals; introv; split; intro k.
  apply @weq_implies with (eqa1 := eqa1) (eqb1 := eqb1); sp.

  apply @weq_implies with (eqa1 := eqa2) (eqb1 := eqb2); sp;
  apply eq_term_equals_sym; sp.
Qed.

Lemma equality_in_w_v1 {p} :
  forall lib A v B (t1 t2 : @CTerm p),
    equality lib t1 t2 (mkc_w A v B)
    <=> {a1, a2, f1, f2 : CTerm
         , t1 ===>(lib) (mkc_sup a1 f1)
         # t2 ===>(lib) (mkc_sup a2 f2)
         # equality lib a1 a2 A
         # equality lib f1 f2 (mkc_fun (substc a1 v B) (mkc_w A v B))
         # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))}.
Proof.
  introv; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    destruct h.
    exists a a' f f'; sp.
    exists eqa; sp.
    rw <- @fold_mkc_fun.
    rw @equality_in_function; dands.

    exists (eqb a a' e).
    apply @nuprl_refl with (t2 := substc a' v0 B0); sp.

    intros b1 b2 eib.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover.
    allrw @substc_cnewvar.
    exists eq; sp.

    intros b1 b2 eib.
    allrw @substc_cnewvar.
    exists eq; sp.
    allrw.
    apply_hyp.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover; sp.

    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib A0 eq0 eqa); introv k; repeat (dest_imp k hyp).
    assert (eqa a0 a'0) as ea by (allrw <-; sp).
    exists (eqb a0 a'0 ea); sp.

  - exrepnd.
    unfold equality in e3; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A v B v B e1); intro n; exrepnd.

    exists (weq lib eqa (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3))); dands.

    apply CL_w; unfold per_w.
    exists eqa.
    exists (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3)); sp.
    unfold type_family.
    fold (@nuprl p lib).
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).

    apply @weq_cons with (a := a1) (f := f1) (a' := a2) (f' := f2) (e := e5); sp.
    generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); intro n.
    rw <- @fold_mkc_fun in e4.
    rw @equality_in_function in e4; repnd.
    generalize (e4 b b'); intro k.
    dest_imp k hyp.
    exists (f a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); sp.
    allapply @nuprl_refl; sp.
    allrw @substc_cnewvar.
    unfold equality in k; exrepnd.
    inversion k1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd; allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.

    assert (eq_term_equals eqa0 eqa)
           as eqta by (eapply nuprl_uniquely_valued; eauto).

    assert (forall (a a' : CTerm) (ea : eqa a a') (ea' : eqa0 a a'),
              eq_term_equals (f a a' (eq_equality1 lib a a' A0 eqa ea e3)) (eqb a a' ea'))
           as eqtb.
    introv.
    generalize (n0 a a' (eq_equality1 lib a a' A0 eqa ea e3)); intro n1.
    assert (nuprl lib (substc a v0 B0) (substc a' v0 B0) (eqb a a' ea')) as n2 by sp.
    apply (nuprl_uniquely_valued lib) with (t := substc a v0 B0); sp; allapply @nuprl_refl; sp.
    apply weq_implies with (eqa1 := eqa0) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.
Qed.

Lemma tequality_mkc_w {p} :
  forall lib (A1 : @CTerm p) v1 B1
         A2 v2 B2,
    tequality lib
      (mkc_w A1 v1 B1)
      (mkc_w A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # (forall a1 a2,
        equality lib a1 a2 A1
        -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))).
Proof.
  introv; split; intro e; repnd.

  - unfold tequality in e; exrepnd.
    unfold nuprl in e0.
    inversion e0; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd; spcast; allfold (@nuprl p lib).
    computes_to_value_isvalue.
    dands.

    + allapply @tequality_if_nuprl; sp.

    + introv eia.
      generalize (equality_eq1 lib A A' a1 a2 eqa); intro i; dest_imp i hyp.
      rw <- i in eia.
      exists (eqb a1 a2 eia); sp.

  - unfold tequality.
    unfold tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_teq1 lib A1 eqa v1 B1 v2 B2); intro neqb.
    dest_imp neqb hyp; try (complete (allapply @nuprl_refl; sp)).
    dest_imp neqb hyp; exrepnd.
    rename f into eqb.

    exists (weq lib eqa eqb).
    apply CL_w; unfold per_w.
    exists eqa eqb; sp.
    unfold type_family.
    exists A1 A2 v1 v2 B1 B2; dands;
    try (complete sp);
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).
Qed.
