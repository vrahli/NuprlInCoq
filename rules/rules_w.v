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
Require Export per_props_equality.
Require Import per_props_w.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


Lemma equality_w_in_uni {o} :
  forall lib A1 v1 B1
         A2 v2 B2
         i,
    @equality o
      lib (mkc_w A1 v1 B1)
      (mkc_w A2 v2 B2)
      (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # (forall a1 a2,
        equality lib a1 a2 A1
        -> equality lib (substc a1 v1 B1) (substc a2 v2 B2) (mkc_uni i))).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality, nuprl in teq; exrepnd.
    inversion teq1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue; GC.
    dands.

    exists eq; sp.
    allrw.
    exists eqa; sp.

    introv e.
    exists eq; sp.
    allfold (@nuprli o lib j0).
    allrw.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp);
      try (complete (apply @nuprli_implies_nuprl with (i := j0); sp;
                     allapply @nuprli_refl; sp)).
    rw <- k in e0.
    generalize (tsb a1 a2 e0); intro n.
    exists (feqb a1 a2 e0); sp.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli o lib j0).

    exists eq; sp.
    allrw.

    generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

    exists (weq lib eqa
                (fun (a1 a2 : CTerm) (e : eqa a1 a2) =>
                   f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0))).
    unfold nuprli.
    apply CL_w; fold (@nuprli o lib j0).
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).
Qed.




(* end hide *)

(**

  We now prove the truth of several rules about the W type.  These are
  the standard elimination and introduction rules for W types.  For
  the elimination (or induction) rule we only deal with goals that
  have a trivial extract ([mk_axiom]) as it is the case for equality
  types.  Therefore, this rule can be used to prove memberships.

*)


(* [19] ============ W INDUCTION ============ *)

(**

  The W induction rule can be stated as follows:
<<
   H, w : W(A;v.B) |- Q ext Ax

     By Winduction a f z b

     H, a : A
        f : B(a) -> W(A;v.B)
        z : b:B(a) -> Q[w\f(b)]
      |- Q[w\sup(a,f)] ext Ax
>>
 *)

Definition rule_w_induction {o}
             (H : @barehypotheses o)
             (Q A B : NTerm)
             (v w a f z b : NVar) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp w (mk_w A v B)))
       (mk_conclax Q))
    [ mk_baresequent
        (snoc (snoc (snoc H (mk_hyp a A))
                    (mk_hyp f (mk_function
                                 (lsubst B [(v,mk_var a)])
                                 b
                                 (mk_w A v B))))
              (mk_hyp z (mk_function
                           (lsubst B [(v,mk_var a)])
                           b
                           (lsubst Q [(w,mk_apply (mk_var f) (mk_var b))]))))
        (mk_conclax (lsubst Q [(w,mk_sup (mk_var a) (mk_var f))]))
    ]
    [sarg_var a, sarg_var f, sarg_var z, sarg_var b].

Lemma rule_w_induction_true {o} :
  forall (lib : library)
         (H : @barehypotheses o)
         (Q A B : NTerm)
         (v w a f z b : NVar)
         (bc1 : !LIn b (w :: a :: f :: z :: v :: vars_hyps H))
         (bc2 : !LIn w [a,f,z])
         (bc3 : !LIn a (bound_vars B))
         (bc4 : !LIn b (bound_vars Q))
         (bc5 : !LIn f (bound_vars Q))
         (bc6 : !LIn a (bound_vars Q)),
    rule_true lib (rule_w_induction H Q A B v w a f z b).
Proof.
  unfold rule_w_induction, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc
                         (snoc (snoc H (mk_hyp a A))
                               (mk_hyp f (mk_function (lsubst B [(v, mk_var a)]) b (mk_w A v B))))
                         (mk_hyp z
                                 (mk_function (lsubst B [(v, mk_var a)]) b
                                              (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]))))
                      (mk_conclax (lsubst Q [(w, mk_sup (mk_var a) (mk_var f))])))
                   (inl eq_refl));
    simpl; intros hyp1; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hyp w (mk_w A v B))))).

  (* We prove some simple facts on our sequents *)
  assert (!(f = a)
          # !(z = a)
          # !(z = f)
          # !(b = w)
          # !(b = a)
          # !(b = f)
          # !(b = z)
          # !(b = v)
          # !LIn b (free_vars A)
          # !LIn a (free_vars A)
          # !LIn f (free_vars A)
          # !LIn z (free_vars A)
          # (b <> v -> !LIn b (free_vars B))
          # (a <> v -> !LIn a (free_vars B))
          # (f <> v -> !LIn f (free_vars B))
          # (z <> v -> !LIn z (free_vars B))
          # !LIn b (free_vars Q)
          # !LIn a (free_vars Q)
          # !LIn f (free_vars Q)
          # !LIn z (free_vars Q)
          # !LIn b (vars_hyps H)
          # !LIn w (vars_hyps H)
          # !LIn a (vars_hyps H)
          # !LIn f (vars_hyps H)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (assert (LIn a (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp));
    try (complete (assert (LIn f (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp));
    try (complete (assert (LIn z (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp));
    try (complete (assert (LIn b (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp));
    try (complete (discover; allrw in_snoc; sp)).

  destruct vhyps as [ nefa vhyps ].
  destruct vhyps as [ neza vhyps ].
  destruct vhyps as [ nezf vhyps ].
  destruct vhyps as [ nebw vhyps ].
  destruct vhyps as [ neba vhyps ].
  destruct vhyps as [ nebf vhyps ].
  destruct vhyps as [ nebz vhyps ].
  destruct vhyps as [ nebv vhyps ].
  destruct vhyps as [ nibA vhyps ].
  destruct vhyps as [ niaA vhyps ].
  destruct vhyps as [ nifA vhyps ].
  destruct vhyps as [ nizA vhyps ].
  destruct vhyps as [ nibB vhyps ].
  destruct vhyps as [ niaB vhyps ].
  destruct vhyps as [ nifB vhyps ].
  destruct vhyps as [ nizB vhyps ].
  destruct vhyps as [ nibQ vhyps ].
  destruct vhyps as [ niaQ vhyps ].
  destruct vhyps as [ nifQ vhyps ].
  destruct vhyps as [ nizQ vhyps ].
  destruct vhyps as [ nibH vhyps ].
  destruct vhyps as [ niwH vhyps ].
  destruct vhyps as [ niaH vhyps ].
  destruct vhyps as [ nifH nizH ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_snoc in sim; exrepnd; subst; allsimpl.
  lsubst_tac.
  rw @member_eq.
  clear pt1 pt2.

  revert_dependents s2a.

  (* we use w_ind_eq *)
  generalize (w_ind_eq
                lib (lsubstc A w1 s1a c1)
                v
                (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)
                (fun t1 t2 =>
                   forall t3,
                     equality lib t1 t3
                              (mkc_w (lsubstc A w1 s1a c1) v
                                     (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2))
                     -> forall s2a,
                          similarity lib s1a s2a H
                          -> forall (c1 : cover_vars Q (snoc s1a (w, t1)))
                                    (c0 : cover_vars Q (snoc s2a (w, t3))),
                               tequality lib
                                 (lsubstc Q wfct (snoc s1a (w, t1)) c1)
                                 (lsubstc Q wfct (snoc s2a (w, t3)) c0)
                                 # member lib mkc_axiom
                                 (lsubstc Q wfct (snoc s1a (w, t1)) c1)));
    intros h.


  (* ---- we prove that Q preserves cequivc *)
  autodimp h hyp.
  introv ceq1 ceq2 teq eiw sim; introv.

  assert (equality lib t0 t6
                   (mkc_w (lsubstc A w1 s1a c1) v
                          (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)))
         as eiw2
         by (apply @equality_respects_cequivc_left with (t1 := t4); auto;
             apply cequivc_sym; auto).

  assert (cover_vars Q (snoc s1a (w, t0)))
         as cov0
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w,t4)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  generalize (teq t6 eiw2 s2a sim cov0 c3); clear teq; intro teq; repnd.

  assert (cequivc lib
            (lsubstc Q wfct (snoc s1a (w, t0)) cov0)
            (lsubstc Q wfct (snoc s1a (w, t4)) c0))
         as cequiv1.
  (* begin proof of assert *)
  unfold cequivc; simpl.
  unfold csubst.
  allrw @csub2sub_snoc.
  apply cequiv_lsubst.

  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; inj; allapply @in_csub2sub; auto.
  introv k; rw @cover_vars_eq in c0; rw subvars_prop in c0; apply c0 in k.
  splst in k; splst; sp.

  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; apply in_snoc in k; repdors; inj; allapply @in_csub2sub; auto.
  introv k; rw @cover_vars_eq in c0; rw subvars_prop in c0; apply c0 in k.
  splst in k; splst; sp.

  apply cequiv_subst_snoc; sp.
  apply cequiv_subst_csub2sub_refl.
  (* end proof of assert *)

  dands.

  apply tequality_respects_cequivc_left
        with (T1 := lsubstc Q wfct (snoc s1a (w, t0)) cov0);
    try (complete sp).

  apply @cequivc_preserving_equality
        with (A := lsubstc Q wfct (snoc s1a (w, t0)) cov0);
    try (complete sp).



  (* ---- The we prove the induction rule *)
  autodimp h hyp.

  introv eia eif ind eiw sim; introv.

  applydup @equality_in_w_v1 in eiw as eiw'; exrepnd.
  spcast.
  apply computes_to_valc_isvalue_eq in eiw'0.
  symmetry in eiw'0; apply mkc_sup_eq in eiw'0; repnd; subst.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc (snoc (snoc s1a (a, a1)) (f, f1)) (z, lam_axiom))
                   (snoc (snoc (snoc s2a (a, a3)) (f, f3)) (z, lam_axiom)));
    clear hyp1; intro hyp1.


  (* -- First we prove the hyps_functionality part *)
  autodimp hyp1 hyp.
  introv sim'.
  rw @similarity_snoc in sim';  simpl in sim';  exrepnd; cpx.
  rw @similarity_snoc in sim'3; simpl in sim'3; exrepnd; cpx.
  rw @similarity_snoc in sim'4; simpl in sim'4; exrepnd; cpx.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (cover_vars
            (mk_function (lsubst B [(v, mk_var a)]) b
                         (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]))
            (snoc (snoc s2a0 (a, t7)) (f, t5)))
         as cov2
         by (apply cover_vars_change_sub with (sub1 := snoc (snoc s1a0 (a, t6)) (f, t0)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc s1a0 (a, t6)) (f, t0))
         (snoc (snoc s2a0 (a, t7)) (f, t5))
         (@lam_axiom o)
         t4 w3 p0 cov2; sp.

  assert (cover_vars (mk_function (lsubst B [(v, mk_var a)]) b (mk_w A v B))
                     (snoc s2a0 (a, t7)))
         as cov3
         by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (a, t6)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a0 (a, t6))
         (snoc s2a0 (a, t7))
         t0 t5 w4 p1 cov3; sp.

  assert (cover_vars A s2a0)
         as cov4
         by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a0 s2a0 t6 t7 w1 p2 cov4; sp.

  apply @hyps_functionality_init_seg_snoc2 with (t' := t2) (w := w0) (c := p) in eqh; sp.
  lsubst_tac; sp.

  (* we prove the tequality of the 'a' part *)
  generalize (eqh (snoc s2a0 (w,t2))); introv imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w0 p; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_w in imp0; repnd; auto.

  (* we prove the tequality of the 'f' part *)
  lsubst_tac.
  rw @tequality_function; dands.

  (* we prove that the domain is functional *)
  generalize (eqh (snoc s2a0 (w,t2))); introv imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w0 p; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_w in imp0; repnd; auto.
  generalize (imp0 t6 t7); clear imp0; intro teqb.
  autodimp teqb hyp.

  revert_dependents w6.
  revert_dependents c1.
  revert_dependents c7.
  revert_dependents c4.
  repeat (rw @fold_subst); introv e1 e2.

  assert (lsubstc (subst B v (mk_var a)) w6 (snoc s1a (a, t6)) c1
          = substc t6 v (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.

  assert (lsubstc (subst B v (mk_var a)) w6 (snoc s2a1 (a, t7)) c7
          = substc t7 v (lsubstc_vars B w2 (csub_filter s2a1 [v]) [v] c10)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.
  auto.

  (* we prove that the co-domain is functional *)
  intros b1 b2 eib.

  generalize (eqh (snoc s2a0 (w,t2))); introv imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w0 p; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  lsubstc_snoc_vs.

  assert (cover_vars (mk_w A v B) (snoc (snoc s1a (a, t6)) (b, b1)))
         as cv1
         by (apply cover_vars_change_sub2 with (sub1 := s1a); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp;
             rw subvars_prop; sp; splst; sp).

  assert (cover_vars (mk_w A v B) (snoc (snoc s2a1 (a, t7)) (b, b2)))
         as cv2
         by (apply cover_vars_change_sub2 with (sub1 := s1a); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp;
             rw subvars_prop; sp; splst; sp).

  generalize (simple_substc2 b1 b (mk_w A v B) (snoc s1a (a, t6)) w0 cv1 c6);
    intro e1; dest_imp e1 hyp;
    try (complete (splst; allapply @similarity_dom; repnd; allrw; sp)).
  rw <- e1; clear e1.

  generalize (simple_substc2 b2 b (mk_w A v B) (snoc s2a1 (a, t7)) w0 cv2 c8);
    intro e2; dest_imp e2 hyp;
    try (complete (splst; allapply @similarity_dom; repnd; allrw; sp)).
  rw <- e2; clear e2.

  lsubst_tac.
  lsubstc_snoc_vs.
  auto.


  (* we prove the tequality of the 'v' part *)
  (* we prove the following to allow lsubst_tac to make progress *)
  assert (!LIn f (free_vars (lsubst B [(v, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint B [(v, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors;
  try (rw not_over_or in k0); repnd;
  try (complete sp);
  try (complete (apply nifB in k1; sp)).
  (* end proof of assert *)

  lsubst_tac.
  rw @tequality_function; dands.

  (* we prove that the domain is functional *)
  generalize (eqh (snoc s2a0 (w,t2))); introv imp.
  autodimp imp hyp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w0 p; sp.
  lsubst_tac; sp.
  rw @eq_hyps_snoc in imp; simpl in imp; exrepnd; cpx.
  lsubst_tac.
  apply tequality_mkc_w in imp0; repnd; auto.
  generalize (imp0 t6 t7); clear imp0; intro teqb.
  autodimp teqb hyp.

  revert_dependents w6.
  revert_dependents c1.
  revert_dependents c.
  rw @fold_subst; introv e1 e2.

  assert (lsubstc (subst B v (mk_var a)) w6 (snoc s1a (a, t6)) c1
          = substc t6 v (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.

  assert (lsubstc (subst B v (mk_var a)) w6 (snoc s2a1 (a, t7)) c
          = substc t7 v (lsubstc_vars B w2 (csub_filter s2a1 [v]) [v] c10)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.
  auto.

  (* we prove that the co-domain is functional *)
  intros b1 b2 eib.

  revert_dependents w6.
  revert_dependents c1.
  rw @fold_subst; introv e1 e2 eib.

  assert (lsubstc (subst B v (mk_var a)) w6 (snoc s1a0 (a, t6)) c1
          = substc t6 v (lsubstc_vars B w2 (csub_filter s1a0 [v]) [v] c2)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  duplicate eib as eib1.
  rw eq in eib; clear eq.

  assert (equality lib (mkc_apply t0 b1) (mkc_apply t5 b2)
                   (mkc_w (lsubstc A w1 s1a0 p2) v
                          (lsubstc_vars B w2 (csub_filter s1a0 [v]) [v] c2)))
         as eap. (* from e1 *)
  (* begin proof of assert *)
  rw @equality_in_function in e1; repnd.
  generalize (e1 b1 b2 eib1); intro eq.

  assert (cover_vars (mk_w A v B) (snoc (snoc s1a0 (a, t6)) (b, b1)))
         as cv1
         by (apply cover_vars_change_sub2 with (sub1 := s1a0); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp;
             rw subvars_prop; sp; splst; sp).

  generalize (simple_substc2 b1 b (mk_w A v B) (snoc s1a0 (a, t6)) w0 cv1 c6);
    intro eq1; dest_imp eq1 hyp;
    try (complete (splst; allapply @similarity_dom; repnd; allrw; sp)).
  rw <- eq1 in eq; clear eq1.

  lsubst_tac.
  lsubstc_snoc_vs.
  auto.
  (* end proof of assert *)

  assert (cover_vars Q (snoc s1a0 (w, mkc_apply t0 b1)))
         as cv1
         by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (w, mkc_sup t6 t0)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  assert (cover_vars Q (snoc s2a0 (w, mkc_apply t5 b2)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a0 (w, mkc_sup t6 t0)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  generalize (ind b1 b2 eib (mkc_apply t5 b2) eap s2a0 sim'5 cv1 cv2); intro teq; repnd.

  assert (substc b1 b
                 (lsubstc_vars (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) w7
                               (csub_filter (snoc (snoc s1a0 (a, t6)) (f, t0)) [b])
                               [b] c5)
          = lsubstc Q wfct (snoc s1a0 (w, mkc_apply t0 b1)) cv1)
         as eq1.
  (* begin proof of assert *)
  assert (wf_term (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b1)]))
         as wfsub by (apply wf_term_csubst; sp).
  assert (cover_vars
            (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b1)])
            (snoc (snoc s1a0 (a, t6)) (f, t0)))
         as cvsub by (rw @cover_vars_csubst3; simpl; sp).
  generalize (simple_substc
                b1 b (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                wfsub (snoc (snoc s1a0 (a, t6)) (f, t0)) cvsub w7 c5);
    intro eq1; rw <- eq1; clear eq1.
  revert_dependents wfsub.
  revert_dependents cvsub.
  rw @fold_subst.
  generalize (csubst_subst_pw_Q Q w f b b1); intro eq1; repeat (dest_imp eq1 hyp).
  rw eq1; introv; clear eq1.
  assert (wf_term (mk_apply (mk_var f) (get_cterm b1)))
         as wfap by (apply wf_apply_iff; sp; eauto with wf).
  assert (cover_vars (mk_apply (mk_var f) (get_cterm b1))
                     (snoc (snoc s1a0 (a, t6)) (f, t0)))
         as ca1 by (apply cover_vars_apply; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s1a0 (a, t6)) (f, t0)) [w]) [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,mkc_apply t0 b1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a0 (w,mkc_apply t0 b1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).
  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b1)) w Q wfsub
                (snoc (snoc s1a0 (a, t6)) (f, t0)) cvsub wfap ca1 wfct cvuq);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq1.
  rw eq1; clear eq1.
  generalize (simple_substc2 (mkc_apply t0 b1) w Q s1a0 wfct cv1 c12);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq1; clear eq1.

  assert (substc b2 b
                 (lsubstc_vars (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) w7
                               (csub_filter (snoc (snoc s2a0 (a, t7)) (f, t5)) [b])
                               [b] c8)
          = lsubstc Q wfct (snoc s2a0 (w, mkc_apply t5 b2)) cv2)
         as eq2.
  (* begin proof of assert *)
  assert (wf_term (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b2)]))
         as wfsub by (apply wf_term_csubst; sp).
  assert (cover_vars
            (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b2)])
            (snoc (snoc s2a0 (a, t7)) (f, t5)))
         as cvsub by (rw @cover_vars_csubst3; simpl; sp).
  generalize (simple_substc
                b2 b (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                wfsub (snoc (snoc s2a0 (a, t7)) (f, t5)) cvsub w7 c8);
    intro eq1; rw <- eq1; clear eq1.
  revert_dependents wfsub.
  revert_dependents cvsub.
  rw @fold_subst.
  generalize (csubst_subst_pw_Q Q w f b b2); intro eq1; repeat (dest_imp eq1 hyp).
  rw eq1; introv; clear eq1.
  assert (wf_term (mk_apply (mk_var f) (get_cterm b2)))
         as wfap by (apply wf_apply_iff; sp; eauto with wf).
  assert (cover_vars (mk_apply (mk_var f) (get_cterm b2))
                     (snoc (snoc s2a0 (a, t7)) (f, t5)))
         as ca1 by (apply cover_vars_apply; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s2a0 (a, t7)) (f, t5)) [w]) [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,mkc_apply t5 b2)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s2a0 (w,mkc_apply t5 b2)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).
  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b2)) w Q wfsub
                (snoc (snoc s2a0 (a, t7)) (f, t5)) cvsub wfap ca1 wfct cvuq);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq1.
  rw eq1; clear eq1.
  generalize (simple_substc2 (mkc_apply t5 b2) w Q s2a0 wfct cv2 c12);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq2; clear eq2.
  auto.


  (* -- Then we prove the similarity part *)
  autodimp hyp1 hyp.

  assert (wf_term
            (mk_function (lsubst B [(v, mk_var a)]) b
                         (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])))
         as wff.
  (* begin proof of assert *)
  apply wf_function_iff; dands.
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  apply lsubst_preserves_wf_term; sp;
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  (* end proof of assert*)

  assert (cover_vars
            (mk_function (lsubst B [(v, mk_var a)]) b
                         (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]))
            (snoc (snoc s1a (a, a1)) (f, f1)))
         as cvf.
  (* begin proof of assert *)
  apply cover_vars_function; dands.
  apply cover_vars_lsubst_if; simpl.
  dup c2 as cvB.
  unfold cover_vars_upto in cvB.
  prove_subvars cvB; allsimpl.
  splst; splst in x; sp.
  introv k; sp; cpx.
  apply cover_vars_var; repeat (rw @dom_csub_snoc); repeat (rw in_snoc); sp.
  apply cover_vars_upto_lsubst_if; simpl.
  dup pC1 as cvQ.
  rw @cover_vars_eq in cvQ.
  prove_subvars cvQ.
  splst; splst in x; sp.
  destruct (eq_var_dec b v0); sp; right; right; sp.
  introv j; sp; cpx.
  apply cover_vars_upto_apply; sp.
  apply cover_vars_upto_var; simpl.
  splst.
  destruct (eq_var_dec b f); sp; right; sp.
  apply cover_vars_upto_var; simpl; sp.
  (* end proof of assert*)

  rw @similarity_snoc; simpl.
  exists (snoc (snoc s1a (a, a1)) (f, f1))
         (snoc (snoc s2a (a, a3)) (f, f3))
         (@lam_axiom o) (@lam_axiom o)
         wff cvf; sp.

  assert (wf_term (mk_function (lsubst B [(v, mk_var a)]) b (mk_w A v B)))
         as wff2.
  (* begin proof of assert *)
  apply wf_function_iff; dands.
  apply lsubst_preserves_wf_term; sp.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; try (rw @nt_wf_eq; sp).
  rw <- @wf_w_iff; sp.
  (* end proof of assert*)

  assert (cover_vars (mk_function (lsubst B [(v, mk_var a)]) b (mk_w A v B))
                     (snoc s1a (a, a1)))
         as cvf2.
  (* begin proof of assert *)
  apply cover_vars_function; dands.
  apply cover_vars_lsubst_if; simpl.
  dup c2 as cvB.
  unfold cover_vars_upto in cvB.
  prove_subvars cvB; allsimpl.
  splst; splst in x; sp.
  introv k; sp; cpx.
  apply cover_vars_var; repeat (rw @dom_csub_snoc); repeat (rw in_snoc); sp.
  rw @cover_vars_upto_w; sp.
  dup c1 as cvA.
  rw @cover_vars_eq in cvA.
  prove_subvars cvA.
  splst; splst in x; sp.
  destruct (eq_var_dec b v0); sp; right; sp.
  dup c2 as cvB.
  prove_subvars cvB.
  splst; splst in x; sp.
  destruct (eq_var_dec v v0); destruct (eq_var_dec b v0); sp.
  (* end proof of assert*)

  rw @similarity_snoc; simpl.
  exists (snoc s1a (a, a1))
         (snoc s2a (a, a3))
         f1 f3
         wff2 cvf2; sp.

  rw @similarity_snoc; simpl.
  exists s1a s2a a1 a3 w1 c1; sp.

  (* we prove the equality of the f's from eiw'4 *)
  lsubst_tac.

  rw <- @fold_mkc_fun in eiw'4.

  revert_dependents w3.
  revert_dependents c4.
  rw @fold_subst; introv.

  assert (lsubstc (subst B v (mk_var a)) w3 (snoc s1a (a, a1)) c4
          = substc a1 v (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.
  rw @equality_in_function3.
  rw @equality_in_function3 in eiw'4; repnd; dands; try (complete auto).
  intros b1 b2 eib.
  generalize (eiw'4 b1 b2 eib); clear eiw'4; intro eqw; repnd.
  allrw @substc_cnewvar.

  assert (cover_vars (mk_w A v B) (snoc (snoc s1a (a, a1)) (b, b1)))
         as cv1
         by (apply cover_vars_change_sub2 with (sub1 := s1a); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp;
             rw subvars_prop; sp; splst; sp).

  generalize (simple_substc2 b1 b (mk_w A v B) (snoc s1a (a, a1)) w0 cv1 c5);
    intro eq1; dest_imp eq1 hyp;
    try (complete (splst; allapply @similarity_dom; repnd; allrw; sp)).
  repeat (rw <- eq1); clear eq1.

  assert (cover_vars (mk_w A v B) (snoc (snoc s1a (a, a1)) (b, b2)))
         as cv2
         by (apply cover_vars_change_sub2 with (sub1 := s1a); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp;
             rw subvars_prop; sp; splst; sp).

  generalize (simple_substc2 b2 b (mk_w A v B) (snoc s1a (a, a1)) w0 cv2 c5);
    intro eq1; dest_imp eq1 hyp;
    try (complete (splst; allapply @similarity_dom; repnd; allrw; sp)).
  repeat (rw <- eq1); clear eq1.

  lsubst_tac.
  lsubstc_snoc_vs.
  auto.


  (* next we prove the equality in Q from ind *)
  (* we prove the following to allow lsubst_tac to make progress *)
  assert (!LIn f (free_vars (lsubst B [(v, mk_var a)]))) as nifB1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint B [(v, mk_var a)]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors;
  try (rw not_over_or in k0); repnd;
  try (complete sp);
  try (complete (apply nifB in k1; sp)).
  (* end proof of assert *)
  lsubst_tac.

  revert_dependents w3.
  revert_dependents c.
  rw @fold_subst; introv.

  assert (lsubstc (subst B v (mk_var a)) w3 (snoc s1a (a, a1)) c
          = substc a1 v (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq; clear eq.
  rw @equality_in_function3; dands.

  rw <- @fold_mkc_fun in eiw'4.
  rw @equality_in_function3 in eiw'4; repnd; dands; try (complete auto).

  intros b1 b2 eib.
  assert (equality lib (mkc_apply f1 b1) (mkc_apply f1 b2)
                   (mkc_w (lsubstc A w1 s1a c1) v
                          (lsubstc_vars B w2 (csub_filter s1a [v]) [v] c2)))
         as eqf.
  (* begin proof of assert *)
  apply @equality_refl in eiw'4.
  rw <- @fold_mkc_fun in eiw'4.
  rw @equality_in_function3 in eiw'4; repnd.
  generalize (eiw'4 b1 b2 eib); clear eiw'4; intro eqw; repnd.
  allrw @substc_cnewvar; auto.
  (* end proof of assert *)

  assert (similarity lib s1a s1a H) as simref by (allapply @similarity_refl; auto).

  assert (cover_vars Q (snoc s1a (w, mkc_apply f1 b1)))
         as cv1
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w,t1)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  assert (cover_vars Q (snoc s1a (w, mkc_apply f1 b2)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w,t1)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).

  generalize (ind b1 b2 eib (mkc_apply f1 b2) eqf s1a simref cv1 cv2); intro teq; repnd.

  assert (substc b1 b
                 (lsubstc_vars (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) w4
                               (csub_filter (snoc (snoc s1a (a, a1)) (f, f1)) [b])
                               [b] c5)
          = lsubstc Q wfct (snoc s1a (w, mkc_apply f1 b1)) cv1)
         as eq1.
  (* begin proof of assert *)
  assert (wf_term (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b1)]))
         as wfsub by (apply wf_term_csubst; sp).
  assert (cover_vars
            (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b1)])
            (snoc (snoc s1a (a, a1)) (f, f1)))
         as cvsub by (rw @cover_vars_csubst3; simpl; sp).
  generalize (simple_substc
                b1 b (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                wfsub (snoc (snoc s1a (a, a1)) (f, f1)) cvsub w4 c5);
    intro eq1; rw <- eq1; clear eq1.
  revert_dependents wfsub.
  revert_dependents cvsub.
  rw @fold_subst.
  generalize (csubst_subst_pw_Q Q w f b b1); intro eq1; repeat (dest_imp eq1 hyp).
  rw eq1; introv; clear eq1.
  assert (wf_term (mk_apply (mk_var f) (get_cterm b1)))
         as wfap by (apply wf_apply_iff; sp; eauto with wf).
  assert (cover_vars (mk_apply (mk_var f) (get_cterm b1))
                     (snoc (snoc s1a (a, a1)) (f, f1)))
         as ca1 by (apply cover_vars_apply; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s1a (a, a1)) (f, f1)) [w]) [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).
  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b1)) w Q wfsub
                (snoc (snoc s1a (a, a1)) (f, f1)) cvsub wfap ca1 wfct cvuq);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq1.
  rw eq1; clear eq1.
  generalize (simple_substc2 (mkc_apply f1 b1) w Q s1a wfct cv1 c9);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  repeat (rw eq1); clear eq1.

  assert (substc b2 b
                 (lsubstc_vars (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) w4
                               (csub_filter (snoc (snoc s1a (a, a1)) (f, f1)) [b])
                               [b] c5)
          = lsubstc Q wfct (snoc s1a (w, mkc_apply f1 b2)) cv2)
         as eq2.
  (* begin proof of assert *)
  assert (wf_term (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b2)]))
         as wfsub by (apply wf_term_csubst; sp).
  assert (cover_vars
            (csubst (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))]) [(b, b2)])
            (snoc (snoc s1a (a, a1)) (f, f1)))
         as cvsub by (rw @cover_vars_csubst3; simpl; sp).
  generalize (simple_substc
                b2 b (lsubst Q [(w, mk_apply (mk_var f) (mk_var b))])
                wfsub (snoc (snoc s1a (a, a1)) (f, f1)) cvsub w4 c5);
    intro eq1; rw <- eq1; clear eq1.
  revert_dependents wfsub.
  revert_dependents cvsub.
  rw @fold_subst.
  generalize (csubst_subst_pw_Q Q w f b b2); intro eq1; repeat (dest_imp eq1 hyp).
  rw eq1; introv; clear eq1.
  assert (wf_term (mk_apply (mk_var f) (get_cterm b2)))
         as wfap by (apply wf_apply_iff; sp; eauto with wf).
  assert (cover_vars (mk_apply (mk_var f) (get_cterm b2))
                     (snoc (snoc s1a (a, a1)) (f, f1)))
         as ca1 by (apply cover_vars_apply; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s1a (a, a1)) (f, f1)) [w]) [w])
         as cvuq
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).
  generalize (simple_lsubstc_subst
                (mk_apply (mk_var f) (get_cterm b2)) w Q wfsub
                (snoc (snoc s1a (a, a1)) (f, f1)) cvsub wfap ca1 wfct cvuq);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw @free_vars_cterm; simpl; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw @lsubstc_cterm in eq1.
  rw eq1; clear eq1.
  generalize (simple_substc2 (mkc_apply f1 b2) w Q s1a wfct cv2 c9);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq2; clear eq2.
  dands; auto.

  generalize (cequivc_app_lam_axiom lib b1); intro ceq1.
  generalize (cequivc_app_lam_axiom lib b2); intro ceq2.

  apply @equality_respects_cequivc_left
        with (t1 := mkc_axiom);
    try (complete sp);
    try (complete (apply cequivc_sym; sp)).

  apply @equality_respects_cequivc_right
        with (t2 := mkc_axiom);
    try (complete sp);
    try (complete (apply cequivc_sym; sp)).


  (* we can not use our hypothesis from hyp0 and hyp1 *)
  exrepnd.
  lsubst_tac.

  revert_dependents wfct0.
  revert_dependents pC0.
  revert_dependents pC2.
  rw @fold_subst; introv teq eq.

  assert (!LIn z (free_vars (subst Q w (mk_sup (mk_var a) (mk_var f))))) as nizQ1.
  (* begin proof of assert *)
  intro k.
  generalize (eqvars_free_vars_disjoint Q [(w, mk_sup (mk_var a) (mk_var f))]); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in k.
  rw in_app_iff in k; rw in_remove_nvars in k; simpl in k.
  revert k; boolvar; simpl; intro k; repdors;
  try (rw not_over_or in k0); repnd;
  try (complete sp);
  try (complete (apply nifB in k1; sp)).
  (* end proof of assert *)
  lsubst_tac.

  assert (wf_term (mk_sup (mk_var a) (@mk_var o f)))
         as wfsup by (apply wf_sup; sp).
  assert (cover_vars (mk_sup (mk_var a) (mk_var f))
                     (snoc (snoc s1a (a, a1)) (f, f1)))
         as cvsup by (apply cover_vars_sup; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s1a (a, a1)) (f, f1)) [w]) [w])
         as cvusup
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).

  generalize (simple_lsubstc_subst
                (mk_sup (mk_var a) (mk_var f)) w Q wfct0
                (snoc (snoc s1a (a, a1)) (f, f1)) c wfsup cvsup wfct cvusup);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw disjoint_cons_l; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw eq1 in teq; rw eq1 in eq; clear eq1.
  generalize (simple_substc2 (mkc_sup a1 f1) w Q s1a wfct c0 c9);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw <- eq1 in teq; rw <- eq1 in eq; clear eq1.

  dands; auto.

  assert (cover_vars (mk_sup (mk_var a) (mk_var f))
                     (snoc (snoc s2a (a, a3)) (f, f3)))
         as cvsup2 by (apply cover_vars_sup; sp; apply cover_vars_var; splst; sp).
  assert (cover_vars_upto Q (csub_filter (snoc (snoc s2a (a, a3)) (f, f3)) [w]) [w])
         as cvusup2
         by (apply csubst.cover_vars_implies_cover_vars_upto with (sub2 := [(w,t1)]); simpl; sp;
             apply cover_vars_if_subvars with (sub1 := snoc s1a (w,t1)); sp;
             rw subvars_prop; introv k; splst in k; rw @dom_csub_app; splst; sp;
             allapply @similarity_dom; repnd; revert l; allrw; sp).

  generalize (simple_lsubstc_subst
                (mk_sup (mk_var a) (mk_var f)) w Q wfct0
                (snoc (snoc s2a (a, a3)) (f, f3)) c4 wfsup cvsup2 wfct cvusup2);
    intro eq1; autodimp eq1 hyp;
    try (complete (simpl; rw disjoint_cons_l; rw disjoint_singleton_l; sp)).
  lsubst_tac.
  lsubstc_snoc_vs.
  rw eq1 in teq; clear eq1.
  assert (cover_vars Q (snoc s2a (w, mkc_sup a3 f3)))
         as cv2
         by (apply cover_vars_change_sub with (sub1 := snoc s1a (w,t1)); sp;
             allrw @dom_csub_snoc; simpl; allapply @similarity_dom; repnd; allrw; sp).
  generalize (simple_substc2 (mkc_sup a3 f3) w Q s2a wfct cv2 c14);
    intro eq1; dest_imp eq1 hyp;
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw <- eq1 in teq; clear eq1.

  assert (cequivc lib (lsubstc Q wfct (snoc s2a (w, mkc_sup a3 f3)) cv2)
                  (lsubstc Q wfct (snoc s2a (w, t3)) c3))
         as ceq.
  (* begin proof of assert *)
  unfold cequivc; simpl.
  unfold csubst.
  apply cequiv_lsubst.
  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; allapply @in_csub2sub; auto.
  introv k; clear teq eq; rw @cover_vars_eq in c0;
    rw subvars_prop in c0; apply c0 in k;
    splst in k; splst; repdors; sp;
    revert k0; allapply @similarity_dom; repnd; allrw; sp.
  apply isprogram_lsubst.
  rw @nt_wf_eq; sp.
  introv k; allapply @in_csub2sub; auto.
  introv k; clear teq eq; rw @cover_vars_eq in c0;
    rw subvars_prop in c0; apply c0 in k;
    splst in k; splst; repdors; sp;
    revert k0; allapply @similarity_dom; repnd; allrw; sp.
  allrw @csub2sub_snoc.
  apply cequiv_subst_snoc; sp.
  apply cequiv_subst_csub2sub_refl.
  rw @fold_cequivc.
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; sp.
  (* end proof of assert *)

  apply tequality_respects_cequivc_right
        with (T2 := lsubstc Q wfct (snoc s2a (w, mkc_sup a3 f3)) cv2);
    try (complete sp).

  try (apply iscvalue_mkc_sup).


  (* ---- Finally, we conclude *)
  introv sim; introv.
  generalize (h t1 t2 sim1 t2 sim1 s2a sim pC1 pC2); intro teq; repnd; auto.
Qed.

(* begin hide *)




(* end hide *)

(* [24] ============ W EQUALITY ============ *)

(**

  We state the W equality rules as follows:
<<
   H |- W(a1,x1.b1) = W(a2,x2.b2) in Type(i)

     By WEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_w_equality {o}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_w a1 x1 b1)
                      (mk_w a2 x2 b2)
                      (mk_uni i))))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality a1 a2 (mk_uni i))),
      mk_baresequent
        (snoc H (mk_hyp y a1))
        (mk_conclax (mk_equality
                       (subst b1 x1 (mk_var y))
                       (subst b2 x2 (mk_var y))
                       (mk_uni i)))
    ]
    [ sarg_var y ].

Lemma rule_w_equality_true {o} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
  forall bc1 : !LIn y (bound_vars b1),
  forall bc2 : !LIn y (bound_vars b2),
    rule_true lib (rule_w_equality
                 a1 a2 b1 b2
                 x1 x2 y
                 i
                 H).
Proof.
  unfold rule_w_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality a1 a2 (mk_uni i))))
                   (inl eq_refl))
             (hyps (mk_baresequent (snoc H (mk_hyp y a1))
                                  (mk_conclax
                                     (mk_equality (subst b1 x1 (mk_var y))
                                                  (subst b2 x2 (mk_var y))
                                                  (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert ((y <> x1 -> !LIn y (free_vars b1))
          # (y <> x2 -> !LIn y (free_vars b2))
          # !LIn y (free_vars a1)
          # !LIn y (free_vars a2)
          # !LIn y (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
  try (complete (generalize (cg0 y); intro p;
                 allrw in_remove_nvars; sp; allsimpl;
                 d_imp p; sp));
  try (complete (generalize (cg y); intro p;
                 allrw in_remove_nvars; sp; allsimpl;
                 d_imp p; sp)).

  destruct vhyps as [ nyb1 vhyps ].
  destruct vhyps as [ nyb2 vhyps ].
  destruct vhyps as [ nyA1 vhyps ].
  destruct vhyps as [ nyA2 nyH ].
  (* done with proving these simple facts *)

  vr_seq_true.

  lift_lsubst.
  rewrite member_eq.
  rw <- @member_equality_iff.

  (* we have to prove the usual tequality and equality.
   * We start by proving the equality, which is about the functions being types *)
  assert (equality lib
            (mkc_w (lsubstc a1 w0 s1 c4) x1
                   (lsubstc_vars b1 w3 (csub_filter s1 [x1]) [x1] c5))
            (mkc_w (lsubstc a2 w4 s1 c6) x2
                   (lsubstc_vars b2 w5 (csub_filter s1 [x2]) [x2] c7))
            (mkc_uni i)) as eqfunc1.

  apply @equality_w_in_uni.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s1); clear hyp1; intro hyp1.
  dest_imp hyp1 hyp.
  dest_imp hyp1 hyp.
  apply @similarity_refl in sim; sp.
  exrepd.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e; auto.

  (* Then we prove that the b's are type families *)
  intros a a' eqaa'.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1 (y, a)) (snoc s1 (y, a'))); clear hyp2; intro hyp2.
  dest_imp hyp2 hyp2'.

  (* we have to prove the functionality of our hypotheses *)
  intros s3 sim2.
  inversion sim2; cpx; allsimpl; cpx.
  rw @eq_hyps_snoc; simpl.
  assert (cover_vars a1 s4) as cv4
    by (apply (similarity_cover_vars lib) with (hs := H) (s1 := s1); auto).
  exists s1 s4 a t2 w p cv4; sp.
  (* while proving that functionality result, we have to prove that
   * a1 is functional, which we prove using our 1st hyp *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s4); thin hyp1; intro hyp1.
  dest_imp hyp1 hyp1'.
  dest_imp hyp1 hyp1'; exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp1.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  apply @equality_commutes2 in hyp0; auto.
  allapply @equality_in_uni; auto.
  (* and we're done proving the functionality of the hypotheses *)

  (* we can keep on using our 2nd hypothsis *)
  dest_imp hyp2 hyp2'.
  rw @similarity_snoc; simpl.
  exists s1 s1 a a' w0 c4; sp.
  complete (allapply @similarity_refl; sp).

  exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp2.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s1 (y, a)) c12
          = substc a x1 (lsubstc_vars b1 w3 (csub_filter s1 [x1]) [x1] c5)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp2.
  rewrite eq1 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s1 (y, a)) c13
          = substc a x2 (lsubstc_vars b2 w5 (csub_filter s1 [x2]) [x2] c7)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp2.
  rewrite eq2 in hyp0.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s1 (y, a')) c14
          = substc a' x1 (lsubstc_vars b1 w3 (csub_filter s1 [x1]) [x1] c5)) as eq3
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq3 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s1 (y, a')) c15
          = substc a' x2 (lsubstc_vars b2 w5 (csub_filter s1 [x2]) [x2] c7)) as eq4
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq4 in hyp0.

  clear eq1 eq2 eq3 eq4.

  apply @equality_commutes in hyp0; sp.
  sp.
  (* we're done proving the equality, now we have to prove the tequality *)


  (* but first we prove the same thing as eqfunc1 but for s2 *)
  assert (equality lib
            (mkc_w (lsubstc a1 w0 s2 c8) x1
                   (lsubstc_vars b1 w3 (csub_filter s2 [x1]) [x1] c9))
            (mkc_w (lsubstc a2 w4 s2 c10) x2
                   (lsubstc_vars b2 w5 (csub_filter s2 [x2]) [x2] c11))
            (mkc_uni i)) as eqfunc2.

  apply @equality_w_in_uni.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp1.
  generalize (hyp1 s2 s2); clear hyp1; intro hyp1.
  dest_imp hyp1 hyp.
  apply @similarity_hyps_functionality_trans with (s1 := s1); auto.

  dest_imp hyp1 hyp.
  apply @similarity_sym in sim.
  apply @similarity_refl in sim; sp.
  apply eqh; auto.

  exrepd.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e; auto.

  (* Then we prove that the b's are type families *)
  intros a a' eqaa'.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s2 (y, a)) (snoc s2 (y, a'))); clear hyp2; intro hyp2.
  dest_imp hyp2 hyp2'.

  (* we have to prove the functionality of our hypotheses *)
  intros s3 sim2.
  inversion sim2; cpx; allsimpl; cpx.
  rw @eq_hyps_snoc; simpl.
  assert (cover_vars a1 s4) as cv4
    by (apply (similarity_cover_vars lib) with (hs := H) (s1 := s2); auto).
  exists s2 s4 a t2 w p cv4; sp.
  apply @similarity_hyps_functionality_trans with (s2 := s2) in eqh; auto.
  (* while proving that functionality result, we have to prove that
   * a1 is functional, which we prove using our 1st hyp *)
  vr_seq_true in hyp1.
  generalize (hyp1 s2 s4); thin hyp1; intro hyp1.
  dest_imp hyp1 hyp1'.
  apply @similarity_hyps_functionality_trans with (s1 := s1); auto.
  dest_imp hyp1 hyp1'; exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp1.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  apply @equality_commutes2 in hyp0; auto.
  allapply @equality_in_uni; auto.
  (* and we're done proving the functionality of the hypotheses *)

  (* we can keep on using our 2nd hypothsis *)
  dest_imp hyp2 hyp2'.
  rw @similarity_snoc; simpl.
  exists s2 s2 a a' w0 c8; sp.
  applydup @similarity_sym in sim; apply @similarity_refl in sim0; sp.

  exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp2.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s2 (y, a)) c12
          = substc a x1 (lsubstc_vars b1 w3 (csub_filter s2 [x1]) [x1] c9)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp2.
  rewrite eq1 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s2 (y, a)) c13
          = substc a x2 (lsubstc_vars b2 w5 (csub_filter s2 [x2]) [x2] c11)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp2.
  rewrite eq2 in hyp0.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s2 (y, a')) c14
          = substc a' x1 (lsubstc_vars b1 w3 (csub_filter s2 [x1]) [x1] c9)) as eq3
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq3 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s2 (y, a')) c15
          = substc a' x2 (lsubstc_vars b2 w5 (csub_filter s2 [x2]) [x2] c11)) as eq4
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq4 in hyp0.

  clear eq1 eq2 eq3 eq4.

  apply @equality_commutes in hyp0; sp.
  (* we're done proving the equality, now we have to prove the tequality *)


  rw @tequality_mkc_equality2; sp.
  apply tequality_mkc_uni.


  (* not we prove the same thing again but for s1/s2 *)
  assert (equality lib
            (mkc_w (lsubstc a1 w0 s1 c4) x1
                   (lsubstc_vars b1 w3 (csub_filter s1 [x1]) [x1] c5))
            (mkc_w (lsubstc a1 w0 s2 c8) x1
                   (lsubstc_vars b1 w3 (csub_filter s2 [x1]) [x1] c9))
            (mkc_uni i)) as eqfunc3.

  apply @equality_w_in_uni.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2); clear hyp1; intro hyp1.
  dest_imp hyp1 hyp.
  dest_imp hyp1 hyp.

  exrepd.
  lift_lsubst in e; lift_lsubst in t.
  rw @member_eq in e.
  rw <- @member_equality_iff in e; auto.

  apply @equality_commutes2 with (a2 := lsubstc a2 w4 s1 c6)
                                  (a4 := lsubstc a2 w4 s2 c10); auto.

  (* Then we prove that the b's are type families *)
  intros a a' eqaa'.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1 (y, a)) (snoc s2 (y, a'))); clear hyp2; intro hyp2.
  dest_imp hyp2 hyp2'.

  (* we have to prove the functionality of our hypotheses *)
  intros s3 sim2.
  inversion sim2; cpx; allsimpl; cpx.
  rw @eq_hyps_snoc; simpl.
  assert (cover_vars a1 s4) as cv4
    by (apply (similarity_cover_vars lib) with (hs := H) (s1 := s1); auto).
  exists s1 s4 a t2 w p cv4; sp.
  (* while proving that functionality result, we have to prove that
   * a1 is functional, which we prove using our 1st hyp *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s4); thin hyp1; intro hyp1.
  dest_imp hyp1 hyp1'.
  dest_imp hyp1 hyp1'; exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp1.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  apply @equality_commutes2 in hyp0; auto.
  allapply @equality_in_uni; auto.
  (* and we're done proving the functionality of the hypotheses *)

  (* we can keep on using our 2nd hypothsis *)
  dest_imp hyp2 hyp2'.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' w0 c4; sp.

  exrepnd; clear_irr.
  lift_lsubst in hyp0; lift_lsubst in hyp2.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2; clear_irr.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s1 (y, a)) c12
          = substc a x1 (lsubstc_vars b1 w3 (csub_filter s1 [x1]) [x1] c5)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp2.
  rewrite eq1 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s1 (y, a)) c13
          = substc a x2 (lsubstc_vars b2 w5 (csub_filter s1 [x2]) [x2] c7)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp2.
  rewrite eq2 in hyp0.

  assert (lsubstc (subst b1 x1 (mk_var y)) w6 (snoc s2 (y, a')) c14
          = substc a' x1 (lsubstc_vars b1 w3 (csub_filter s2 [x1]) [x1] c9)) as eq3
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq3 in hyp0.

  assert (lsubstc (subst b2 x2 (mk_var y)) w7 (snoc s2 (y, a')) c15
          = substc a' x2 (lsubstc_vars b2 w5 (csub_filter s2 [x2]) [x2] c11)) as eq4
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq4 in hyp0.

  clear eq1 eq2 eq3 eq4.

  apply @equality_commutes2 in hyp0; sp.
  (* we're done proving the equality, now we have to prove the tequality *)

  apply @equality3_implies_cequorsq2; auto.
Qed.

(* begin hide *)

Lemma rule_w_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H
         (bc1 : !LIn y (bound_vars b1))
         (bc2 : !LIn y (bound_vars b2)),
    @rule_true_if o lib (rule_w_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_w_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.





(* end hide *)


(* [24] ============ W INTRODUCTION ============ *)

(**

  We state the W introduction rule as follows:
<<
   H |- sup(a1,f1) = sup(a2,f2) in W(A,v.B)

     By WIntroduction ()

     H |- a1 = a2 in A
     H |- f1 = f2 in B[v\a1] -> W(A,v.B)
     H, a : A |- B[v\a] in Type(i)
>>
 *)

Definition rule_w_introduction {o}
           (a1 a2 f1 f2 A B : NTerm)
           (i : nat)
           (a v b : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_sup a1 f1)
                      (mk_sup a2 f2)
                      (mk_w A v B))))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality a1 a2 A)),
      mk_baresequent
        H
        (mk_conclax (mk_equality
                       f1
                       f2
                       (mk_function (subst B v a1) b (mk_w A v B)))),
      mk_baresequent
        (snoc H (mk_hyp a A))
        (mk_conclax (mk_member (subst B v (mk_var a)) (mk_uni i)))
    ]
    [].

Lemma rule_w_introduction_true {o} :
  forall lib (a1 a2 f1 f2 A B : NTerm),
  forall i : nat,
  forall a v b : NVar,
  forall H : @barehypotheses o,
  forall bc1 : !LIn b (v :: vars_hyps H),
  forall bc2 : !LIn a (bound_vars B),
  forall bc3 : disjoint (free_vars a1) (bound_vars B),
    rule_true lib (rule_w_introduction
                 a1 a2 f1 f2 A B
                 i
                 a v b
                 H).
Proof.
  unfold rule_w_introduction, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality a1 a2 A)))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      H
                      (mk_conclax
                         (mk_equality f1 f2 (mk_function (subst B v a1) b (mk_w A v B)))))
                   (inr (inl eq_refl)))
             (hyps (mk_baresequent (snoc H (mk_hyp a A))
                                  (mk_conclax (mk_member (subst B v (mk_var a)) (mk_uni i))))
                   (inr (inr (inl eq_refl))));
    simpl; intros hyp1 hyp2 hyp3; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destruct hyp3 as [ ws3 hyp3 ].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (!(b = v)
          # !LIn b (free_vars a1)
          # !LIn b (free_vars a2)
          # !LIn b (free_vars f1)
          # !LIn b (free_vars f2)
          # !LIn b (free_vars A)
          # (b <> v -> !LIn b (free_vars B))
          # (a <> v -> !LIn a (free_vars B))
          # !LIn a (vars_hyps H)
          # !LIn a (free_vars A)) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.
  sp;
    try (complete (assert (LIn b (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp));
    try (complete (assert (LIn a (remove_nvars [v] (free_vars B)))
                          by (rw in_remove_nvars; simpl; sp);
                   discover; sp)).

  destruct vhyps as [ nebv  vhyps ].
  destruct vhyps as [ niba1 vhyps ].
  destruct vhyps as [ niba2 vhyps ].
  destruct vhyps as [ nibf1 vhyps ].
  destruct vhyps as [ nibf2 vhyps ].
  destruct vhyps as [ nibA  vhyps ].
  destruct vhyps as [ nibB  vhyps ].
  destruct vhyps as [ niaB  vhyps ].
  destruct vhyps as [ niaH  niaA  ].
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  allrw @member_eq; dands.

  rw @tequality_mkc_equality2; dands.

  rw @tequality_mkc_w; dands.


  (* We prove that A is a type *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @tequality_mkc_equality2 in hyp0; repnd.
  auto.


  (* we prove that B is a family *)
  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,a0)) (snoc s2 (a,a3))); clear hyp3; intro hyp3.

  dest_imp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @tequality_mkc_equality2 in hyp0; repnd.
  auto.

  dest_imp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a0 a3 w0 c4; sp.

  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply tequality_in_uni_implies_tequality in hyp0; try (complete auto).

  assert (lsubstc (subst B v (mk_var a)) wt (snoc s1 (a, a0)) ct2
          = substc a0 v (lsubstc_vars B w3 (csub_filter s1 [v]) [v] c5)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq in hyp0; clear eq.

  assert (lsubstc (subst B v (mk_var a)) wt (snoc s2 (a, a3)) ct3
          = substc a3 v (lsubstc_vars B w3 (csub_filter s2 [v]) [v] c7)) as eq.
  (* begin proof of assert *)
  apply lsubstc_subst_snoc_eq;
    try (complete sp);
    try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  (* end proof of assert *)

  rw eq in hyp0; clear eq.
  auto.


  (* now we prove the equivalence between the equalities of the sups *)
  assert (similarity lib s2 s2 H)
         as sims2 by (apply @similarity_sym in sim; auto; apply @similarity_refl in sim; auto).

  assert (similarity lib s1 s1 H)
         as sims1 by (apply @similarity_refl in sim; auto).

  assert (hyps_functionality lib s2 H)
         as hf2 by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  split; intro k.

  (* 1st implication *)
  rw @equality_in_w_v1 in k; exrepnd; computes_to_value_isvalue.
  rw @equality_in_w_v1.
  exists (lsubstc a1 w4 s2 c12)
         (lsubstc a2 w6 s2 c14)
         (lsubstc f1 w5 s2 c13)
         (lsubstc f2 w7 s2 c15); dands;
  try (complete sp);
  try (complete (spcast; apply computes_to_valc_refl; apply iscvalue_mkc_sup)).

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd.
  apply hyp5 in hyp1; auto.

  vr_seq_true in hyp2.
  generalize (hyp2 s2 s2 hf2 sims2); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.
  generalize (lsubstc_vars_disjoint (mk_w A v B) wT (csub_filter s2 [b]) [b] c17); intro e.
  autodimp e hyp.
  rw disjoint_singleton_r; simpl; rw remove_nvars_nil_l; rw app_nil_r; rw in_app_iff; rw in_remove_nvars; sp.
  exrepnd.
  rw e0 in hyp2; clear e0.
  generalize (tequality_function_fun lib
                (lsubstc (subst B v a1) w8 s2 c16)
                b
                (lsubstc (mk_w A v B) wT (csub_filter s2 [b]) c'));
    intro eq.
  autodimp eq hyp; try (complete (left; apply inhabited_implies_tequality in hyp2; auto)).
  apply @tequality_preserving_equality with (a := lsubstc f1 w5 s2 c13) (b := lsubstc f2 w7 s2 c15) in eq;
    try (complete auto).
  generalize (simple_lsubstc_subst a1 v B w8 s2 c16 w4 c12 w3 c7); intro eqs.
  autodimp eqs hyp; rw eqs in eq; clear eqs.
  generalize (lsubstc_csub_filter_eq (mk_w A v B) wT s2 [b] c'); intro eqs; exrepnd; proof_irr.
  rw eqs0 in eq; clear eqs0.
  lsubst_tac; auto.

  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s2 (a,a0)) (snoc s2 (a,a'))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s2 s' hf2 sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s2 s2 a0 a' w0 c6; sp.
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s2 B v a a0 wt w3 ct2 c7); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s2 B v a a' wt w3 ct3 c7); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.

  (* 2nd implication *)
  rw @equality_in_w_v1 in k; exrepnd; computes_to_value_isvalue.
  rw @equality_in_w_v1.
  exists (lsubstc a1 w4 s1 c8)
         (lsubstc a2 w6 s1 c10)
         (lsubstc f1 w5 s1 c9)
         (lsubstc f2 w7 s1 c11); dands;
  try (complete sp);
  try (complete (spcast; apply computes_to_valc_refl; apply iscvalue_mkc_sup)).

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s1 eqh sims1); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1; auto.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s1 eqh sims1); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.
  generalize (lsubstc_vars_disjoint (mk_w A v B) wT (csub_filter s1 [b]) [b] c17); intro e.
  autodimp e hyp.
  rw disjoint_singleton_r; simpl; rw remove_nvars_nil_l; rw app_nil_r; rw in_app_iff; rw in_remove_nvars; sp.
  exrepnd.
  rw e0 in hyp2; clear e0.
  generalize (tequality_function_fun lib
                (lsubstc (subst B v a1) w8 s1 c16)
                b
                (lsubstc (mk_w A v B) wT (csub_filter s1 [b]) c'));
    intro eq.
  autodimp eq hyp; try (complete (left; apply inhabited_implies_tequality in hyp2; auto)).
  apply @tequality_preserving_equality with (a := lsubstc f1 w5 s1 c9) (b := lsubstc f2 w7 s1 c11) in eq;
    try (complete auto).
  generalize (simple_lsubstc_subst a1 v B w8 s1 c16 w4 c8 w3 c5); intro eqs.
  autodimp eqs hyp; rw eqs in eq; clear eqs.
  generalize (lsubstc_csub_filter_eq (mk_w A v B) wT s1 [b] c'); intro eqs; exrepnd; proof_irr.
  rw eqs0 in eq; clear eqs0.
  lsubst_tac; auto.

  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,a0)) (snoc s1 (a,a'))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a0 a' w0 c4; sp.
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s1 B v a a0 wt w3 ct2 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s1 B v a a' wt w3 ct3 c5); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.


  (* Now we prove the equorsq2 *)
  assert (similarity lib s2 s2 H)
         as sims2 by (apply @similarity_sym in sim; auto; apply @similarity_refl in sim; auto).

  assert (similarity lib s1 s1 H)
         as sims1 by (apply @similarity_refl in sim; auto).

  assert (hyps_functionality lib s2 H)
         as hf2 by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  unfold equorsq2, equorsq; dands; left.

  (* 1st concl *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); intro hyps1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  applydup @equality_commutes3 in hyps0 as eqf; try (complete auto).

  rw @equality_in_w_v1.
  exists (lsubstc a1 w4 s1 c8)
         (lsubstc a1 w4 s2 c12)
         (lsubstc f1 w5 s1 c9)
         (lsubstc f1 w5 s2 c13); dands;
  try (complete sp);
  try (complete (spcast; apply computes_to_valc_refl; apply iscvalue_mkc_sup)).

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1; auto.
  applydup @equality_commutes3 in hyp0 as eqa; auto.

  generalize (lsubstc_vars_disjoint (mk_w A v B) wT (csub_filter s1 [b]) [b] c17); intro e.
  autodimp e hyp.
  rw disjoint_singleton_r; simpl; rw remove_nvars_nil_l; rw app_nil_r; rw in_app_iff; rw in_remove_nvars; sp.
  exrepnd.
  rw e0 in eqf; clear e0.
  generalize (tequality_function_fun lib
                (lsubstc (subst B v a1) w8 s1 c16)
                b
                (lsubstc (mk_w A v B) wT (csub_filter s1 [b]) c'));
    intro eq.
  autodimp eq hyp; try (complete (left; apply inhabited_implies_tequality in eqf; auto)).
  apply @tequality_preserving_equality with (a := lsubstc f1 w5 s1 c9) (b := lsubstc f1 w5 s2 c13) in eq;
    try (complete auto).
  generalize (simple_lsubstc_subst a1 v B w8 s1 c16 w4 c8 w3 c5); intro eqs.
  autodimp eqs hyp; rw eqs in eq; clear eqs.
  generalize (lsubstc_csub_filter_eq (mk_w A v B) wT s1 [b] c'); intro eqs; exrepnd; proof_irr.
  rw eqs0 in eq; clear eqs0.
  lsubst_tac; auto.

  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,a0)) (snoc s1 (a,a'))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a0 a' w0 c4; sp.
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s1 B v a a0 wt w3 ct2 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s1 B v a a' wt w3 ct3 c5); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.


  (* 2nd concl *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); intro hyps1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  applydup @equality_commutes5 in hyps0 as eqf; try (complete auto).

  rw @equality_in_w_v1.
  exists (lsubstc a2 w6 s1 c10)
         (lsubstc a2 w6 s2 c14)
         (lsubstc f2 w7 s1 c11)
         (lsubstc f2 w7 s2 c15); dands;
  try (complete sp);
  try (complete (spcast; apply computes_to_valc_refl; apply iscvalue_mkc_sup)).

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1; auto.
  applydup @equality_commutes5 in hyp0 as eqa; auto.

  generalize (lsubstc_vars_disjoint (mk_w A v B) wT (csub_filter s1 [b]) [b] c17); intro e.
  autodimp e hyp.
  rw disjoint_singleton_r; simpl; rw remove_nvars_nil_l; rw app_nil_r; rw in_app_iff; rw in_remove_nvars; sp.
  exrepnd.
  rw e0 in eqf; clear e0.
  generalize (tequality_function_fun lib
                (lsubstc (subst B v a1) w8 s1 c16)
                b
                (lsubstc (mk_w A v B) wT (csub_filter s1 [b]) c'));
    intro eq.
  autodimp eq hyp; try (complete (left; apply inhabited_implies_tequality in eqf; auto)).
  apply @tequality_preserving_equality with (a := lsubstc f2 w7 s1 c11) (b := lsubstc f2 w7 s2 c15) in eq;
    try (complete auto).
  generalize (simple_lsubstc_subst a1 v B w8 s1 c16 w4 c8 w3 c5); intro eqs.
  autodimp eqs hyp; rw eqs in eq; clear eqs.
  generalize (lsubstc_csub_filter_eq (mk_w A v B) wT s1 [b] c'); intro eqs; exrepnd; proof_irr.
  rw eqs0 in eq; clear eqs0.
  lsubst_tac; auto.
  assert (tequality lib
            (substc (lsubstc a1 w4 s1 c8) v
                    (lsubstc_vars B w3 (csub_filter s1 [v]) [v] c5))
            (substc (lsubstc a2 w6 s1 c10) v
                    (lsubstc_vars B w3 (csub_filter s1 [v]) [v] c5))) as teq;
    try (complete (apply @tequality_mkc_fun_dom
                         with (B := mkc_w (lsubstc A w0 s1 c4) v
                                          (lsubstc_vars B w3 (csub_filter s1 [v]) [v] c5))
                         in teq;
                   try (complete (apply inhabited_implies_tequality in eq; auto));
                   apply @tequality_preserving_equality
                         with (a := lsubstc f2 w7 s1 c11) (b := lsubstc f2 w7 s2 c15)
                         in teq; auto)).
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,lsubstc a1 w4 s1 c8)) (snoc s1 (a,lsubstc a2 w6 s1 c10))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 (lsubstc a1 w4 s1 c8) (lsubstc a2 w6 s1 c10) w0 c4; sp.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s1 eqh sims1); clear hyp1; intro hyp1.
  exrepnd; lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1; auto.
  exrepnd; lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s1 B v a (lsubstc a1 w4 s1 c8) wt w3 ct2 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s1 B v a (lsubstc a2 w6 s1 c10) wt w3 ct3 c5); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.

  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,a0)) (snoc s1 (a,a'))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a0 a' w0 c4; sp.
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s1 B v a a0 wt w3 ct2 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s1 B v a a' wt w3 ct3 c5); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.


  (* Now we prove the membership *)
  assert (similarity lib s1 s1 H)
         as sims1 by (apply @similarity_refl in sim; auto).

  rw <- @member_equality_iff.
  rw @equality_in_w_v1.
  exists (lsubstc a1 w4 s1 c8)
         (lsubstc a2 w6 s1 c10)
         (lsubstc f1 w5 s1 c9)
         (lsubstc f2 w7 s1 c11); dands;
  try (complete sp);
  try (complete (spcast; apply computes_to_valc_refl; apply iscvalue_mkc_sup)).

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s1 eqh sims1); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s1 eqh sims1); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.
  generalize (lsubstc_vars_disjoint (mk_w A v B) wT (csub_filter s1 [b]) [b] c17); intro e.
  autodimp e hyp.
  rw disjoint_singleton_r; simpl; rw remove_nvars_nil_l; rw app_nil_r; rw in_app_iff; rw in_remove_nvars; sp.
  exrepnd.
  rw e0 in hyp2; clear e0.
  generalize (tequality_function_fun lib
                (lsubstc (subst B v a1) w8 s1 c16)
                b
                (lsubstc (mk_w A v B) wT (csub_filter s1 [b]) c'));
    intro eq.
  autodimp eq hyp; try (complete (left; apply inhabited_implies_tequality in hyp2; auto)).
  apply @tequality_preserving_equality with (a := lsubstc f1 w5 s1 c9) (b := lsubstc f2 w7 s1 c11) in eq;
    try (complete auto).
  generalize (simple_lsubstc_subst a1 v B w8 s1 c16 w4 c8 w3 c5); intro eqs.
  autodimp eqs hyp; rw eqs in eq; clear eqs.
  generalize (lsubstc_csub_filter_eq (mk_w A v B) wT s1 [b] c'); intro eqs; exrepnd; proof_irr.
  rw eqs0 in eq; clear eqs0.
  lsubst_tac; auto.

  introv eia.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (a,a0)) (snoc s1 (a,a'))); clear hyp3; intro hyp3.
  autodimp hyp3 hyp.
  apply @hyps_functionality_snoc2; simpl; try (complete auto).
  introv eia' sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s' eqh sim'); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in hyp1; auto.
  rw @tequality_mkc_equality2 in hyp0; repnd; auto.
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a0 a' w0 c4; sp.
  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp3.
  rw <- @member_member_iff in hyp3.
  apply member_in_uni in hyp3.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.

  generalize (lsubstc_subst_snoc_eq s1 B v a a0 wt w3 ct2 c5); intro eq1.
  repeat (autodimp eq1 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq1 in hyp0; clear eq1.

  generalize (lsubstc_subst_snoc_eq s1 B v a a' wt w3 ct3 c5); intro eq2.
  repeat (autodimp eq2 hyp); try (complete (allapply @similarity_dom; repnd; allrw; auto)).
  rw eq2 in hyp0; auto.
Qed.

(* end hide *)
