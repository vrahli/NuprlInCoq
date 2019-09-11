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


(*Require Export per_props2.*)
Require Export rwper.
Require Export subst_tacs.
Require Export cequiv_tacs.
Require Export sequents_tacs.
Require Export list. (* why? *)

(* !! MOVE *)
Lemma hasvaluec_mkc_axiom {o} : forall lib, @hasvaluec o lib mkc_axiom.
Proof.
  unfold hasvaluec, hasvalue, mkc_axiom; simpl.
  exists (@mk_axiom o); sp.
  apply computes_to_value_isvalue_refl; sp.
Qed.
Hint Immediate hasvaluec_mkc_axiom.

(* !! MOVE *)
Lemma hasvaluec_mkc_id {o} : forall lib, @hasvaluec o lib mkc_id.
Proof.
  unfold hasvaluec, hasvalue, mkc_id; simpl.
  exists (@mk_id o); sp.
  apply computes_to_value_isvalue_refl; sp.
  repeat constructor; simpl; sp; subst; repeat constructor.
Qed.
Hint Immediate hasvaluec_mkc_id.

(* !! MOVE *)
Lemma hasvaluec_mkc_zero {o} : forall lib, @hasvaluec o lib mkc_zero.
Proof.
  unfold hasvaluec, hasvalue, mkc_zero; simpl.
  exists (@mk_zero o); sp.
  apply computes_to_value_isvalue_refl; sp.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate hasvaluec_mkc_zero.

(* !! MOVE *)
Lemma cequiv_isaxiom {o} :
  forall lib (t1 a1 b1 t2 a2 b2 : @NTerm o),
    cequiv lib t1 t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_isaxiom t1 a1 b1) (mk_isaxiom t2 a2 b2).
Proof.
  introv c1 c2 c3.
  applydup @cequiv_isprogram in c1.
  applydup @cequiv_isprogram in c2.
  applydup @cequiv_isprogram in c3.
  repnd.
  unfold mk_isaxiom, mk_can_test, nobnd.
  repeat prove_cequiv; auto.
Qed.

Lemma cequivc_mkc_isaxiom_of_axiom {o} :
  forall lib (t a b : @CTerm o),
    cequivc lib t mkc_axiom
    -> cequivc lib (mkc_isaxiom t a b) a.
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allrw @isprog_eq.
  assert (cequiv lib (mk_isaxiom x1 x0 x) (mk_isaxiom mk_axiom x0 x))
         as c' by (apply cequiv_isaxiom; sp; try (complete (apply cequiv_refl; sp))).
  apply cequiv_trans with (b := mk_isaxiom mk_axiom x0 x); auto.
  apply reduces_to_implies_cequiv; sp.
  apply isprogram_isaxiom; sp.
  apply reduces_to_if_step.
  simpl; sp.
Qed.

Lemma cequivc_mkc_isaxiom_axiom {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_isaxiom mkc_axiom a b) a.
Proof.
  introv.
  apply cequivc_mkc_isaxiom_of_axiom; sp.
Qed.

(* !! MOVE *)
Lemma compute_step_isaxiom_right {p} :
  forall lib (t a b : @NTerm p),
    isvalue t
    -> !t = mk_axiom
    -> compute_step lib (mk_isaxiom t a b) = csuccess b.
Proof.
  introv isv neq.
  destruct t; try (complete (inversion isv; allsimpl; tcsp)).
  destruct o; try (complete (inversion isv; allsimpl; tcsp)).
  destruct c; try (complete (simpl; auto)).
  destruct l; try (complete (provefalse; apply neq; sp)).
  apply isvalue_program in isv.
  destruct isv as [cl wf].
  inversion wf; subst; allsimpl; cpx.
Qed.

Lemma cequivc_mkc_isaxiom_of_non_axiom {o} :
  forall lib (t u a b : @CTerm o),
    computes_to_valc lib t u
    -> !u = mkc_axiom
    -> cequivc lib (mkc_isaxiom t a b) b.
Proof.
  introv c neq.
  destruct_cterms.
  allunfold @cequivc; allunfold @computes_to_valc; allsimpl.
  allrw @isprog_eq.
  assert (!x1 = mk_axiom) as neqax by (intro k; apply neq; apply cterm_eq; simpl; auto).
  clear neq.
  assert (cequiv lib x2 x1) as ceq by (apply computes_to_value_implies_cequiv; auto).
  assert (cequiv lib (mk_isaxiom x2 x0 x) (mk_isaxiom x1 x0 x))
         as c' by (apply cequiv_isaxiom; sp; try (complete (apply cequiv_refl; sp))).
  apply cequiv_trans with (b := mk_isaxiom x1 x0 x); auto.
  apply reduces_to_implies_cequiv; sp.
  apply isprogram_isaxiom; sp; rw @isprogram_eq; auto.
  apply reduces_to_if_step.
  apply computes_to_value_isvalue in c.
  apply compute_step_isaxiom_right; auto.
Qed.

Lemma cequivc_mkc_isaxiom_id {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_isaxiom mkc_id a b) b.
Proof.
  introv.
  apply cequivc_mkc_isaxiom_of_non_axiom with (u := mkc_id); auto.
  apply computes_to_valc_refl.
  repeat constructor; simpl; sp; subst; repeat constructor.
  intro k; inversion k.
Qed.

Lemma equality_in_uand_implies {o} :
  forall lib t1 t2 A B w s c,
    @equality o lib t1 t2 (lsubstc (mk_uand A B) w s c)
    -> {wa : wf_term A
        , {wb : wf_term B
        , {ca : cover_vars A s
        , {cb : cover_vars B s
        , equality lib t1 t2 (lsubstc A wa s ca)
        # equality lib t1 t2 (lsubstc B wb s cb)
       }}}}.
Proof.
  introv eq.

  assert (wf_term A)
    as wA by (dup w as w'; apply wf_uand in w'; sp).
  assert (wf_term B)
    as wB by (dup w as w'; apply wf_uand in w'; sp).

  assert (cover_vars A s)
    as cA by (dup c as c'; apply cover_vars_uand in c'; sp).
  assert (cover_vars B s)
    as cB by (dup c as c'; apply cover_vars_uand in c'; sp).

  exists wA wB cA cB.

  allunfold @mk_uand.
  remember (newvars2 [A,B]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp;
  repeat (rw app_nil_r in Heqp); repeat (rw in_app_iff in Heqp);
  repeat (rw not_over_or in Heqp); repnd.

  lsubst_tac.
  rwpers.

  generalize (eq mkc_axiom mkc_axiom); intro eq1.
  autodimp eq1 hyp.
  rwpers.
  repnd.
  clear eq1.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  rwpers.
  generalize (eq0 mkc_axiom mkc_axiom); clear eq0; intro k.
  autodimp k hyp; repnd.
  rwpers; spcast.
  apply hasvaluec_mkc_axiom.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  allrw @fold_type.
  generalize (cequivc_mkc_isaxiom_axiom lib (lsubstc A wA s cA) (lsubstc B wB s cB));
    intro ceq.
  rwg_h k ceq.
  rwg_h k0 ceq.

  generalize (eq mkc_id mkc_id); intro eq2.
  autodimp eq2 hyp.
  rwpers.
  repnd.
  clear eq2.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  rwpers.
  generalize (eq0 mkc_axiom mkc_axiom); clear eq0; intro j.
  autodimp j hyp; repnd.
  rwpers; spcast.
  apply hasvaluec_mkc_id.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  allrw @fold_type.
  generalize (cequivc_mkc_isaxiom_id lib (lsubstc A wA s cA) (lsubstc B wB s cB));
    intro ceq'.
  rwg_h j ceq'.
  rwg_h j0 ceq'.
  auto.
Qed.

Lemma tequality_uand_implies {o} :
  forall lib A B w s1 s2 c1 c2,
    @tequality o lib (lsubstc (mk_uand A B) w s1 c1) (lsubstc (mk_uand A B) w s2 c2)
    -> {wa : wf_term A
        , {wb : wf_term B
        , {ca1 : cover_vars A s1
        , {ca2 : cover_vars A s2
        , {cb1 : cover_vars B s1
        , {cb2 : cover_vars B s2
        , tequality lib (lsubstc A wa s1 ca1) (lsubstc A wa s2 ca2)
        # tequality lib (lsubstc B wb s1 cb1) (lsubstc B wb s2 cb2)
       }}}}}}.
Proof.
  introv teq.

  assert (wf_term A)
    as wA by (dup w as w'; apply wf_uand in w'; sp).
  assert (wf_term B)
    as wB by (dup w as w'; apply wf_uand in w'; sp).

  assert (cover_vars A s1)
    as cA1 by (dup c1 as c'; apply cover_vars_uand in c'; sp).
  assert (cover_vars B s1)
    as cB1 by (dup c1 as c'; apply cover_vars_uand in c'; sp).

  assert (cover_vars A s2)
    as cA2 by (dup c2 as c'; apply cover_vars_uand in c'; sp).
  assert (cover_vars B s2)
    as cB2 by (dup c2 as c'; apply cover_vars_uand in c'; sp).

  exists wA wB cA1 cA2 cB1 cB2.

  allunfold @mk_uand.
  remember (newvars2 [A,B]); repnd.
  apply newvars2_prop2 in Heqp; simpl in Heqp;
  repeat (rw app_nil_r in Heqp); repeat (rw in_app_iff in Heqp);
  repeat (rw not_over_or in Heqp); repnd.

  lsubst_tac.
  rwpers.

  generalize (teq mkc_axiom mkc_axiom); intro teq1.
  autodimp teq1 hyp.
  rwpers.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  rwpers.
  generalize (teq1 mkc_axiom mkc_axiom); clear teq0 teq1; intro k.
  autodimp k hyp; repnd.
  rwpers; spcast.
  apply hasvaluec_mkc_axiom.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  generalize (cequivc_mkc_isaxiom_axiom lib (lsubstc A wA s1 cA1) (lsubstc B wB s1 cB1));
    intro ceq.
  rwg_h k ceq; clear ceq.
  generalize (cequivc_mkc_isaxiom_axiom lib (lsubstc A wA s2 cA2) (lsubstc B wB s2 cB2));
    intro ceq.
  rwg_h k ceq; clear ceq.

  dands; auto.

  generalize (teq mkc_id mkc_id); intro teq2.
  autodimp teq2 hyp.
  rwpers.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  rwpers.
  generalize (teq2 mkc_axiom mkc_axiom); clear teq0 teq2; intro j.
  autodimp j hyp; repnd.
  rwpers; spcast.
  apply hasvaluec_mkc_id.
  repeat (substc_lsubstc_vars3; lsubst_tac).
  generalize (cequivc_mkc_isaxiom_id lib (lsubstc A wA s1 cA1) (lsubstc B wB s1 cB1));
    intro ceq'.
  rwg_h j ceq'; clear ceq'.
  generalize (cequivc_mkc_isaxiom_id lib (lsubstc A wA s2 cA2) (lsubstc B wB s2 cB2));
    intro ceq'.
  rwg_h j ceq'; clear ceq'.

  auto.
Qed.
