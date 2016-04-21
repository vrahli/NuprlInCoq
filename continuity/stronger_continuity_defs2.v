(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export computation_dec1.
(*Require Export computation_dec.*)
Require Export computation9.
Require Export stronger_continuity_defs_typ.


Definition old_bound_nat_aux {o} (arg : @NTerm o) x z (f : @NTerm o) :=
  mk_cbv arg x (mk_less (mk_var x)
                        mk_zero
                        (mk_vbot z)
                        (mk_apply f (mk_var x))).

Definition bound_nat_aux {o} (a : get_patom_set o) (arg : @NTerm o) x e z (f : @NTerm o) :=
  mk_cbv arg x (mk_less (mk_var x)
                        mk_zero
                        (mk_vbot z)
                        (mk_try (mk_apply f (mk_var x))
                                (mk_utoken a)
                                e
                                (spexc a))).
(* Above we assume that e computes to axiom *)

Definition bound_nat_try_aux {o} (a : get_patom_set o) (arg : @NTerm o) x e z (f : @NTerm o) t :=
  mk_cbv arg x (mk_less (mk_var x)
                        mk_zero
                        (mk_vbot z)
                        (mk_try (mk_apply f (mk_var x)) (mk_utoken a) e t)).

Definition bound_nat {o} a x e z (f : @NTerm o) :=
  mk_lam x (bound_nat_aux a (mk_var x) x e z f).

Definition bound_nat_try {o} (a : get_patom_set o) x e z (f : @NTerm o) :=
  mk_lam x (bound_nat_try_aux a (mk_var x) x e z f mk_zero).

Definition bound_nat_try_c {o} (a : get_patom_set o) x e z (f : @CTerm o) :=
  mkc_lam x (mkcv_cbv [x]
                      (mkc_var x)
                      x
                      (mkcv_dup1
                         x
                         (mkcv_less [x]
                                    (mkc_var x)
                                    (mkcv_zero [x])
                                    (mkcv_vbot [x] z)
                                    (mkcv_try [x]
                                              (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))
                                              (mkcv_utoken [x] a)
                                              e
                                              (mkcv_zero [e,x]))))).


Lemma get_cterm_bound_nat_try_c {o} :
  forall (a : get_patom_set o) x e z f,
    get_cterm (bound_nat_try_c a x e z f)
    = bound_nat_try a x e z (get_cterm f).
Proof. sp. Qed.

Definition implies_equal_bound_nat_try_c {o} :
  forall lib a x e z (f g : @CTerm o),
    e <> x
    -> equality lib f g (nat2natE a)
    -> equality lib (bound_nat_try_c a x e z f) (bound_nat_try_c a x e z g) nat2nat.
Proof.
  introv d equ.
  unfold nat2nat.
  unfold nat2natE in equ.
  allrw @equality_in_fun; repnd; dands; tcsp.
  clear equ1 equ0.

  introv en.
  unfold bound_nat_try_c.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].

  allrw @mkcv_cbv_substc_same.
  allrw @mkcv_cont1_dup1.
  allrw @mkc_var_substc.

  dup en as ct.
  apply equality_in_tnat in ct; unfold equality_of_nat in ct; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply simpl_cequivc_mkc_cbv;
     apply computes_to_valc_implies_cequivc;exact ct1
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply simpl_cequivc_mkc_cbv;
     apply computes_to_valc_implies_cequivc;exact ct0
    |].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
      apply reduces_toc_implies_cequivc;
      apply reduces_toc_mkc_cbv_val; eauto 3 with slow
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;
      apply reduces_toc_implies_cequivc;
      apply reduces_toc_mkc_cbv_val; eauto 3 with slow
    |].

  allrw @mkcv_less_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_vbot_substc.
  repeat (rw @mkcv_try_substc; auto).
  allrw @mkcv_apply_substc.
  allrw @csubst_mk_cv.
  allrw @mkc_var_substc.
  allrw @mkcv_utoken_substc.
  allrw @substc_mkcv_zero.
  unfold mkcv_zero.
  repeat (rw @substc2_mk_cv).
  fold (@mkcv_zero o [e]).

  rw @mkc_zero_eq.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_less_nat
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat
    |].
  boolvar; tcsp.

  applydup equ in en.
  eapply equality_respects_cequivc_left in en0;
    [|apply implies_cequivc_apply;[apply cequivc_refl|];
      apply computes_to_valc_implies_cequivc;exact ct1
    ].
  eapply equality_respects_cequivc_right in en0;
    [|apply implies_cequivc_apply;[apply cequivc_refl|];
      apply computes_to_valc_implies_cequivc;exact ct0
    ].

  apply @equality_in_natE in en0.
  repndors.

  - unfold equality_of_nat in en0; exrepnd; spcast.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;[exact en0|];
        apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;[exact en1|];
        apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc
      |].
    apply equality_in_tnat; unfold equality_of_nat.
    exists k0; dands; spcast; apply computes_to_valc_refl; eauto 2 with slow.

  - repnd; spcast.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact en1|apply cequivc_refl]
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact en0|apply cequivc_refl]
      |].

    unfold spexc.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    allrw @substc_mkcv_zero.
    apply equality_in_tnat; unfold equality_of_nat.
    exists 0; dands; spcast; rw @mkc_zero_eq;
    apply computes_to_valc_refl; eauto 2 with slow.
Qed.

Lemma alpha_eq_bound_nat_try_aux {o} :
  forall (a : get_patom_set o) arg1 arg2 x1 e1 z1 x2 e2 z2 f1 f2 t1 t2,
    isprog f1
    -> isprog f2
    -> isprog t1
    -> isprog t2
    -> alpha_eq arg1 arg2
    -> alpha_eq f1 f2
    -> alpha_eq t1 t2
    -> alpha_eq (bound_nat_try_aux a arg1 x1 e1 z1 f1 t1)
                (bound_nat_try_aux a arg2 x2 e2 z2 f2 t2).
Proof.
  introv isp1 isp2 ispt1 ispt2 aeq1 aeq2 aeqt.
  applydup @closed_if_isprog in isp1 as cl1.
  applydup @closed_if_isprog in isp2 as cl2.
  applydup @closed_if_isprog in ispt1 as clt1.
  applydup @closed_if_isprog in ispt2 as clt2.

  unfold bound_nat_try_aux, mk_cbv, nobnd, mk_less.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (x1 :: x2
                               :: e1
                               :: e2
                               :: z1
                               :: z2
                               :: bound_vars f1
                               ++ bound_vars f2
                               ++ bound_vars t1
                               ++ bound_vars t2)) as fv.
  exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v]); allsimpl; auto.

  { unfold all_vars; simpl.
    rw cl1; rw cl2; simpl.
    rw clt1; rw clt2; simpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    rw disjoint_singleton_l; simpl.
    allrw @remove_nvars_eq; allsimpl.
    allrw in_app_iff; allsimpl.
    allrw in_app_iff; simpl.
    allrw in_app_iff; simpl.
    allrw in_remove_nvars; simpl; allrw not_over_or.
    sp. }

  allrw memvar_singleton.
  allrw <- @beq_var_refl.

  repeat (prove_alpha_eq4).

  { pose proof (ex_fresh_var []) as fv'.
    exrepnd.
    allsimpl; allrw not_over_or; repnd; GC.

    apply (al_bterm_aux [v]); allsimpl; auto.

    { apply disjoint_singleton_l; boolvar; unfold all_vars; simpl; boolvar; simpl;
      allrw not_over_or; tcsp. }

    repeat (boolvar; simpl); tcsp. }

  { repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow). }

  { repeat (rw @lsubst_aux_trivial_cl_term2; auto).
    pose proof (ex_fresh_var []) as fv'.
    exrepnd.
    allsimpl; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v]); allsimpl; auto.
    { unfold all_vars; rw clt1; rw clt2; simpl; allrw app_nil_r.
      apply disjoint_singleton_l; allrw in_app_iff; sp. }
    { repeat (rw @lsubst_aux_trivial_cl_term2; auto). }
  }
Qed.

Lemma alpha_eq_bound_nat_aux {o} :
  forall a (arg1 arg2 : @NTerm o) x1 e1 z1 x2 e2 z2 f1 f2,
    isprog f1
    -> isprog f2
    -> alpha_eq arg1 arg2
    -> alpha_eq f1 f2
    -> alpha_eq (bound_nat_aux a arg1 x1 e1 z1 f1)
                (bound_nat_aux a arg2 x2 e2 z2 f2).
Proof.
  introv isp1 isp2 aeq1 aeq2.
  applydup @closed_if_isprog in isp1 as cl1.
  applydup @closed_if_isprog in isp2 as cl2.

  unfold bound_nat_aux, mk_cbv, nobnd, mk_less.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (x1 :: x2
                               :: z1
                               :: z2
                               :: e1
                               :: e2
                               :: bound_vars f1
                               ++ bound_vars f2)) as fv.
  exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v]); allsimpl; auto.

  { unfold all_vars; simpl.
    rw cl1; rw cl2; simpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    rw disjoint_singleton_l; simpl.
    allrw @remove_nvars_eq; allsimpl.
    allrw in_app_iff; allsimpl.
    allrw in_app_iff; simpl.
    tcsp. }

  allrw memvar_singleton.
  allrw <- @beq_var_refl.

  repeat (prove_alpha_eq4).

  { pose proof (ex_fresh_var []) as fv'.
    exrepnd.
    allsimpl; allrw not_over_or; repnd; GC.

    apply (al_bterm_aux [v]); allsimpl; auto.

    { apply disjoint_singleton_l; boolvar; unfold all_vars; simpl; boolvar; simpl;
      allrw not_over_or; tcsp. }

    repeat (boolvar; simpl); tcsp. }

  { repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow). }

  { pose proof (ex_fresh_var []) as fv'.
    exrepnd.
    allsimpl; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v]); allsimpl; auto.

    { unfold all_vars; simpl; tcsp. }
  }
Qed.

Definition combine3 {A B C} (l1 : list A) (l2 : list B) (l3 : list C) : list ((A # B) # C) :=
  combine (combine l1 l2) l3.

Fixpoint lfresh {o} vs (t : @NTerm o) :=
  match vs with
    | [] => t
    | v :: vs => mk_fresh v (lfresh vs t)
  end.

(* spexc is not necessary in the fresh case because with move freshs down
   value-like terms such as exceptions
 *)
Definition spfexc {o} vs1 vs2 (a : get_patom_set o) :=
  mk_exception (lfresh vs1 (mk_utoken a)) (lfresh vs2 mk_axiom).

Definition spfexc_pair {o} a (t u : @NTerm o) :=
  {vs1 : list NVar
   & {vs2 : list NVar
   & {vs3 : list NVar
   & {vs4 : list NVar
   & length vs1 = length vs2
   # length vs3 = length vs4
   # length vs1 = length vs3
   # t = spfexc vs1 vs2 a
   # u = spfexc vs3 vs4 a }}}}.

Lemma spfexc_pair_spfexc {o} :
  forall vs1 vs2 vs3 vs4 (a : get_patom_set o),
    length vs1 = length vs2
    -> length vs3 = length vs4
    -> length vs1 = length vs3
    -> spfexc_pair a (spfexc vs1 vs2 a) (spfexc vs3 vs4 a).
Proof.
  introv; exists vs1 vs2 vs3 vs4; sp.
Qed.
Hint Resolve spfexc_pair_spfexc : slow.

Definition eq_fun2natE2 {o} lib a (f g : @NTerm o) :=
  forall n,
    ({k : nat
      & computes_to_value lib (mk_apply f (mk_nat n)) (mk_nat k)
      # computes_to_value lib (mk_apply g (mk_nat n)) (mk_nat k)}
    [+]
    (computes_to_exception lib (mk_utoken a) (mk_apply f (mk_nat n)) mk_axiom
     # computes_to_exception lib (mk_utoken a) (mk_apply g (mk_nat n)) mk_axiom)).

Hint Resolve wf_apply : isprog.
Hint Resolve wf_term_implies : isprog.
Hint Resolve nt_wf_implies : isprog.
Hint Resolve wf_mk_nat : isprog.

Lemma eq_fun2natE2_alpha_eq {o} :
  forall lib a (f f' g g' : @NTerm o),
    nt_wf f
    -> nt_wf g
    -> alpha_eq f f'
    -> alpha_eq g g'
    -> eq_fun2natE2 lib a f g
    -> eq_fun2natE2 lib a f' g'.
Proof.
  introv wff wfg aeq1 aeq2 e; introv.
  pose proof (e n) as h; clear e.
  repndors; exrepnd;[left|right].
  - eapply compute_to_value_alpha in h1;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ];
    eauto 4 with isprog; exrepnd.
    eapply compute_to_value_alpha in h0;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ];
    eauto 4 with isprog; exrepnd.
    allapply @alpha_eq_mk_nat; subst.
    exists k; dands; auto.
  - eapply compute_to_exception_alpha in h0;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ];
    eauto 4 with isprog; exrepnd.
    eapply compute_to_exception_alpha in h;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ];
    eauto 4 with isprog; exrepnd.
    allapply @alpha_eq_mk_utoken; subst.
    allapply @alpha_eq_mk_axiom; subst.
    auto.
Qed.

Definition eq_fun2natE {o} lib a (f g : @NTerm o) :=
  forall n,
    ({k : nat
      & computes_to_value lib (mk_apply f (mk_nat n)) (mk_nat k)
      # computes_to_value lib (mk_apply g (mk_nat n)) (mk_nat k)}
    [+]
    (cequiv lib (mk_apply f (mk_nat n)) (spexc a)
     # cequiv lib (mk_apply g (mk_nat n)) (spexc a))).

Lemma eq_fun2natE_alpha_eq {o} :
  forall lib a (f f' g g' : @NTerm o),
    nt_wf f
    -> nt_wf g
    -> alpha_eq f f'
    -> alpha_eq g g'
    -> eq_fun2natE lib a f g
    -> eq_fun2natE lib a f' g'.
Proof.
  introv wff wfg aeq1 aeq2 e; introv.
  pose proof (e n) as h; clear e.
  repndors; exrepnd;[left|right].
  - eapply compute_to_value_alpha in h1;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ];
    eauto 4 with isprog.
    eapply compute_to_value_alpha in h0;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ];
    eauto 4 with isprog.
    exrepnd.
    allapply @alpha_eq_mk_nat; subst.
    exists k; dands; auto.
  - eapply cequiv_rw_l_eauto in h0;
    [|apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ].
    eapply cequiv_rw_l_eauto in h;
    [|apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ].
    auto.
Qed.

Lemma equality_in_nat2natE_implies {o} :
  forall lib (f g : @CTerm o) a,
    equality lib f g (nat2natE a)
    -> eq_fun2natE lib a (get_cterm f) (get_cterm g).
Proof.
  introv equ.
  apply equality_in_fun in equ; repnd.
  clear equ0 equ1.
  introv.
  pose proof (equ (mkc_nat n) (mkc_nat n)) as k.
  autodimp k hyp.
  { apply equality_in_tnat; unfold equality_of_nat.
    exists n; dands; spcast; apply computes_to_valc_refl;
    eauto 3 with slow. }

  apply equality_in_natE_implies in k.
  unfold equality_of_nat_tt in k; exrepnd.
  allunfold @computes_to_valc; allsimpl.
  allunfold @cequivc; allsimpl.
  allrw @get_cterm_apply; allsimpl; tcsp.
Qed.

(* XXXXXXXXXXXXXXXXX *)

Definition eq_fun2TE {o} lib a (f g : @NTerm o) :=
  forall n,
    ({v1 : NTerm
      & {v2 : NTerm
      & computes_to_value lib (mk_apply f (mk_nat n)) v1
      # computes_to_value lib (mk_apply g (mk_nat n)) v2
      # alpha_eq v1 v2
      # !LIn a (get_utokens v1) }}
    [+]
    (cequiv lib (mk_apply f (mk_nat n)) (spexc a)
     # cequiv lib (mk_apply g (mk_nat n)) (spexc a))).

Definition TE {o} (a : @get_patom_set o) T := with_nexc_c a T mkc_unit.
Definition nat2TE {o} (a : @get_patom_set o) T := mkc_fun mkc_tnat (TE a T).

Definition compute_to_eqvals_na {o} lib a (t1 t2 : @CTerm o) :=
  {v : CTerm
   & computes_to_valc lib t1 v
   # computes_to_valc lib t2 v
   # noseqc v
   # noconstc v
   # !LIn a (getc_utokens v) }.

Definition value_type {o} lib (T : @CTerm o) :=
  forall t, member lib t T -> hasvaluec lib t.

Definition eq_value_type_na {o} lib a (T : @CTerm o) :=
  forall t1 t2,
    equality lib t1 t2 T
    -> compute_to_eqvals_na lib a t1 t2.

Lemma eq_value_type_na_implies_value_type {o} :
  forall lib a (T : @CTerm o),
    eq_value_type_na lib a T -> value_type lib T.
Proof.
  introv eqv mem.
  apply eqv in mem.
  unfold compute_to_eqvals_na in mem.
  exrepnd.
  eapply computes_to_valc_implies_hasvaluec; eauto.
Qed.
Hint Resolve eq_value_type_na_implies_value_type : slow.

Lemma tequality_TE {o} :
  forall lib a (t1 t2 : @CTerm o),
    tequality lib (TE a t1) (TE a t2) <=> tequality lib t1 t2.
Proof.
  introv.
  unfold TE.
  rw @tequality_with_nexc_c.
  split; introv k; repnd; dands; eauto 3 with slow.
  apply type_mkc_unit.
Qed.

Lemma disjoint_val_exc {o} :
  forall lib (a b : @CTerm o) T,
    value_type lib T
    -> disjoint_types lib T (mkc_texc a b).
Proof.
  introv vT mem; repnd.

  apply vT in mem0.

  allrw @equality_in_mkc_texc; exrepnd; spcast.
  apply hasvaluec_computes_to_valc_implies in mem0; exrepnd.
  eapply computes_to_valc_and_excc_false in mem5; eauto.
Qed.

Lemma equality_in_TE {o} :
  forall lib n (a b : @CTerm o) T,
    type lib T ->
    value_type lib T ->
    (equality lib a b (TE n T)
     <=> (equality lib a b T
          {+} (ccequivc lib a (spexcc n) # ccequivc lib b (spexcc n)))).
Proof.
  introv tT vT.
  unfold TE, with_nexc_c.

  pose proof (equality_in_disjoint_bunion lib a b T (mkc_ntexc n mkc_unit)) as h.
  autodimp h hyp.
  { unfold mkc_ntexc; apply disjoint_val_exc; auto. }
  rw h; clear h.
  rw @type_mkc_ntexc.

  split; intro k; repnd; dands; eauto 3 with slow; repndors; tcsp;
  allrw @equality_in_tnat;
  allrw @equality_in_mkc_ntexc;
  exrepnd; spcast; tcsp;
  allrw @equality_in_unit;
  repnd; spcast; auto.

  - allapply @computes_to_excc_implies_cequivc.
    allapply @computes_to_valc_implies_cequivc.
    right; dands; spcast.
    + eapply cequivc_trans;[exact k5|].
      apply continuity_defs_ceq.cequivc_mkc_exception; auto.
    + eapply cequivc_trans;[exact k6|].
      unfold spexc.
      apply continuity_defs_ceq.cequivc_mkc_exception; auto.

  - right; allrw @equality_in_mkc_ntexc.
    allunfold @spexc.
    apply cequivc_sym in k0; apply cequivc_sym in k.
    apply cequivc_exception_implies in k0.
    apply cequivc_exception_implies in k.
    exrepnd.
    allapply @cequivc_axiom_implies.
    allapply @cequivc_utoken_implies.
    exists x0 x c0 c; dands; spcast; auto.
    allrw @equality_in_unit; dands; spcast; auto.
Qed.

Lemma iscvalue_implies_iscanc {o} :
  forall (t : @CTerm o), iscvalue t -> iscanc t.
Proof.
  introv isc.
  destruct_cterms.
  allunfold @iscvalue; allunfold @iscanc; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_implies_iscanc : slow.

Lemma iscanc_implies_iscvalue {o} :
  forall (t : @CTerm o), iscanc t -> iscvalue t.
Proof.
  introv isc.
  destruct_cterms.
  allunfold @iscvalue; allunfold @iscanc; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve iscanc_implies_iscvalue : slow.

Lemma isccan_implies_isvalue {o} :
  forall (t : @NTerm o), isprog t -> isccan t -> isvalue t.
Proof.
  introv isp isc.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  destruct op; tcsp.
  constructor; simpl; eauto 3 with slow.
Qed.
Hint Resolve isccan_implies_isvalue : slow.

Lemma isccanc_implies_iscvalue {o} :
  forall (t : @CTerm o), isccanc t -> iscvalue t.
Proof.
  introv isc.
  destruct_cterms.
  allunfold @iscvalue; allunfold @isccanc; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve isccanc_implies_iscvalue : slow.

Lemma reduces_in_atmost_k_steps_excc_eq {o} :
  forall lib (t : @CTerm o) v1 v2 k,
    reduces_in_atmost_k_steps_excc lib t v1 k
    -> reduces_in_atmost_k_steps_excc lib t v2 k
    -> v1 = v2.
Proof.
  introv r1 r2.
  destruct_cterms.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  apply cterm_eq; simpl.
  allunfold @reduces_in_atmost_k_steps_exc.
  rw r1 in r2; ginv.
Qed.

Lemma equality_in_TE_implies {o} :
  forall lib (t1 t2 : @CTerm o) a T,
    eq_value_type_na lib a T
    -> equality lib t1 t2 (TE a T)
    -> compute_to_eqvals_na lib a t1 t2
       [+] (cequivc lib t1 (spexcc a) # cequivc lib t2 (spexcc a)).
Proof.
  introv vT equ.

  applydup @inhabited_implies_tequality in equ as tT.
  apply tequality_TE in tT.

  apply equality_in_TE in equ; eauto 3 with slow.

  assert {k : nat
          , {v : CTerm
             , reduces_ksteps_excc lib t1 v k
             # reduces_ksteps_excc lib t2 v k
             # iscanc v
             # noconstc v
             # noseqc v
             # !LIn a (getc_utokens v) }
            {+} (reduces_ksteps_excc lib t1 (spexcc a) k
                 # reduces_ksteps_excc lib t2 (spexcc a) k) } as j.
  { repndors.

    - apply vT in equ.
      unfold compute_to_eqvals_na in equ; exrepnd.
      rw @computes_to_valc_iff_reduces_in_atmost_k_stepsc in equ1; exrepnd.
      rw @computes_to_valc_iff_reduces_in_atmost_k_stepsc in equ2; exrepnd.
      exists (Peano.max k k0); left.
      exists v.
      dands; eauto 3 with slow; spcast.
      + apply reduces_in_atmost_k_steps_excc_can; eauto 3 with slow.
        eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact equ6]; auto;
        try (apply NPeano.Nat.le_max_l; auto).
      + apply reduces_in_atmost_k_steps_excc_can; eauto 3 with slow.
        eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact equ7]; auto;
        try (apply NPeano.Nat.le_max_r; auto).

    - repnd; spcast.
      apply cequivc_spexcc in equ.
      apply cequivc_spexcc in equ0.
      exrepnd.
      allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
      allrw @computes_to_excc_iff_reduces_in_atmost_k_stepsc; exrepnd.

      exists (Peano.max (k3 + k + k0) (k4 + k1 + k2)).
      right; dands; spcast.

      + apply (reduces_in_atmost_k_steps_excc_le_exc _ (k3 + k + k0));
        eauto 3 with slow; tcsp;
        try (apply NPeano.Nat.le_max_l; auto).
        pose proof (reduces_in_atmost_k_steps_excc_exception
                      lib k k0 n0 e0 (mkc_utoken a) mkc_axiom) as h.
        repeat (autodimp h hyp); tcsp; exrepnd.
        pose proof (reduces_in_atmost_k_steps_excc_trans2
                      lib k3 i
                      t1
                      (mkc_exception n0 e0)
                      (mkc_exception (mkc_utoken a) mkc_axiom)) as q.
        repeat (autodimp q hyp); exrepnd.
        apply (reduces_in_atmost_k_steps_excc_le_exc _ i0); tcsp; try omega.

      + apply (reduces_in_atmost_k_steps_excc_le_exc _ (k4 + k1 + k2));
        eauto 3 with slow; tcsp;
        try (apply NPeano.Nat.le_max_r; auto).
        pose proof (reduces_in_atmost_k_steps_excc_exception
                      lib k1 k2 n e (mkc_utoken a) mkc_axiom) as h.
        repeat (autodimp h hyp); tcsp; exrepnd.
        pose proof (reduces_in_atmost_k_steps_excc_trans2
                      lib k4 i
                      t2
                      (mkc_exception n e)
                      (mkc_exception (mkc_utoken a) mkc_axiom)) as q.
        repeat (autodimp q hyp); exrepnd.
        apply (reduces_in_atmost_k_steps_excc_le_exc _ i0); tcsp; try omega.
  }

  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in j; auto.

  { exrepnd.
    clear equ.
    pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t1) as q.
    pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t2) as h.

    destruct q as [q|q];destruct h as [h|h]; exrepnd.

    - destruct (dec_spexcc v0 a) as [d1|d1];
      destruct (dec_spexcc v a) as [d2|d2];
      subst.

      + right.
        apply reduces_in_atmost_k_steps_excc_decompose in h0; eauto 3 with slow.
        apply reduces_in_atmost_k_steps_excc_decompose in q0; eauto 3 with slow.
        exrepnd.
        allunfold @reduces_in_atmost_k_stepsc; allsimpl.
        allrw @get_cterm_mkc_exception; allsimpl.
        dands;
        apply cequiv_spexc_if;
        try (apply isprog_apply);
        try (apply isprog_mk_nat);
        eauto 3 with slow.
        * exists (get_cterm a') (get_cterm e'); dands; eauto 3 with slow.
          unfold computes_to_exception; exists k1; auto.
        * exists (get_cterm a'0) (get_cterm e'0); dands; eauto 3 with slow.
          unfold computes_to_exception; exists k0; auto.

     + provefalse.
       repndors; exrepnd; spcast.

       * eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact j0].
         subst; allsimpl.
         unfold iscanc in j1; allsimpl; tcsp.

       * eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0].
         subst; allsimpl; tcsp.

     + provefalse.
       repndors; exrepnd; spcast.

       * eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2].
         subst; allsimpl.
         unfold iscanc in j1; allsimpl; tcsp.

       * eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact j1].
         subst; allsimpl; tcsp.

     + left.
       exists v.
       dands; try (apply computes_to_valc_iff_reduces_in_atmost_k_stepsc; dands).

       * exists x.
         repndors; exrepnd; spcast.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst.
           eapply reduces_in_atmost_k_steps_excc_eq in j0;[|exact q0]; subst.
           apply reduces_in_atmost_k_steps_excc_can_implies; auto. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * apply iscanc_implies_iscvalue.
         destruct (dec_iscanc v) as [d|d]; auto.
         provefalse.
         repndors; exrepnd; spcast.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst.
           destruct d; eauto 3 with slow. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * exists x.
         repndors; exrepnd; spcast.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst.
           eapply reduces_in_atmost_k_steps_excc_eq in j0;[|exact q0]; subst.
           apply reduces_in_atmost_k_steps_excc_can_implies; auto. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * apply iscanc_implies_iscvalue.
         destruct (dec_iscanc v) as [d|d]; auto.
         provefalse.
         repndors; exrepnd; spcast.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst.
           destruct d; eauto 3 with slow. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * repndors; exrepnd; spcast; auto.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst; auto. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * repndors; exrepnd; spcast; auto.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst; auto. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

       * repndors; exrepnd; spcast; auto.

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j2]; subst; auto. }

         { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact j0]; subst; sp. }

    - provefalse.
      repndors; exrepnd; spcast; destruct h; eexists; eauto.

    - provefalse.
      repndors; exrepnd; spcast; destruct q; eexists; eauto.

    - provefalse.
      repndors; exrepnd; spcast; destruct q; eexists; eauto.
  }

  { clear j; introv.

    clear equ.

    pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t1) as h.
    pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t2) as q.

    destruct h as [h|h];
      destruct q as [q|q];
      exrepnd.

    - destruct (dec_spexcc v0 a) as [d1|d1];
      destruct (dec_spexcc v a) as [d2|d2];
      subst.

      + left; right; dands; spcast; auto.

      + right; intro xx; repndors; exrepnd; spcast.

        * eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx1].
          subst.
          unfold iscanc in xx0; allsimpl; tcsp.

        * eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
          subst; allsimpl; tcsp.

      + right; intro xx; repndors; exrepnd; spcast.

        * eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
          subst.
          unfold iscanc in xx0; allsimpl; tcsp.

        * eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx0].
          subst; allsimpl; tcsp.

      + destruct (dec_iscanc v0) as [g1|g1];
        destruct (dec_iscanc v) as [g2|g2].

        * destruct (decidable_noseqc v) as [ns|ns].

          { destruct (decidable_noconstc v) as [n|n].

            { destruct (dec_eq_cterms v v0 n) as [r|r]; subst; auto.

              - destruct (in_deq (get_patom_set o) (get_patom_deq o) a (getc_utokens v0)) as [i|i].

                + right; intro xx; repndors; exrepnd; spcast.

                  * eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx1].
                    eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
                    subst; allsimpl; tcsp.

                  * eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
                    subst; tcsp.

                + left; left.
                  exists v0; dands; spcast; auto.

              - right; intro xx; repndors; exrepnd; spcast.

                + eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx1].
                  eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
                  subst; allsimpl; tcsp.

                + eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
                  subst; tcsp.
            }

            { right; intro xx; repndors; exrepnd; spcast.

              - eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
                subst; allsimpl; tcsp.

              - eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
                subst; tcsp.
            }
          }

          { right; intro xx; repndors; exrepnd; spcast.

            - eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
              subst; allsimpl; tcsp.

            - eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
              subst; tcsp.
          }

        * right; intro xx; repndors; exrepnd; spcast.

          { eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx2].
            subst; allsimpl; tcsp. }

          { eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
            subst; tcsp. }

        * right; intro xx; repndors; exrepnd; spcast.

          { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx1].
            subst; allsimpl; tcsp. }

          { eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
            subst; tcsp. }

        * right; intro xx; repndors; exrepnd; spcast.

          { eapply reduces_in_atmost_k_steps_excc_eq in h0;[|exact xx1].
            subst; allsimpl; tcsp. }

          { eapply reduces_in_atmost_k_steps_excc_eq in q0;[|exact xx].
            subst; tcsp. }

    - right; intro xx; repndors; exrepnd; spcast; destruct q; eexists; eauto.

    - right; intro xx; repndors; exrepnd; spcast; destruct h; eexists; eauto.

    - right; intro xx; repndors; exrepnd; spcast; destruct h; eexists; eauto.
  }
Qed.

Lemma equality_in_nat2TE_implies {o} :
  forall lib (f g : @CTerm o) a T,
    eq_value_type_na lib a T
    -> equality lib f g (nat2TE a T)
    -> eq_fun2TE lib a (get_cterm f) (get_cterm g).
Proof.
  introv vT equ.
  apply equality_in_fun in equ; repnd.
  clear equ0 equ1.
  introv.
  pose proof (equ (mkc_nat n) (mkc_nat n)) as k.
  autodimp k hyp.
  { apply equality_in_tnat; unfold equality_of_nat.
    exists n; dands; spcast; apply computes_to_valc_refl;
    eauto 3 with slow. }

  apply equality_in_TE_implies in k; auto.
  repndors;[left|right].

  - unfold compute_to_eqvals_na in k; exrepnd.
    allunfold @computes_to_valc.
    allrw @get_cterm_apply; allsimpl.
    exists (get_cterm v) (get_cterm v); dands; auto.

  - allunfold @cequivc.
    allrw @get_cterm_apply; allsimpl.
    sp.
Qed.

Lemma eq_fun2TE_alpha_eq {o} :
  forall lib a (f f' g g' : @NTerm o),
    nt_wf f
    -> nt_wf g
    -> alpha_eq f f'
    -> alpha_eq g g'
    -> eq_fun2TE lib a f g
    -> eq_fun2TE lib a f' g'.
Proof.
  introv wff wfg aeq1 aeq2 e; introv.
  pose proof (e n) as h; clear e.
  repndors; exrepnd;[left|right].
  - eapply compute_to_value_alpha in h0;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ];
    eauto 4 with isprog.
    eapply compute_to_value_alpha in h2;
    [| |apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ];
    eauto 4 with isprog.
    exrepnd.
    exists t2'0 t2'.
    dands; eauto 4 with slow.
    apply alphaeq_preserves_utokens in h5; rw <- h5; auto.
  - eapply cequiv_rw_l_eauto in h0;
    [|apply implies_alpha_eq_mk_apply;[exact aeq1|apply alpha_eq_refl] ].
    eapply cequiv_rw_l_eauto in h;
    [|apply implies_alpha_eq_mk_apply;[exact aeq2|apply alpha_eq_refl] ].
    auto.
Qed.

(* XXXXXXXXXXXXXXXXX *)

Definition red_spexc_pair {o} lib a (t u : @NTerm o) :=
  isprog t
  # isprog u
  # reduces_to_exc lib t (spexc a)
  # reduces_to_exc lib u (spexc a).

Inductive differ_try {o} (a : get_patom_set o) (f g c : NTerm) : @NTerm o -> @NTerm o -> @NTerm o -> Type :=
| differ_try_base :
    forall arg1 arg2 arg3 x1 x2 x3 e1 e2 e3 z1 z2 z3 f' g' c',
      differ_try a f g c arg1 arg2 arg3
      -> alpha_eq f f'
      -> alpha_eq g g'
      -> alpha_eq c c'
      -> differ_try a f g c
                    (bound_nat_try_aux a arg1 x1 e1 z1 f' c')
                    (bound_nat_aux a arg2 x2 e2 z2 f')
                    (bound_nat_aux a arg3 x3 e3 z3 g')
| differ_try_exc :
    forall t e1 e2,
      spfexc_pair a e1 e2
      -> differ_try a f g c t e1 e2
| differ_try_var :
    forall v, differ_try a f g c (mk_var v) (mk_var v) (mk_var v)
| differ_try_sterm :
    forall s, differ_try a f g c (sterm s) (sterm s) (sterm s)
| differ_try_oterm :
    forall op bs1 bs2 bs3,
      length bs1 = length bs2
      -> length bs1 = length bs3
      -> !LIn a (get_utokens_o op)
      -> (forall b1 b2 b3,
            LIn (b1,b2,b3) (combine3 bs1 bs2 bs3)
            -> differ_try_b a f g c b1 b2 b3)
      -> differ_try a f g c (oterm op bs1) (oterm op bs2) (oterm op bs3)
with differ_try_b {o} (a : get_patom_set o) (f g c : NTerm) : @BTerm o -> @BTerm o -> @BTerm o -> Type :=
     | differ_try_bterm :
         forall vs t1 t2 t3,
           differ_try a f g c t1 t2 t3
           -> differ_try_b a f g c (bterm vs t1) (bterm vs t2) (bterm vs t3).
Hint Constructors differ_try differ_try_b.

Definition differ_try_alpha {o} a f g c (t1 t2 t3 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
   & {u3 : NTerm
   & alpha_eq t1 u1
   # alpha_eq t2 u2
   # alpha_eq t3 u3
   # differ_try a f g c u1 u2 u3}}}.

Definition br_list3 {T} R (l1 l2 l3 : list T) :=
  length l1 = length l2
  # length l1 = length l3
  # (forall a1 a2 a3,
       LIn (a1,a2,a3) (combine3 l1 l2 l3)
       -> R a1 a2 a3).

Definition br_bterms3 {o} R (bs1 bs2 bs3 : list (@BTerm o)) :=
  br_list3 R bs1 bs2 bs3.

Lemma br_bterms3_nil {o} :
  forall (R : @BTerm o -> @BTerm o -> @BTerm o -> Type),
    br_bterms3 R [] [] [].
Proof.
  introv.
  unfold br_bterms3, br_list3; simpl; sp.
Qed.
Hint Resolve br_bterms3_nil : slow.

Lemma br_bterms3_cons {o} :
  forall R (b1 b2 b3 : @BTerm o) bs1 bs2 bs3,
    R b1 b2 b3
    -> br_bterms3 R bs1 bs2 bs3
    -> br_bterms3 R (b1 :: bs1) (b2 :: bs2) (b3 :: bs3).
Proof.
  introv h1 h2.
  allunfold @br_bterms3.
  allunfold @br_list3; simpl; tcsp.
  repnd; dands; tcsp.
  introv i; dorn i; cpx; tcsp.
Qed.
Hint Resolve br_bterms3_cons : slow.

Lemma br_bterms3_cons_iff {o} :
  forall R (b1 b2 b3 : @BTerm o) bs1 bs2 bs3,
    br_bterms3 R (b1 :: bs1) (b2 :: bs2) (b3 :: bs3)
    <=> (R b1 b2 b3 # br_bterms3 R bs1 bs2 bs3).
Proof.
  introv.
  allunfold @br_bterms3.
  allunfold @br_list3.
  split; intro k; repnd; dands; allsimpl; cpx.
  introv i; dorn i; cpx; tcsp.
Qed.

Definition differ_try_bterms {o} a f g c (bs1 bs2 bs3 : list (@BTerm o)) :=
  br_bterms3 (differ_try_b a f g c) bs1 bs2 bs3.

Lemma differ_try_bterms_implies_eq_map_num_bvars {o} :
  forall a f g c (bs1 bs2 bs3 : list (@BTerm o)),
    differ_try_bterms a f g c bs1 bs2 bs3
    -> (map num_bvars bs1 = map num_bvars bs2
        # map num_bvars bs1 = map num_bvars bs3).
Proof.
  induction bs1; destruct bs2; destruct bs3; introv d; allsimpl; auto;
  allunfold @differ_try_bterms; allunfold @br_bterms3; allunfold @br_list3;
  allsimpl; repnd; cpx.
  pose proof (IHbs1 bs2 bs3) as q; clear IHbs1.
  repeat (autodimp q hyp); repnd.
  pose proof (d a0 b b0) as h; autodimp h hyp.
  inversion h; subst.
  dands; f_equal; auto.
Qed.

Lemma differ_try_bterms_cons {o} :
  forall a f g c (b1 b2 b3 : @BTerm o) bs1 bs2 bs3,
    differ_try_bterms a f g c (b1 :: bs1) (b2 :: bs2) (b3 :: bs3)
    <=> (differ_try_b a f g c b1 b2 b3 # differ_try_bterms a f g c bs1 bs2 bs3).
Proof.
  unfold differ_try_bterms; introv.
  rw @br_bterms3_cons_iff; sp.
Qed.

Lemma differ_try_bterms_nil {o} :
  forall a f g c, @differ_try_bterms o a f g c [] [] [].
Proof.
  unfold differ_try_bterms, br_bterms3, br_list3; simpl; sp.
Qed.
Hint Resolve differ_try_bterms_nil : slow.

Lemma differ_try_bterms_cons_if {o} :
  forall a f g c (b1 b2 b3 : @BTerm o) bs1 bs2 bs3,
    differ_try_b a f g c b1 b2 b3
    -> differ_try_bterms a f g c bs1 bs2 bs3
    -> differ_try_bterms a f g c (b1 :: bs1) (b2 :: bs2) (b3 :: bs3).
Proof.
  introv d1 d2; apply differ_try_bterms_cons; sp.
Qed.
Hint Resolve differ_try_bterms_cons_if : slow.

Definition differ_try_implies_differ_try_alpha {o} :
  forall a f g c (t1 t2 t3 : @NTerm o),
    differ_try a f g c t1 t2 t3 -> differ_try_alpha a f g c t1 t2 t3.
Proof.
  introv d.
  exists t1 t2 t3; auto.
Qed.
Hint Resolve differ_try_implies_differ_try_alpha : slow.

Inductive differ_try_subs {o} a f g c : @Sub o -> @Sub o -> @Sub o -> Type :=
| dsub_try_nil : differ_try_subs a f g c [] [] []
| dsub_try_cons :
    forall v t1 t2 t3 sub1 sub2 sub3,
      differ_try a f g c t1 t2 t3
      -> differ_try_subs a f g c sub1 sub2 sub3
      -> differ_try_subs a f g c ((v,t1) :: sub1) ((v,t2) :: sub2) ((v,t3) :: sub3).
Hint Constructors differ_try_subs.

Lemma differ_try_subs_sub_find_some {o} :
  forall a f g c (sub1 sub2 sub3 : @Sub o) v t,
    differ_try_subs a f g c sub1 sub2 sub3
    -> sub_find sub1 v = Some t
    -> {u2 : NTerm
        & {u3 : NTerm
        & sub_find sub2 v = Some u2
        # sub_find sub3 v = Some u3
        # differ_try a f g c t u2 u3}}.
Proof.
  induction sub1; destruct sub2; destruct sub3; introv d fs; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eauto.
Qed.

Lemma differ_try_subs_sub_find_none {o} :
  forall a f g c (sub1 sub2 sub3 : @Sub o) v,
    differ_try_subs a f g c sub1 sub2 sub3
    -> sub_find sub1 v = None
    -> (sub_find sub2 v = None # sub_find sub3 v = None).
Proof.
  induction sub1; destruct sub2; destruct sub3; introv d fn; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma map_combine3 :
   forall {T1 T2 T3 U1 U2 U3}
          (f: T1 -> U1)
          (g: T2 -> U2)
          (h: T3 -> U3)
          (l1: list T1)
          (l2: list T2)
          (l3: list T3),
     combine3 (map f l1) (map g l2) (map h l3)
     = map (fun x => (f (fst (fst x)), g (snd (fst x)), h (snd x))) (combine3 l1 l2 l3).
Proof.
  introv.
  unfold combine3.
  rw <- @map_combine.
  rw <- @map_combine; auto.
Qed.

Lemma in_combine3 :
  forall A B C a b c,
  forall l1 : list A,
  forall l2 : list B,
  forall l3 : list C,
     LIn (a,b,c) (combine3 l1 l2 l3)
    ->  LIn a l1 # LIn b l2 # LIn c l3.
Proof.
  introv i.
  repeat (allapply in_combine; repnd; tcsp).
Qed.

Lemma differ_try_subs_filter {o} :
  forall a f g c (sub1 sub2 sub3 : @Sub o) l,
    differ_try_subs a f g c sub1 sub2 sub3
    -> differ_try_subs a f g c (sub_filter sub1 l) (sub_filter sub2 l) (sub_filter sub3 l).
Proof.
  induction sub1; destruct sub2, sub3; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.
Hint Resolve differ_try_subs_filter : slow.

Lemma closed_lfresh {o} :
  forall vs (t : @NTerm o), closed t -> closed (lfresh vs t).
Proof.
  induction vs; introv cl; simpl; auto.
  unfold mk_fresh,closed; simpl.
  rw IHvs; auto.
Qed.
Hint Resolve closed_lfresh : slow.

Lemma cl_lsubst_aux_lfresh {o} :
  forall vs (t : @NTerm o) sub,
    closed t
    -> lsubst_aux (lfresh vs t) sub = lfresh vs t.
Proof.
  introv cl.
  rw @lsubst_aux_trivial_cl_term2; eauto with slow.
Qed.

Lemma lsubst_aux_spfexc {o} :
  forall vs1 vs2 (a : get_patom_set o) sub,
    lsubst_aux (spfexc vs1 vs2 a) sub = spfexc vs1 vs2 a.
Proof.
  introv; allsimpl; allrw @sub_filter_nil_r.
  repeat (rw @cl_lsubst_aux_lfresh; eauto 3 with slow).
Qed.

Lemma red_spexc_pair_isprog1 {o} :
  forall lib a (t1 t2 : @NTerm o),
    red_spexc_pair lib a t1 t2 -> isprog t1.
Proof.
  introv r; unfold red_spexc_pair in r; sp.
Qed.
Hint Resolve red_spexc_pair_isprog1 : slow.

Lemma red_spexc_pair_isprog2 {o} :
  forall lib a (t1 t2 : @NTerm o),
    red_spexc_pair lib a t1 t2 -> isprog t2.
Proof.
  introv r; unfold red_spexc_pair in r; sp.
Qed.
Hint Resolve red_spexc_pair_isprog2 : slow.

Lemma differ_try_lsubst_aux {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) sub1 sub2 sub3,
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try a f g c t1 t2 t3
    -> differ_try_subs a f g c sub1 sub2 sub3
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> disjoint (bound_vars t3) (sub_free_vars sub3)
    -> differ_try a f g c (lsubst_aux t1 sub1) (lsubst_aux t2 sub2) (lsubst_aux t3 sub3).
Proof.
  nterm_ind1s t1 as [v|s|op bs ind] Case;
  introv clf clg clc dt ds disj1 disj2 disj3; allsimpl.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    { allunfold @spfexc_pair; exrepnd; subst.
      allrw @lsubst_aux_spfexc; eauto 3 with slow. }
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ_try_subs_sub_find_some a f g c sub1 sub2 sub3) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ_try_subs_sub_find_none a f g c sub1 sub2 sub3) in Heqf1; auto.
      repnd; allrw; auto.

  - Case "sterm".
    inversion dt; subst; allsimpl; ginv; auto.
    allunfold @spfexc_pair; exrepnd; subst.
    allrw @lsubst_aux_spfexc; eauto 3 with slow.

  - Case "oterm".
    inversion dt as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      allrw @sub_find_sub_filter; tcsp.
      fold_terms.
      repeat (rw (lsubst_aux_trivial_cl_term2 f'); eauto 3 with slow;[]).
      repeat (rw (lsubst_aux_trivial_cl_term2 g'); eauto 3 with slow;[]).
      repeat (rw (lsubst_aux_trivial_cl_term2 c'); eauto 3 with slow;[]).
      apply differ_try_base; auto.

      apply (ind arg1 arg1 []); eauto 3 with slow.

    + allunfold @spfexc_pair; exrepnd; subst.
      allrw @lsubst_aux_spfexc; eauto 3 with slow.

    + apply differ_try_oterm; allrw map_length; auto.

      introv i.
      rw @map_combine3 in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      applydup imp in i1.
      destruct a2 as [l1 t1].
      destruct a1 as [l2 t2].
      destruct a0 as [l3 t3].
      applydup in_combine3 in i1; repnd.
      allsimpl.
      inversion i0 as [? ? ? ? d]; subst; clear i0.
      rename l3 into l.
      constructor; auto.
      disj_flat_map; allsimpl.
      allrw disjoint_app_l; repnd.
      apply (ind t1 t1 l); eauto 3 with slow.
Qed.

Lemma in_combine3_same :
  forall A (a1 a2 a3 : A) l,
    LIn (a1, a2, a3) (combine3 l l l) <=> (LIn a1 l # a2 = a1 # a3 = a1).
Proof.
  introv.
  induction l; allsimpl; split; introv k; repnd; tcsp.
  - repndors; ginv; tcsp.
    apply IHl in k; repnd; subst; sp.
  - subst; repndors; subst; tcsp.
    right; apply IHl; sp.
Qed.

Lemma differ_try_refl {o} :
  forall a f g c (t : @NTerm o),
    isprog f
    -> isprog g
    -> !LIn a (get_utokens t)
    -> differ_try a f g c t t t.
Proof.
  nterm_ind t as [v|s|op bs ind] Case; introv df dg nia; allsimpl; auto.

  Case "oterm".
  allrw in_app_iff; allrw not_over_or; repnd.
  apply differ_try_oterm; auto.
  introv i.
  rw in_combine3_same in i; repnd; subst.
  destruct b1 as [l t].
  constructor; auto.
  eapply ind; eauto.
  intro i; destruct nia; rw lin_flat_map; eexists; dands; eauto.
Qed.
Hint Resolve differ_try_refl : slow.

Lemma differ_try_alpha_refl {o} :
  forall a f g c (t : @NTerm o),
    isprog f
    -> isprog g
    -> !LIn a (get_utokens t)
    -> differ_try_alpha a f g c t t t.
Proof.
  introv ispf ispg nia.
  unfold differ_try_alpha.
  exists t t t; dands; eauto 3 with slow.
Qed.
Hint Resolve differ_try_alpha_refl : slow.

Lemma differ_try_subs_refl {o} :
  forall a f g c (sub : @Sub o),
    isprog f
    -> isprog g
    -> !LIn a (get_utokens_sub sub)
    -> differ_try_subs a f g c sub sub sub.
Proof.
  induction sub; introv df dg nia; allsimpl; auto.
  destruct a0.
  allrw @get_utokens_sub_cons; allrw in_app_iff; allrw not_over_or; repnd.
  repeat (autodimp IHsub hyp).
  constructor; eauto 3 with slow.
Qed.
Hint Resolve differ_try_subs_refl : slow.

Lemma alpha_eq_lfresh {o} :
  forall vs1 vs2 (t : @NTerm o),
    closed t
    -> length vs1 = length vs2
    -> alpha_eq (lfresh vs1 t) (lfresh vs2 t).
Proof.
  induction vs1; destruct vs2; introv cl len; allsimpl; auto; ginv; cpx.
  pose proof (ex_fresh_var (all_vars (lfresh vs1 t) ++ all_vars (lfresh vs2 t))) as fv; exrepnd.
  apply (implies_alpha_eq_mk_fresh_sub v); auto.
  eapply alpha_eq_trans;[apply alpha_eq_lsubst_closed;apply closed_lfresh;auto|].
  eapply alpha_eq_trans;[apply (IHvs1 vs2); auto|].
  apply alpha_eq_sym.
  apply alpha_eq_lsubst_closed.
  apply closed_lfresh; auto.
Qed.

Lemma alpha_eq_spfexc {o} :
  forall vs1 vs2 vs3 vs4 (a : get_patom_set o),
    length vs1 = length vs2
    -> length vs3 = length vs4
    -> length vs1 = length vs3
    -> alpha_eq (spfexc vs1 vs2 a) (spfexc vs3 vs4 a).
Proof.
  introv len1 len2 len3.
  unfold spfexc.
  apply implies_alphaeq_exception; apply alpha_eq_lfresh; eauto 3 with slow; try omega.
Qed.
Hint Resolve alpha_eq_spfexc : slow.

Lemma bound_vars_lfresh {o} :
  forall vs (t : @NTerm o),
    bound_vars (lfresh vs t) = vs ++ bound_vars t.
Proof.
  induction vs; introv; simpl; auto.
  allrw app_nil_r.
  rw IHvs; auto.
Qed.

Lemma bound_vars_spfexc {o} :
  forall vs1 vs2 (a : get_patom_set o),
    bound_vars (spfexc vs1 vs2 a) = vs1 ++ vs2.
Proof.
  introv; simpl.
  allrw @bound_vars_lfresh; allsimpl; allrw app_nil_r; auto.
Qed.

(* !!MOVE *)
Hint Resolve alphaeq_preserves_isnoncan_like : slow.
Hint Resolve alphaeq_preserves_isexc : slow.

Hint Resolve wf_exception : isprog.

Lemma reduces_int_atmost_k_steps_exc_alpha_eq {o} :
  forall lib k (t1 t2 t3 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t3
    -> reduces_in_atmost_k_steps_exc lib t1 t2 k
    -> {t4 : NTerm & reduces_in_atmost_k_steps_exc lib t3 t4 k # alpha_eq t2 t4}.
Proof.
  induction k; introv wf a r.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst.
    exists t3; dands; auto.
    rw @reduces_in_atmost_k_steps_exc_0; auto.

  - allrw @reduces_in_atmost_k_steps_exc_S.
    repndors; exrepnd; repndors; repnd; subst.

    + allapply @alpha_eq_exception; exrepnd; subst.
      allrw @nt_wf_eq; allrw @computation2.wf_exception_iff; repnd.
      eapply compute_step_alpha in r4;[| |exact a1]; exrepnd; eauto 3 with slow.

      applydup @alphaeq_preserves_wf_term in a1; auto.
      applydup @compute_step_preserves_wf in r2; auto.
      applydup @alphaeq_preserves_wf_term_inv in r0; auto.

      apply (IHk (mk_exception a' e') t2 (mk_exception a'0 t2')) in r1;
        try (apply implies_alphaeq_exception); auto; exrepnd; eauto 4 with isprog.
      exists t4; dands; auto.
      allrw @reduces_in_atmost_k_steps_exc_S; simpl; left.
      exists a'0 e'0 a'0 t2'; dands; auto.
      left; dands; eauto 3 with slow.

    + allapply @alpha_eq_exception; exrepnd; subst.
      allrw @nt_wf_eq; allrw @computation2.wf_exception_iff; repnd.
      eapply compute_step_alpha in r4;[| |exact a3]; exrepnd; eauto 4 with slow.

      applydup @alphaeq_preserves_wf_term in a3; auto.
      applydup @compute_step_preserves_wf in r2; auto.
      applydup @alphaeq_preserves_wf_term_inv in r0; auto.

      apply (IHk (mk_exception a' e') t2 (mk_exception t2' e'0)) in r1;
        try (apply implies_alphaeq_exception); auto; exrepnd; eauto 4 with isprog.
      exists t4; dands; auto.
      allrw @reduces_in_atmost_k_steps_exc_S; simpl; left.
      exists a'0 e'0 t2' e'0; dands; auto.
      right; dands; eauto 3 with slow.

    + eapply compute_step_alpha in r2;[| |exact a]; exrepnd; auto.

      applydup @alphaeq_preserves_wf_term in a; eauto 3 with slow.
      applydup @compute_step_preserves_wf in r2; auto.
      applydup @alphaeq_preserves_wf_term_inv in r3; auto.

      apply (IHk v t2 t2') in r1; auto; exrepnd; eauto 3 with slow.
      exists t4; dands; auto.
      allrw @reduces_in_atmost_k_steps_exc_S; simpl; right; dands; eauto 3 with slow.
      intro ise; destruct r0; eauto 3 with slow.
Qed.

Lemma reduces_to_exc_alpha_eq {o} :
  forall lib (t1 t2 t3 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t3
    -> reduces_to_exc lib t1 t2
    -> {t4 : NTerm & reduces_to_exc lib t3 t4 # alpha_eq t2 t4}.
Proof.
  introv wf aeq r.
  allunfold @reduces_to_exc; exrepnd.
  eapply reduces_int_atmost_k_steps_exc_alpha_eq in r0;[| |exact aeq];exrepnd; auto.
  exists t4; dands; auto.
  exists k; auto.
Qed.

Lemma alpha_eq_spexc {o} :
  forall (a : get_patom_set o) t,
    alpha_eq (spexc a) t
    -> t = spexc a.
Proof.
  introv aeq.
  apply alpha_eq_exception in aeq; exrepnd; subst.
  apply alpha_eq_mk_utoken in aeq2; subst.
  apply alpha_eq_mk_axiom in aeq1; subst; auto.
Qed.

Lemma red_spexc_pair_alpha_eq1 {o} :
  forall lib a (t1 t2 t3 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t3
    -> red_spexc_pair lib a t1 t2
    -> red_spexc_pair lib a t3 t2.
Proof.
  introv wf aeq r.
  allunfold @red_spexc_pair; repnd; dands; eauto 3 with slow.
  eapply reduces_to_exc_alpha_eq in r2;[| |exact aeq];exrepnd; auto.
  apply alpha_eq_spexc in r3; subst; auto.
Qed.

Lemma red_spexc_pair_alpha_eq2 {o} :
  forall lib a (t1 t2 t3 : @NTerm o),
    nt_wf t2
    -> alpha_eq t2 t3
    -> red_spexc_pair lib a t1 t2
    -> red_spexc_pair lib a t1 t3.
Proof.
  introv wf aeq r.
  allunfold @red_spexc_pair; repnd; dands; eauto 3 with slow.
  eapply reduces_to_exc_alpha_eq in r;[| |exact aeq];exrepnd; auto.
  apply alpha_eq_spexc in r3; subst; auto.
Qed.

Lemma null_eqset :
  forall {T} (l1 l2 : list T),
    eqset l1 l2
    -> null l1
    -> null l2.
Proof.
  introv e n i.
  apply e in i; apply n in i; sp.
Qed.

Lemma alpha_eq_lfresh_implies {o} :
  forall vs (t u : @NTerm o),
    closed t
    -> alpha_eq (lfresh vs t) u
    -> {vs' : list NVar
        & {t' : NTerm
        & u = lfresh vs' t'
        # length vs' = length vs
        # alpha_eq t t' }}.
Proof.
  induction vs; introv cl aeq; allsimpl.
  - exists ([] : list NVar) u; simpl; dands; auto.
  - apply alpha_eq_mk_fresh in aeq; exrepnd; subst.
    apply alphaeqbt_1v in aeq1; exrepnd; ginv.
    allrw disjoint_singleton_l.
    unfold var_ren in aeq0; allsimpl.

    eapply alpha_eq_trans in aeq0;
      [|apply alpha_eq_sym; apply alpha_eq_lsubst_closed; eauto 3 with slow].
    allrw in_app_iff; allrw not_over_or; repnd.
    rw @lsubst_trivial4 in aeq0; allsimpl;
    [|allrw disjoint_singleton_l; auto;
      introv i;
      apply alphaeq_preserves_free_vars in aeq0;
      rw @closed_lfresh in aeq0; auto;
      symmetry in aeq0; apply null_iff_nil in aeq0;
      eapply null_eqset in aeq0;[|apply eqset_free_vars_disjoint]; allsimpl;
      apply null_app in aeq0; repnd;
      boolvar; tcsp; allsimpl;
      apply null_cons in aeq0; sp
     |introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l; auto
    ].

    apply IHvs in aeq0; auto; exrepnd; subst.
    exists (v2 :: vs') t'; simpl; dands; auto.
Qed.

Lemma spfexc_pair_alpha_eq_l {o} :
  forall a (t1 t2 t3 : @NTerm o),
    alpha_eq t1 t3
    -> spfexc_pair a t1 t2
    -> spfexc_pair a t3 t2.
Proof.
  introv aeq spf.
  allunfold @spfexc_pair; exrepnd; subst.
  apply alpha_eq_exception in aeq; exrepnd; subst.
  apply alpha_eq_lfresh_implies in aeq1; eauto 3 with slow.
  apply alpha_eq_lfresh_implies in aeq2; eauto 3 with slow.
  exrepnd; subst.
  allapply @alpha_eq_mk_utoken; subst.
  allapply @alpha_eq_mk_axiom; subst.
  exists vs'0 vs' vs3 vs4; dands; auto; try omega.
Qed.

Lemma spfexc_pair_alpha_eq_r {o} :
  forall a (t1 t2 t3 : @NTerm o),
    alpha_eq t2 t3
    -> spfexc_pair a t1 t2
    -> spfexc_pair a t1 t3.
Proof.
  introv aeq spf.
  allunfold @spfexc_pair; exrepnd; subst.
  apply alpha_eq_exception in aeq; exrepnd; subst.
  apply alpha_eq_lfresh_implies in aeq1; eauto 3 with slow.
  apply alpha_eq_lfresh_implies in aeq2; eauto 3 with slow.
  exrepnd; subst.
  allapply @alpha_eq_mk_utoken; subst.
  allapply @alpha_eq_mk_axiom; subst.
  exists vs1 vs2 vs'0 vs'; dands; auto; try omega.
Qed.

Lemma differ_try_change_bound_vars {o} :
  forall a f g c vs (t1 t2 t3 : @NTerm o),
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try a f g c t1 t2 t3
    -> {u1 : NTerm
        & {u2 : NTerm
        & {u3 : NTerm
        & differ_try a f g c u1 u2 u3
        # alpha_eq t1 u1
        # alpha_eq t2 u2
        # alpha_eq t3 u3
        # disjoint (bound_vars u1) vs
        # disjoint (bound_vars u2) vs
        # disjoint (bound_vars u3) vs}}}.
Proof.
  nterm_ind1s t1 as [v|s ind|op bs ind] Case; introv ispf ispg ispc d.

  - Case "vterm".
    inversion d as [|? ? ? r|?|?|?]; subst.

    + pose proof (change_bvars_alpha_wspec vs t2) as h.
      destruct h as [t2' h]; repnd.
      pose proof (change_bvars_alpha_wspec vs t3) as q.
      destruct q as [t3' q]; repnd.
      eapply spfexc_pair_alpha_eq_l in r;[|exact h].
      eapply spfexc_pair_alpha_eq_r in r;[|exact q].
      exists (@vterm o v) t2' t3'; allsimpl; dands; eauto 3 with slow.

    + exists (@mk_var o v) (@mk_var o v) (@mk_var o v); simpl; dands; eauto 3 with slow.

  - Case "sterm".
    inversion d as [?|? ? ? spe|?|?|?]; subst; clear d.

    + pose proof (change_bvars_alpha_wspec vs t2) as h.
      destruct h as [t2' h]; repnd.
      pose proof (change_bvars_alpha_wspec vs t3) as q.
      destruct q as [t3' q]; repnd.
      eapply spfexc_pair_alpha_eq_l in spe;[|exact h].
      eapply spfexc_pair_alpha_eq_r in spe;[|exact q].
      exists (sterm s) t2' t3'; allsimpl; dands; eauto 3 with slow.

    + exists (sterm s) (sterm s) (sterm s); simpl; dands; auto.

  - Case "oterm".
    inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|? ? ? r|?|?|? ? ? ? len1 len2 nia imp];
      subst; simphyps; cpx; ginv; clear d;[|idtac|]; fold_terms.

    + allfold (bound_nat_try_aux a arg1 x1 e1 z1 f').
      pose proof (ind arg1 arg1 []) as h; clear ind.
      repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (h arg2 arg3 ispf ispg ispc d1) as q; clear h.
      exrepnd.

      pose proof (ex_fresh_var vs) as fv.
      destruct fv as [v fv].

      pose proof (change_bvars_alpha_wspec vs f) as cf.
      destruct cf as [f'' cf].
      pose proof (change_bvars_alpha_wspec vs g) as cg.
      destruct cg as [g'' cg].
      pose proof (change_bvars_alpha_wspec vs c) as ct.
      destruct ct as [c'' ct].

      exists (bound_nat_try_aux a u1 v v v f'' c'')
             (bound_nat_aux a u2 v v v f'')
             (bound_nat_aux a u3 v v v g'').
      simpl; allrw app_nil_r.
      allrw disjoint_app_l.
      allrw disjoint_cons_l.
      allrw disjoint_app_l.
      allrw disjoint_cons_l.
      allrw disjoint_singleton_l.
      repnd; dands; eauto 3 with slow.

      { apply alpha_eq_bound_nat_try_aux; eauto 3 with slow. }
      { apply alpha_eq_bound_nat_aux; eauto 3 with slow. }
      { apply alpha_eq_bound_nat_aux; eauto 3 with slow. }

    + pose proof (change_bvars_alpha_wspec vs (oterm op bs)) as ct.
      destruct ct as [t ct]; repnd.
      pose proof (change_bvars_alpha_wspec vs t2) as h.
      destruct h as [t2' h]; repnd.
      pose proof (change_bvars_alpha_wspec vs t3) as q.
      destruct q as [t3' q]; repnd.
      eapply spfexc_pair_alpha_eq_l in r;[|exact h].
      eapply spfexc_pair_alpha_eq_r in r;[|exact q].
      exists t t2' t3'; allsimpl; dands; eauto 3 with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
               & {bs3' : list BTerm
               & alpha_eq_bterms bs bs'
               # alpha_eq_bterms bs2 bs2'
               # alpha_eq_bterms bs3 bs3'
               # differ_try_bterms a f g c bs' bs2' bs3'
               # disjoint (bound_vars_bterms bs') vs
               # disjoint (bound_vars_bterms bs2') vs
               # disjoint (bound_vars_bterms bs3') vs}}}) as h.

      { revert dependent bs3.
        revert dependent bs2.
        induction bs; destruct bs2; introv len1; destruct bs3; introv len2 imp; allsimpl; ginv.
        - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)) ([] : list (@BTerm o));
            dands; simpl; eauto 3 with slow; try (apply br_bterms_nil).
        - cpx.
          destruct a0 as [l1 t1].
          destruct b as [l2 t2].
          destruct b0 as [l3 t3].
          pose proof (imp (bterm l1 t1) (bterm l2 t2) (bterm l3 t3)) as h; autodimp h hyp.
          inversion h as [? ? ? ? d1]; subst; clear h.
          rename l3 into l.
          pose proof (ind t1 t1 l) as h; repeat (autodimp h hyp); eauto 3 with slow.
          pose proof (h t2 t3 ispf ispg ispc d1) as k; clear h.
          exrepnd.

          autodimp IHbs hyp.
          { introv i d; eapply ind; eauto. }
          pose proof (IHbs bs2) as k; clear IHbs ind.
          repeat (autodimp k hyp).
          pose proof (k bs3) as q; clear k.
          repeat (autodimp q hyp).
          exrepnd.

          pose proof (fresh_vars
                        (length l)
                        (vs
                           ++ l
                           ++ all_vars t1
                           ++ all_vars t2
                           ++ all_vars t3
                           ++ all_vars u1
                           ++ all_vars u2
                           ++ all_vars u3
                           ++ all_vars f
                           ++ all_vars g
                        )) as fv; exrepnd.
          allrw disjoint_app_r; repnd.

          exists ((bterm lvn (lsubst_aux u1 (var_ren l lvn))) :: bs')
                 ((bterm lvn (lsubst_aux u2 (var_ren l lvn))) :: bs2')
                 ((bterm lvn (lsubst_aux u3 (var_ren l lvn))) :: bs3');
            dands; simpl;
            try (apply br_bterms_cons);
            try (apply br_bterms3_cons);
            try (apply alpha_eq_bterm_congr);
            tcsp.
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply differ_try_bterm; auto.
            apply differ_try_lsubst_aux; eauto 3 with slow;
            try (rw @sub_free_vars_var_ren; eauto 3 with slow);
            try (rw @dom_sub_var_ren; eauto 3 with slow).
            apply differ_try_subs_refl; simpl;
            allrw @get_utokens_sub_var_ren; tcsp;
            try (rw @sub_bound_vars_var_ren; auto). }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u1 (var_ren l lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u2 (var_ren l lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u3 (var_ren l lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
      }

      exrepnd.
      applydup @alpha_eq_bterms_implies_same_length in h1.
      applydup @alpha_eq_bterms_implies_same_length in h2.
      applydup @alpha_eq_bterms_implies_same_length in h3.
      exists (oterm op bs') (oterm op bs2') (oterm op bs3'); dands; eauto 3 with slow.

      * apply differ_try_oterm; tcsp; try omega.
        apply h4.

      * apply alpha_eq_oterm_combine; dands; auto.
        apply h1.

      * apply alpha_eq_oterm_combine; dands; auto.
        apply h2.

      * apply alpha_eq_oterm_combine; dands; auto.
        apply h3.
Qed.

Lemma differ_try_lsubst {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) sub1 sub2 sub3,
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try a f g c t1 t2 t3
    -> differ_try_subs a f g c sub1 sub2 sub3
    -> differ_try_alpha a f g c (lsubst t1 sub1) (lsubst t2 sub2) (lsubst t3 sub3).
Proof.
  introv ispf ispg ispc dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  pose proof (unfold_lsubst sub3 t3) as q; exrepnd.
  rw h0; rw k0; rw q0.

  pose proof (differ_try_change_bound_vars
                a f g c (sub_free_vars sub1 ++ sub_free_vars sub2 ++ sub_free_vars sub3)
                t1 t2 t3 ispf ispg ispc dt) as d; exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2) (lsubst_aux u3 sub3); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto 3 with slow.

  - apply lsubst_aux_alpha_congr2; eauto 3 with slow.

  - apply lsubst_aux_alpha_congr2; eauto 3 with slow.

  - apply differ_try_lsubst_aux; auto.
Qed.
Hint Resolve differ_try_lsubst : slow.

Lemma differ_try_subst {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) v u1 u2 u3,
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try a f g c t1 t2 t3
    -> differ_try a f g c u1 u2 u3
    -> differ_try_alpha a f g c (subst t1 v u1) (subst t2 v u2) (subst t3 v u3).
Proof.
  introv ispf ispg ispc dt ds.
  apply differ_try_lsubst; auto.
Qed.
Hint Resolve differ_try_subst : slow.

Lemma cbv_subst_bound_nat_try_aux_alpha_eq {o} :
  forall a v z e (f : @NTerm o) t u,
    isprog f
    -> isprog u
    -> alpha_eq (subst
                   (mk_less (mk_var v) mk_zero (mk_vbot z)
                            (mk_try (mk_apply f (mk_var v)) (mk_utoken a) e u))
                   v
                   t)
                (mk_less t mk_zero (mk_vbot z)
                         (mk_try (mk_apply f t) (mk_utoken a) e u)).
Proof.
  introv isp ispu.
  pose proof (unfold_lsubst
                [(v,t)]
                (mk_less (mk_var v) mk_zero (mk_vbot z)
                         (mk_try (mk_apply f (mk_var v)) (mk_utoken a) e u)))
    as unf; exrepnd.
  unfold subst.
  rw unf0; clear unf0.
  allapply @alpha_eq_mk_less; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.
  allapply @alpha_eq_mk_vbot; exrepnd; subst.
  allapply @alpha_eq_mk_zero; subst.
  allapply @alpha_eq_mk_ntry; exrepnd; subst.
  allapply @alpha_eq_mk_utoken; subst.
  allapply @alpha_eq_mk_apply; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.
  allapply @alpha_eq_bterm_mk_zero; exrepnd; allsimpl; cpx; ginv.

  allrw app_nil_r.
  allrw disjoint_cons_l.
  allrw disjoint_app_l.
  allrw disjoint_cons_l.
  repnd.

  rename a'0 into f'.
  rename a' into u'.
  pose proof (ex_fresh_var (bound_vars u ++ bound_vars u')) as fv; exrepnd.
  allrw in_app_iff; allrw not_over_or; repnd.

  applydup @closed_if_isprog in ispu as clu.
  apply (alpha_eq_bterm_trans (bterm [v'0] u)) in unf1;
    [apply alpha_eq_bterm_triv in unf1|];
    [|apply (al_bterm_aux [v0]); simpl; auto;
      [unfold all_vars; rw clu; simpl; apply disjoint_singleton_l; rw in_app_iff; sp
      |];
      repeat (rw @lsubst_aux_trivial_cl_term2; auto)];[].

  assert (closed u') as clu'.
  { eauto 3 with slow. }

  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  rw (@lsubst_aux_trivial_cl_term2 o u'); eauto 3 with slow.
  rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.

  unfold mk_less, mk_try, mk_apply, mk_utoken, mk_vbot, nobnd.
  repeat (prove_alpha_eq4; eauto 2 with slow).

  { pose proof (ex_fresh_var (v' :: z :: [])) as fv.
    exrepnd; allsimpl; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;
    repeat (boolvar; simpl); tcsp;
    allrw disjoint_singleton_l; allsimpl; tcsp. }

  apply (al_bterm_aux [v0]); allsimpl; tcsp.
  { unfold all_vars.
    rw clu; rw clu'; simpl.
    apply disjoint_singleton_l; rw in_app_iff; sp. }
  rw (@lsubst_aux_trivial_cl_term2 o u'); eauto 3 with slow.
  rw (@lsubst_aux_trivial_cl_term2 o u); eauto 3 with slow.
Qed.

Lemma alpha_eq_mk_integer {o} :
  forall i (u : @NTerm o),
    alpha_eq (mk_integer i) u
    -> u = mk_integer i.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
Qed.

Lemma closed_mk_integer {o} :
  forall i, @closed o (mk_integer i).
Proof. sp. Qed.
Hint Resolve closed_mk_integer : slow.

Lemma closed_mk_nat {o} :
  forall i, @closed o (mk_nat i).
Proof. sp. Qed.
Hint Resolve closed_mk_nat : slow.

Lemma reduces_to_bound_nat_aux_nat {o} :
  forall lib a n x e z (f : @NTerm o),
    isprog f
    -> reduces_to
         lib
         (bound_nat_aux a (mk_nat n) x e z f)
         (mk_try (mk_apply f (mk_nat n))
                 (mk_utoken a)
                 e
                 (spexc a)).
Proof.
  introv isp.

  eapply reduces_to_if_split2;[csunf;simpl;auto|].
  unfold apply_bterm; simpl; fold_terms.
  unflsubst; simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  fold_terms.

  eapply reduces_to_if_split2;
    [csunf;simpl;dcwf h; simpl; unfold compute_step_comp;simpl;auto|];[].
  match goal with
    | [ |- context[mk_fix ?x] ] => remember (mk_fix x) as b
  end; clear Heqb.
  boolvar; tcsp; try omega.

  rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow.
Qed.

Lemma if_has_value_like_k_ncompop_can_same {o} :
  forall lib c k (t : @NTerm o) a b,
    wf_term t
    -> wf_term a
    -> wf_term b
    -> has_value_like_k
         lib k
         (oterm (NCan (NCompOp c)) [nobnd t, nobnd t, nobnd a, nobnd b])
    -> {j : nat
        & {u : NTerm
        & j < k
        # reduces_in_atmost_k_steps lib t u j
        # (ispk u [+] isexc u)}}.
Proof.
  introv wft wfa wfb hv.
  unfold has_value_like_k in hv; exrepnd.
  apply computes_to_val_like_in_max_k_steps_comp_implies in hv0; auto;[].
  repndors; exrepnd; subst.

  - exists k1 (pk2term pk1); dands; eauto 3 with slow; try omega.

  - exists k1 (mk_exception en e); dands; eauto 3 with slow; try omega.

  - exists k2 (mk_exception en e); dands; eauto 3 with slow; try omega.
Qed.

Lemma alpha_eq_pk2term {o} :
  forall (pk : @param_kind o) t,
    alpha_eq (pk2term pk) t
    -> t = pk2term pk.
Proof.
  introv aeq.
  inversion aeq; ginv; allrw @pk2term_eq; ginv.
  allsimpl; cpx.
Qed.

Lemma get_utokens_c_pk2can {o} :
  forall (pk : @param_kind o),
    get_utokens_c (pk2can pk) = get_utokens_pk pk.
Proof.
  introv; destruct pk; simpl; auto.
Qed.

Lemma differ_try_pk2term {o} :
  forall a f g c (pk : @param_kind o) t u,
    differ_try a f g c (pk2term pk) t u
    -> ((t = pk2term pk # u = pk2term pk # !LIn a (get_utokens_pk pk))
        [+] spfexc_pair a t u).
Proof.
  introv d.
  inversion d as [|? ? ? r|?|?|? ? ? ? len1 len2 nia imp];
    subst; allsimpl; clear d; GC; tcsp; ginv;
    allrw @pk2term_eq; ginv.
  allsimpl; cpx.
  allrw @get_utokens_c_pk2can; tcsp.
Qed.

Lemma differ_try_alpha_pk2term {o} :
  forall a f g c (pk : @param_kind o) t u,
    differ_try_alpha a f g c (pk2term pk) t u
    -> ((t = pk2term pk # u = pk2term pk # !LIn a (get_utokens_pk pk))
        [+] spfexc_pair a t u).
Proof.
  introv d.
  unfold differ_try_alpha in d; exrepnd.
  allapply @alpha_eq_pk2term; subst.
  allapply @differ_try_pk2term; repndors; repnd; subst.
  - apply alpha_eq_sym in d3; apply alpha_eq_pk2term in d3.
    apply alpha_eq_sym in d2; apply alpha_eq_pk2term in d2.
    subst; tcsp.
  - eapply spfexc_pair_alpha_eq_l in d0;[|apply alpha_eq_sym;exact d2].
    eapply spfexc_pair_alpha_eq_r in d0;[|apply alpha_eq_sym;exact d3].
    tcsp.
Qed.

Lemma differ_try_integer {o} :
  forall a f g c i (t u : @NTerm o),
    differ_try a f g c (mk_integer i) t u
    -> ((t = mk_integer i # u = mk_integer i)
        [+] spfexc_pair a t u).
Proof.
  introv d.
  inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp];
    subst; allsimpl; clear d; GC; tcsp; ginv.
  allsimpl; cpx.
Qed.

Lemma differ_try_alpha_integer {o} :
  forall a f g c i (t u : @NTerm o),
    differ_try_alpha a f g c (mk_integer i) t u
    -> ((t = mk_integer i # u = mk_integer i)
        [+] spfexc_pair a t u).
Proof.
  introv d.
  unfold differ_try_alpha in d; exrepnd.
  allapply @alpha_eq_mk_integer; subst.
  allapply @differ_try_integer; repndors; repnd; subst.
  - apply alpha_eq_sym in d3; apply alpha_eq_mk_integer in d3.
    apply alpha_eq_sym in d2; apply alpha_eq_mk_integer in d2.
    subst; tcsp.
  - eapply spfexc_pair_alpha_eq_l in d0;[|apply alpha_eq_sym;exact d2].
    eapply spfexc_pair_alpha_eq_r in d0;[|apply alpha_eq_sym;exact d3].
    tcsp.
Qed.

Lemma differ_try_alpha_nat {o} :
  forall a f g c i (t u : @NTerm o),
    differ_try_alpha a f g c (mk_nat i) t u
    -> ((t = mk_nat i # u = mk_nat i)
        [+] spfexc_pair a t u).
Proof.
  introv d.
  allunfold @mk_nat.
  apply differ_try_alpha_integer in d; sp.
Qed.

Lemma wf_isexc_implies {o} :
  forall (t : @NTerm o),
    isexc t
    -> wf_term t
    -> {a : NTerm
        & {e : NTerm
        & t = mk_exception a e
        # wf_term a
        # wf_term e}}.
Proof.
  introv ise wf.
  apply isexc_implies2 in ise; exrepnd; subst.
  allapply @wf_exception_implies; exrepnd; subst.
  exists a t; auto.
Qed.

Lemma differ_try_exception {o} :
  forall a f g c (n e t u : @NTerm o),
    differ_try a f g c (mk_exception n e) t u
    -> ({n1 : NTerm
         & {n2 : NTerm
         & {e1 : NTerm
         & {e2 : NTerm
         & t = mk_exception n1 e1
         # u = mk_exception n2 e2
         # differ_try a f g c n n1 n2
         # differ_try a f g c e e1 e2}}}}
        [+] spfexc_pair a t u).
Proof.
  introv d.
  inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; tcsp.
  allsimpl; cpx; GC; allsimpl.
  pose proof (imp (nobnd n) x0 x) as h1; autodimp h1 hyp.
  pose proof (imp (nobnd e) y0 y) as h2; autodimp h2 hyp.
  clear imp.
  inversion h1 as [? ? ? ? d1]; subst; clear h1.
  inversion h2 as [? ? ? ? d2]; subst; clear h2.
  fold_terms.
  left.
  eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma differ_try_alpha_exception {o} :
  forall a f g c (n e t u : @NTerm o),
    differ_try_alpha a f g c (mk_exception n e) t u
    -> ({n1 : NTerm
         & {n2 : NTerm
         & {e1 : NTerm
         & {e2 : NTerm
         & t = mk_exception n1 e1
         # u = mk_exception n2 e2
         # differ_try_alpha a f g c n n1 n2
         # differ_try_alpha a f g c e e1 e2}}}}
        [+] spfexc_pair a t u).
Proof.
  introv d.
  unfold differ_try_alpha in d; exrepnd.
  allapply @alpha_eq_exception; exrepnd; subst.
  allapply @differ_try_exception; exrepnd.

  repndors; exrepnd; subst; tcsp.

  - apply alpha_eq_sym in d2; apply alpha_eq_exception in d2.
    apply alpha_eq_sym in d3; apply alpha_eq_exception in d3.
    exrepnd; subst.
    left.
    eexists; eexists; eexists; eexists; dands; auto.

    + exists a' n1 n2; dands; eauto 3 with slow.

    + exists e' e1 e2; dands; eauto 3 with slow.

  - eapply spfexc_pair_alpha_eq_l in d0;[|apply alpha_eq_sym;exact d2].
    eapply spfexc_pair_alpha_eq_r in d0;[|apply alpha_eq_sym;exact d3].
    tcsp.
Qed.

Lemma implies_differ_try_alpha_exception {o} :
  forall a f g c (n1 n2 n3 e1 e2 e3 : @NTerm o),
    differ_try_alpha a f g c n1 n2 n3
    -> differ_try_alpha a f g c e1 e2 e3
    -> differ_try_alpha
         a f g c
         (mk_exception n1 e1)
         (mk_exception n2 e2)
         (mk_exception n3 e3).
Proof.
  introv d1 d2.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_exception u0 u1) (mk_exception u4 u2) (mk_exception u5 u3).
  dands; eauto 3 with slow; try (apply implies_alphaeq_exception; auto).
  apply differ_try_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; auto.
Qed.

Lemma implies_alpha_eq_compop {o} :
  forall c (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq c1 c2
    -> alpha_eq d1 d2
    -> alpha_eq
         (mk_compop c a1 b1 c1 d1)
         (mk_compop c a2 b2 c2 d2).
Proof.
  introv aeq1 aeq2 aeq3 aeq4.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; ginv; tcsp; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_differ_try_alpha_compop {o} :
  forall a f g d c (a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : @NTerm o),
    differ_try_alpha a f g d a1 a2 a3
    -> differ_try_alpha a f g d b1 b2 b3
    -> differ_try_alpha a f g d c1 c2 c3
    -> differ_try_alpha a f g d d1 d2 d3
    -> differ_try_alpha
         a f g d
         (mk_compop c a1 b1 c1 d1)
         (mk_compop c a2 b2 c2 d2)
         (mk_compop c a3 b3 c3 d3).
Proof.
  introv diff1 diff2 diff3 diff4.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_compop c u9 u6 u0 u1) (mk_compop c u10 u7 u4 u2) (mk_compop c u11 u8 u5 u3).
  dands; eauto 3 with slow; try (apply implies_alpha_eq_compop; auto).
  apply differ_try_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; auto.
Qed.

Lemma implies_alpha_eq_arithop {o} :
  forall c (a1 a2 b1 b2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq
         (mk_arithop c a1 b1)
         (mk_arithop c a2 b2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; ginv; tcsp; apply alphaeqbt_nilv2; auto.
Qed.

Lemma implies_differ_try_alpha_arithop {o} :
  forall a f g d c (a1 a2 a3 b1 b2 b3 : @NTerm o),
    differ_try_alpha a f g d a1 a2 a3
    -> differ_try_alpha a f g d b1 b2 b3
    -> differ_try_alpha
         a f g d
         (mk_arithop c a1 b1)
         (mk_arithop c a2 b2)
         (mk_arithop c a3 b3).
Proof.
  introv diff1 diff2.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_arithop c u0 u1) (mk_arithop c u4 u2) (mk_arithop c u5 u3).
  dands; eauto 3 with slow; try (apply implies_alpha_eq_arithop; auto).
  apply differ_try_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; auto.
Qed.

Lemma wf_term_cantest_iff {o} :
  forall test (bs : list (@BTerm o)),
    wf_term (oterm (NCan (NCanTest test)) bs)
    <=> {a, b, c : NTerm
         $ bs = [bterm [] a, bterm [] b, bterm [] c]
         # wf_term a
         # wf_term b
         # wf_term c}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; cpx).
    destruct b as [l1 t1]; destruct b0 as [l2 t2]; destruct b1 as [l3 t3].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2, l3; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    pose proof (k (bterm [] t3)) as h3; autodimp h3 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2 t3; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma differ_try_ncan_ncan {o} :
  forall a f g c nc nc' bs' bs (t u : @NTerm o),
    differ_try a f g c (oterm (NCan nc) (bterm [] (oterm (NCan nc') bs') :: bs)) t u
    -> ({t1 : NTerm
         & {t2 : NTerm
         & {bs1 : list BTerm
         & {bs2 : list BTerm
         & t = oterm (NCan nc) (nobnd t1 :: bs1)
         # u = oterm (NCan nc) (nobnd t2 :: bs2)
         # differ_try a f g c (oterm (NCan nc') bs') t1 t2}}}}
        [+] spfexc_pair a t u).
Proof.
  introv d.
  inversion d as [? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|?|?|?|? ? ? ? len1 len2 nia imp];
    subst; allsimpl; clear d; GC; tcsp;[|].

  - left.
    unfold bound_nat_aux, mk_cbv.
    eexists; eexists; eexists; eexists; dands; eauto.

  - left.
    destruct bs2, bs3; allsimpl; cpx.
    allsimpl.
    pose proof (imp (nobnd (oterm (NCan nc') bs')) b b0) as d1; autodimp d1 hyp.
    inversion d1 as [? ? ? ? d2]; subst; clear d1.
    unfold nobnd.
    eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma differ_try_ncan_abs {o} :
  forall a f g c nc abs bs' bs (t u : @NTerm o),
    differ_try a f g c (oterm (NCan nc) (bterm [] (oterm (Abs abs) bs') :: bs)) t u
    -> ({t1 : NTerm
         & {t2 : NTerm
         & {bs1 : list BTerm
         & {bs2 : list BTerm
         & t = oterm (NCan nc) (nobnd t1 :: bs1)
         # u = oterm (NCan nc) (nobnd t2 :: bs2)
         # differ_try a f g c (oterm (Abs abs) bs') t1 t2}}}}
        [+] spfexc_pair a t u).
Proof.
  introv d.
  inversion d as [? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|?|?|?|? ? ? ? len1 len2 nia imp];
    subst; allsimpl; clear d; GC; tcsp;[|].

  - left.
    unfold bound_nat_aux, mk_cbv.
    eexists; eexists; eexists; eexists; dands; eauto.

  - left.
    destruct bs2, bs3; allsimpl; cpx.
    allsimpl.
    pose proof (imp (nobnd (oterm (Abs abs) bs')) b b0) as d1; autodimp d1 hyp.
    inversion d1 as [? ? ? ? d2]; subst; clear d1.
    unfold nobnd.
    eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma has_value_like_k_reduces_to {o} :
  forall lib (t : @NTerm o) u k,
    reduces_to lib t u
    -> has_value_like_k lib k t
    -> {j : nat & j <= k # has_value_like_k lib j u}.
Proof.
  introv r hv.
  unfold has_value_like_k, computes_to_val_like_in_max_k_steps in hv; exrepnd.
  eapply reduces_in_atmost_k_steps_if_reduces_to in hv1; eauto.
  exrepnd.
  exists k'; dands; auto.
  exists u0.
  unfold computes_to_val_like_in_max_k_steps; dands; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_vbot {o} :
  forall lib k z (t : @NTerm o),
    !computes_to_val_like_in_max_k_steps lib (mk_vbot z) t k.
Proof.
  introv comp.
  unfold computes_to_val_like_in_max_k_steps in comp; repnd.
  apply reduces_in_atmost_k_steps_vbot in comp0; tcsp.
Qed.

Lemma computes_to_exception_in_max_k_steps_0 {o} :
  forall lib (a t v : @NTerm o),
    computes_to_exception_in_max_k_steps lib a t v 0
    <=> t = mk_exception a v.
Proof.
  introv.
  unfold computes_to_exception_in_max_k_steps.
  rw @reduces_in_atmost_k_steps_0; sp.
Qed.

Lemma hasvalue_like_subst_less_seq {o} :
  forall lib (f : @ntseq o) v a b c u k,
    computes_to_val_like_in_max_k_steps
      lib
      (subst (mk_less (mk_var v) a b c) v (sterm f))
      u
      k
    -> False.
Proof.
  introv comp.
  unfold subst, lsubst in comp; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  destruct k.

  - allrw @computes_to_val_like_in_max_k_steps_0; repnd; subst.
    unfold isvalue_like in comp; allsimpl; tcsp.

  - allrw @computes_to_val_like_in_max_k_steps_S; exrepnd.
    csunf comp1; allsimpl; ginv.
Qed.

Lemma has_value_like_k_subst_less_seq {o} :
  forall lib (f : @ntseq o) v a b c k,
    has_value_like_k
      lib
      k
      (subst (mk_less (mk_var v) a b c) v (sterm f))
    -> False.
Proof.
  introv comp.
  unfold subst, lsubst in comp; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  destruct k.

  - allrw @has_value_like_0; repnd; subst.
    unfold isvalue_like in comp; allsimpl; tcsp.

  - allrw @has_value_like_S; exrepnd.
    csunf comp1; allsimpl; ginv.
Qed.

Lemma has_value_like_k_bound_nat_try_aux {o} :
  forall lib k a (arg : @NTerm o) x e z f t,
    isprog f
    -> isprog t
    -> wf_term arg
    -> has_value_like_k lib k (bound_nat_try_aux a arg x e z f t)
    -> {j : nat
        & j < k
        # ({n : nat & reduces_in_atmost_k_steps lib arg (mk_nat n) j}
           [+] {n : NTerm
                & {e : NTerm
                & computes_to_exception_in_max_k_steps lib n arg e j}})}.
Proof.
  introv isp ispt wf hv.
  unfold has_value_like_k in hv; exrepnd.
  revert dependent arg.
  induction k; introv wf comp.

  - allrw @computes_to_val_like_in_max_k_steps_0; repnd; subst.
    unfold isvalue_like in comp; allsimpl; tcsp.

  - allrw @computes_to_val_like_in_max_k_steps_S; exrepnd.
    destruct arg as [v|s|op bs].

    + csunf comp1; allsimpl; ginv.

    + csunf comp1; allsimpl; ginv.
      allunfold @apply_bterm; allsimpl; allrw @fold_subst.
      apply hasvalue_like_subst_less_seq in comp0; sp.

    + dopid op as [can|ncan|exc|abs] Case.

      * Case "Can".
        csunf comp1; allsimpl; ginv.
        unfold apply_bterm in comp0; allsimpl; allrw @fold_subst.
        pose proof (cbv_subst_bound_nat_try_aux_alpha_eq a x z e f (oterm (Can can) bs) t) as h.
        repeat (autodimp h hyp).
        eapply alphaeq_preserves_computes_to_val_like_in_max_k_steps in comp0;[| |exact h];
        [|apply nt_wf_subst; eauto 3 with slow;
          apply nt_wf_eq; apply wf_less; eauto 3 with slow;
          apply wf_try; eauto 3 with slow;
          apply wf_apply; eauto 3 with slow].

        exrepnd; clear h.
        apply computes_to_val_like_in_max_k_steps_comp_implies in comp0; eauto 3 with slow;
        [|apply wf_try_iff; dands; eauto 3 with slow;
          apply wf_apply_iff; dands; eauto 3 with slow];[].
        repndors; exrepnd; repndors; exrepnd; subst; ginv; boolvar; allsimpl.

        { apply computes_to_val_like_in_max_k_steps_vbot in comp6; tcsp. }

        { allunfold @computes_to_can_in_max_k_steps; repnd.
          apply reduces_in_atmost_k_steps_if_isvalue_like in comp7; eauto 3 with slow.
          apply reduces_in_atmost_k_steps_if_isvalue_like in comp2; eauto 3 with slow.
          unfold mk_zero, mk_nat in comp7; ginv.
          unfold mk_integer in comp2; ginv; fold_terms.
          pose proof (Wf_Z.Z_of_nat_complete_inf i1) as hi1; autodimp hi1 hyp; exrepnd; subst.
          fold_terms.
          exists 0; dands; tcsp; try omega.
          left.
          exists n.
          rw @reduces_in_atmost_k_steps_0; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { apply computes_to_exception_in_max_k_steps_can in comp6; tcsp. }

      * Case "NCan".
        unfold bound_nat_try_aux in comp1.
        rw @compute_step_mk_cbv_ncan in comp1.
        remember (compute_step lib (oterm (NCan ncan) bs)) as comp'; symmetry in Heqcomp'; destruct comp'; ginv.
        applydup @compute_step_preserves_wf in Heqcomp'; auto.
        apply IHk in comp0; exrepnd; repndors; exrepnd; auto.

        { exists (S j); dands; try omega.
          left.
          exists n0.
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { exists (S j); dands; try omega.
          right.
          exists n0 e0.
          rw @computes_to_exception_in_max_k_steps_S.
          eexists; dands; eauto. }

      * Case "Exc".
        csunf comp1; allsimpl; ginv.
        exists 0; dands; try omega.
        right.
        apply wf_exception_implies in wf; exrepnd; subst; fold_terms.
        exists a0 t0.
        rw @computes_to_exception_in_max_k_steps_0; auto.

      * Case "Abs".
        unfold bound_nat_try_aux in comp1.
        rw @compute_step_mk_cbv_abs in comp1.
        remember (compute_step_lib lib abs bs) as comp'; symmetry in Heqcomp'; destruct comp'; ginv.
        applydup @wf_compute_step_lib in Heqcomp'; auto.
        apply IHk in comp0; exrepnd; repndors; exrepnd; auto.

        { exists (S j); dands; try omega.
          left.
          exists n0.
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { exists (S j); dands; try omega.
          right.
          exists n0 e0.
          rw @computes_to_exception_in_max_k_steps_S.
          eexists; dands; eauto. }
Qed.

Lemma reduces_to_bound_nat_try_aux_nat {o} :
  forall lib a n x e z (f : @NTerm o) t,
    isprog f
    -> isprog t
    -> reduces_to lib (bound_nat_try_aux a (mk_nat n) x e z f t)
                  (mk_try (mk_apply f (mk_nat n)) (mk_utoken a) e t).
Proof.
  introv isp ispt.

  eapply reduces_to_if_split2;[csunf;simpl;auto|].
  unfold apply_bterm; simpl; fold_terms.
  unflsubst; simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  fold_terms.

  eapply reduces_to_if_split2;
    [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
  match goal with
    | [ |- context[mk_fix ?x] ] => remember (mk_fix x) as b
  end; clear Heqb.
  boolvar; tcsp; try omega;
  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
Qed.

Lemma if_has_value_like_k_ncompop {o} :
  forall lib c k (t u a b : @NTerm o),
    wf_term t
    -> wf_term u
    -> wf_term a
    -> wf_term b
    -> has_value_like_k lib k (mk_compop c t u a b)
    -> {j : nat
        & {v : NTerm
        & j < k
        # reduces_in_atmost_k_steps lib t v j
        # (iswfpk c v [+] isexc v)}}.
Proof.
  introv wft wfu wfa wfb hv.
  unfold has_value_like_k in hv; exrepnd.
  apply computes_to_val_like_in_max_k_steps_comp_implies in hv0; auto;[].
  repndors; exrepnd; subst.

  - exists k1 (pk2term pk1); dands; eauto 3 with slow; try omega.
    repndors; exrepnd; subst; allsimpl; left; eauto 3 with slow.

  - exists k1 (mk_exception en e); dands; eauto 3 with slow; try omega.

  - exists k1 (pk2term pk); dands; eauto 3 with slow; try omega.
    left; repndors; exrepnd; subst; allsimpl; eauto 3 with slow.
Qed.

(* !!MOVE *)
Hint Resolve co_wf_def_len_implies : slow.
Hint Resolve ca_wf_def_len_implies : slow.

Lemma get_utokens_pk_pk2term {o} :
  forall (pk : @param_kind o),
    get_utokens_pk pk = get_utokens (pk2term pk).
Proof.
  introv; destruct pk; simpl; auto.
Qed.

Lemma differ_try_iswfpk {o} :
  forall c a f g d (t1 t2 t3 : @NTerm o),
    iswfpk c t1
    -> differ_try a f g d t1 t2 t3
    -> ((iswfpk c t2 # iswfpk c t3 # !LIn a (get_utokens t2) # !LIn a (get_utokens t3))
        [+] spfexc_pair a t2 t3).
Proof.
  introv i dd.
  unfold iswfpk in i; destruct c.
  - unfold isinteger in i; exrepnd; subst.
    apply differ_try_integer in dd; repndors; repnd; subst; allsimpl; dands; eauto 3 with slow.
    left; dands; eauto 3 with slow; tcsp.
  - unfold ispk in i; exrepnd; subst.
    apply differ_try_pk2term in dd; repndors; repnd; subst; allsimpl; dands; eauto 3 with slow.
    allrw <- @get_utokens_pk_pk2term.
    left; dands; eauto 3 with slow.
Qed.

Lemma differ_try_alpha_iswfpk {o} :
  forall c a f g d (t1 t2 t3 : @NTerm o),
    iswfpk c t1
    -> differ_try_alpha a f g d t1 t2 t3
    -> ((iswfpk c t2 # iswfpk c t3 # !LIn a (get_utokens t2) # !LIn a (get_utokens t3))
        [+] spfexc_pair a t2 t3).
Proof.
  introv i dd.
  unfold iswfpk in i; destruct c.
  - unfold isinteger in i; exrepnd; subst.
    apply differ_try_alpha_integer in dd; repndors; repnd; subst; dands; eauto 3 with slow.
    left; dands; eauto 3 with slow; tcsp.
  - unfold ispk in i; exrepnd; subst.
    apply differ_try_alpha_pk2term in dd; repndors; repnd; subst; allsimpl; dands; eauto 3 with slow.
    allrw <- @get_utokens_pk_pk2term.
    left; dands; eauto 3 with slow.
Qed.

Lemma spfexc_pair_spexc {o} :
  forall (a : get_patom_set o),
    spfexc_pair a (spexc a) (spexc a).
Proof.
  introv.
  exists ([] : list NVar) ([] : list NVar) ([] : list NVar) ([] : list NVar).
  simpl; dands; auto.
Qed.
Hint Resolve spfexc_pair_spexc : slow.

Lemma fold_lfresh {o} :
  forall v vs (t : @NTerm o),
    mk_fresh v (lfresh vs t) = lfresh (v :: vs) t.
Proof.
  sp.
Qed.

Lemma get_fresh_atom_lfresh {o} :
  forall vs (t : @NTerm o),
    get_fresh_atom (lfresh vs t) = get_fresh_atom t.
Proof.
  induction vs; introv; simpl; auto.
  unfold get_fresh_atom; simpl; allrw app_nil_r.
  fold (get_fresh_atom (lfresh vs t)); rw IHvs; auto.
Qed.

Lemma reduces_in_atmost_k_steps_utoken_alpha {o} :
  forall lib a k (t1 t2 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> reduces_in_atmost_k_steps lib t1 (mk_utoken a) k
    -> reduces_in_atmost_k_steps lib t2 (mk_utoken a) k.
Proof.
  introv wf aeq r.
  eapply reduces_in_atmost_k_steps_alpha in r;[| |exact aeq]; auto.
  exrepnd.
  apply alpha_eq_mk_utoken in r0; subst; auto.
Qed.

Lemma get_utokens_lfresh {o} :
  forall vs (t : @NTerm o),
    get_utokens (lfresh vs t) = get_utokens t.
Proof.
  induction vs; introv; simpl; auto.
  allrw app_nil_r; auto.
Qed.

Lemma subst_utokens_aux_lfresh {o} :
  forall vs sub (t : @NTerm o),
    subst_utokens_aux (lfresh vs t) sub = lfresh vs (subst_utokens_aux t sub).
Proof.
  induction vs; simpl; introv; auto; fold_terms.
  rw IHvs; auto.
Qed.

Lemma compute_step_lfresh_snoc_utoken {o} :
  forall lib vs v (a : get_patom_set o),
    {vs' : list NVar
     & length vs = length vs'
     # compute_step lib (lfresh (snoc vs v) (mk_utoken a))
       = csuccess (lfresh vs' (mk_utoken a)) }.
Proof.
  induction vs as [|x vs ind]; introv; allsimpl.
  - exists ([] : list NVar); simpl.
    csunf; simpl; auto.
  - pose proof (nterm_trico_like (lfresh (snoc vs v) (mk_utoken a))) as tri; repndors.

    + unfold isvariable in tri; destruct vs; allsimpl; ginv; sp.

    + destruct vs; allsimpl; fold_terms; allunfold @isvalue_like; allsimpl; tcsp.

    + rw @computation2.compute_step_fresh_if_isnoncan_like; auto.
      allrw @get_fresh_atom_lfresh.
      simpl.
      unfsubst.
      rw @cl_lsubst_aux_lfresh; eauto 3 with slow.
      pose proof (ind v a) as h; exrepnd.
      rw h0; simpl.

      pose proof (unfold_subst_utokens
                    [(get_fresh_atom (mk_utoken a), mk_var x)]
                    (lfresh vs' (mk_utoken a))) as unf; exrepnd.
      allsimpl; allrw disjoint_singleton_r.
      apply alpha_eq_lfresh_implies in unf1; exrepnd; subst; eauto 3 with slow.
      allapply @alpha_eq_mk_utoken; subst; allsimpl.
      rw unf0.

      pose proof (get_fresh_atom_prop (mk_utoken a)) as ni; allsimpl.
      allrw not_over_or; repnd; GC.
      rw @subst_utokens_aux_lfresh; simpl.
      unfold subst_utok; simpl; boolvar; tcsp; fold_terms.
      exists (x :: vs'0); simpl; dands; auto; try omega.
Qed.

Lemma compute_step_lfresh_snoc_axiom {o} :
  forall (lib : @library o) vs v,
    {vs' : list NVar
     & length vs = length vs'
     # compute_step lib (lfresh (snoc vs v) mk_axiom)
       = csuccess (lfresh vs' mk_axiom) }.
Proof.
  induction vs as [|x vs ind]; introv; allsimpl.
  - exists ([] : list NVar); simpl.
    csunf; simpl; auto.
  - pose proof (nterm_trico_like (lfresh (snoc vs v) (@mk_axiom o))) as tri; repndors.

    + unfold isvariable in tri; destruct vs; allsimpl; ginv; sp.

    + destruct vs; allsimpl; fold_terms; allunfold @isvalue_like; allsimpl; tcsp.

    + rw @computation2.compute_step_fresh_if_isnoncan_like; auto.
      allrw @get_fresh_atom_lfresh.
      simpl.
      unfsubst.
      rw @cl_lsubst_aux_lfresh; eauto 3 with slow.
      pose proof (ind v) as h; exrepnd.
      rw h0; simpl.

      pose proof (unfold_subst_utokens
                    [(get_fresh_atom mk_axiom, mk_var x)]
                    (lfresh vs' (@mk_axiom o))) as unf; exrepnd.
      allsimpl; allrw disjoint_singleton_r.
      apply alpha_eq_lfresh_implies in unf1; exrepnd; subst; eauto 3 with slow.
      allapply @alpha_eq_mk_axiom; subst; allsimpl.
      rw unf0.

      rw @subst_utokens_aux_lfresh; simpl.
      unfold subst_utok; simpl; boolvar; tcsp; fold_terms.
      exists (x :: vs'0); simpl; dands; auto; try omega.
Qed.

Lemma reduces_in_atmost_k_steps_lfresh_utoken {o} :
  forall lib (a : get_patom_set o) vs,
    reduces_in_atmost_k_steps lib (lfresh vs (mk_utoken a)) (mk_utoken a) (length vs).
Proof.
  intros lib a vs.
  remember (length vs) as n.
  revert dependent vs.
  induction n; introv len; allsimpl; cpx.
  pose proof (rev_list_dest _ vs) as d; repndors; subst; allsimpl; ginv.
  exrepnd; subst; allsimpl; allrw length_snoc; ginv.
  allrw @reduces_in_atmost_k_steps_S.
  pose proof (compute_step_lfresh_snoc_utoken lib u v a) as h; exrepnd.
  rw h0.
  eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_lfresh_axiom {o} :
  forall (lib : @library o) vs,
    reduces_in_atmost_k_steps lib (lfresh vs mk_axiom) mk_axiom (length vs).
Proof.
  intros lib vs.
  remember (length vs) as n.
  revert dependent vs.
  induction n; introv len; allsimpl; cpx.
  pose proof (rev_list_dest _ vs) as d; repndors; subst; allsimpl; ginv.
  exrepnd; subst; allsimpl; allrw length_snoc; ginv.
  allrw @reduces_in_atmost_k_steps_S.
  pose proof (compute_step_lfresh_snoc_axiom lib u v) as h; exrepnd.
  rw h0.
  eexists; dands; eauto.
Qed.

Definition differ_try_b_alpha {o} a f g c (b1 b2 b3 : @BTerm o) :=
  {u1 : BTerm
   & {u2 : BTerm
   & {u3 : BTerm
   & alpha_eq_bterm b1 u1
   # alpha_eq_bterm b2 u2
   # alpha_eq_bterm b3 u3
   # differ_try_b a f g c u1 u2 u3}}}.

Definition differ_try_bterms_alpha {o} a f g c (bs1 bs2 bs3 : list (@BTerm o)) :=
  {bs1' : list BTerm
   & {bs2' : list BTerm
   & {bs3' : list BTerm
   & alpha_eq_bterms bs1 bs1'
   # alpha_eq_bterms bs2 bs2'
   # alpha_eq_bterms bs3 bs3'
   # differ_try_bterms a f g c bs1' bs2' bs3' }}}.

Lemma implies_differ_try_bterms_alpha {o} :
  forall a f g c (bs1 bs2 bs3 : list (@BTerm o)),
    length bs1 = length bs2
    -> length bs1 = length bs3
    -> (forall b1 b2 b3,
          LIn (b1,b2,b3) (combine3 bs1 bs2 bs3)
          -> differ_try_b_alpha a f g c b1 b2 b3)
    -> differ_try_bterms_alpha a f g c bs1 bs2 bs3.
Proof.
  induction bs1; destruct bs2, bs3; introv len1 len2 imp; allsimpl; ginv; auto.
  - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)) ([] : list (@BTerm o)); dands; eauto 3 with slow.
  - cpx.
    pose proof (imp a0 b b0) as d; autodimp d hyp.
    unfold differ_try_b_alpha in d; exrepnd.
    pose proof (IHbs1 bs2 bs3) as h; repeat (autodimp h hyp).
    unfold differ_try_bterms_alpha in h; exrepnd.
    exists (u1 :: bs1') (u2 :: bs2') (u3 :: bs3').
    dands; eauto 3 with slow.
Qed.

Lemma differ_try_alpha_oterm {o} :
  forall a f g c op (bs1 bs2 bs3 : list (@BTerm o)),
    differ_try_bterms_alpha a f g c bs1 bs2 bs3
    -> !LIn a (get_utokens_o op)
    -> differ_try_alpha
         a f g c
         (oterm op bs1)
         (oterm op bs2)
         (oterm op bs3).
Proof.
  introv d ni.
  unfold differ_try_bterms_alpha in d; exrepnd.
  exists (oterm op bs1') (oterm op bs2') (oterm op bs3').
  dands; eauto 3 with slow; try (apply alpha_eq_oterm_combine; complete auto).
  allunfold @alpha_eq_bterms; repnd.
  unfold differ_try_bterms, br_bterms3, br_list3 in d0; repnd.
  eauto 3 with slow.
Qed.

Lemma implies_differ_try_b_alpha {o} :
  forall a f g c vs (t1 t2 t3 : @NTerm o),
    differ_try_alpha a f g c t1 t2 t3
    -> differ_try_b_alpha a f g c (bterm vs t1) (bterm vs t2) (bterm vs t3).
Proof.
  introv d.
  unfold differ_try_alpha in d; exrepnd.
  exists (bterm vs u1) (bterm vs u2) (bterm vs u3).
  dands; eauto 3 with slow.
Qed.

Lemma differ_try_isvalue_like {o} :
  forall a f g c (t1 t2 t3 : @NTerm o),
    isvalue_like t1
    -> differ_try a f g c t1 t2 t3
    -> ((isvalue_like t2
         # isvalue_like t3
         # (forall v,
              differ_try_alpha
                a f g c
                (pushdown_fresh v t1)
                (pushdown_fresh v t2)
                (pushdown_fresh v t3)))
          [+] spfexc_pair a t2 t3).
Proof.
  introv isv d.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst.

    { inversion d as [? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp];
      subst; allsimpl; clear d; tcsp; GC;[].
      left; dands; eauto 3 with slow.
      introv.

      apply differ_try_alpha_oterm; auto.
      apply implies_differ_try_bterms_alpha; allrw @length_mk_fresh_bterms; auto.
      introv i.
      allunfold @mk_fresh_bterms.
      allrw @map_combine3.
      allrw in_map_iff; exrepnd; allsimpl; ginv.
      applydup imp in i1.
      inversion i0 as [? ? ? ? d]; subst; clear i0.
      unfold mk_fresh_bterm.
      apply implies_differ_try_b_alpha.
      unfold maybe_new_var; boolvar;
      [|apply differ_try_implies_differ_try_alpha;
         apply differ_try_oterm; simpl; tcsp;
         introv i; repndors; tcsp; complete ginv].

      pose proof (ex_fresh_var (all_vars t1
                                         ++ all_vars t2
                                         ++ all_vars t3)) as fv; exrepnd.
      exists (mk_fresh v0 t1) (mk_fresh v0 t2) (mk_fresh v0 t3).
      allrw in_app_iff; allrw not_over_or; repnd.
      dands; eauto 3 with slow;
      try (complete (apply differ_try_oterm; simpl; tcsp; introv i; repndors; ginv; tcsp));
      apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp;
      try (rw @lsubst_trivial4; simpl;
           [|apply disjoint_singleton_l; apply newvar_prop
            |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]);
      try (rw @lsubst_trivial4; simpl;
           [auto
           |apply disjoint_singleton_l; auto
           |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]).
    }

    { inversion d as [?|?|?|?|?];
      subst; allsimpl; clear d; tcsp; GC;[].

      left; dands; eauto 3 with slow.
    }

  - apply isexc_implies2 in isv; exrepnd; subst.
    inversion d as [? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp];
      subst; allsimpl; clear d; tcsp; GC;[].
    left; dands; eauto 3 with slow.
    introv.

    apply differ_try_alpha_oterm; simpl; tcsp.
    apply implies_differ_try_bterms_alpha; allrw @length_mk_fresh_bterms; auto.
    introv i.
    allunfold @mk_fresh_bterms.
    allrw @map_combine3.
    allrw in_map_iff; exrepnd; allsimpl; ginv.
    applydup imp in i1.
    inversion i0 as [? ? ? ? d]; subst; clear i0.
    unfold mk_fresh_bterm.
    apply implies_differ_try_b_alpha.
    unfold maybe_new_var; boolvar;
    [|apply differ_try_implies_differ_try_alpha;
       apply differ_try_oterm; simpl; tcsp;
       introv i; repndors; tcsp; complete ginv].

    pose proof (ex_fresh_var (all_vars t1
                                       ++ all_vars t2
                                       ++ all_vars t3)) as fv; exrepnd.
    exists (mk_fresh v0 t1) (mk_fresh v0 t2) (mk_fresh v0 t3).
    allrw in_app_iff; allrw not_over_or; repnd.
    dands; eauto 3 with slow;
    try (complete (apply differ_try_oterm; simpl; tcsp; introv i; repndors; ginv; tcsp));
    apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp;
    try (rw @lsubst_trivial4; simpl;
         [|apply disjoint_singleton_l; apply newvar_prop
          |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]);
    try (rw @lsubst_trivial4; simpl;
         [auto
         |apply disjoint_singleton_l; auto
         |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]).
Qed.

Lemma ren_utok_op_if_get_utok_none {o} :
  forall ren (op : @Opid o),
    get_utok op = None
    -> ren_utok_op ren op = op.
Proof.
  introv e.
  destruct op; allsimpl; ginv.
  destruct c; allsimpl; ginv.
Qed.

Lemma swap_ren_utokens {o} :
  forall (t : @NTerm o) sw ren,
    swap sw (ren_utokens ren t) = ren_utokens ren (swap sw t).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  Case "oterm".
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t].
  allsimpl.
  f_equal.
  eapply ind; eauto 3 with slow.
Qed.

Lemma cswap_ren_utokens {o} :
  forall (t : @NTerm o) sw ren,
    cswap sw (ren_utokens ren t) = ren_utokens ren (cswap sw t).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  Case "oterm".
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t].
  allsimpl.
  f_equal.
  eapply ind; eauto 3 with slow.
Qed.

Lemma simple_subst_aux_subst_utokens_aux_aeq_ren {o} :
  forall (t1 t2 : @NTerm o) a1 a2 v,
    wf_term t2
    -> !LIn v (bound_vars t1)
    -> !LIn v (free_vars t1)
    -> alpha_eq t1 t2
    -> alpha_eq
         (subst_aux (subst_utokens_aux t1 [(a1, mk_var v)]) v (mk_utoken a2))
         (ren_utokens [(a1,a2)] t2).
Proof.
  nterm_ind1s t1 as [x|f ind|op bs ind] Case; introv wf ni1 ni2 aeq.

  - Case "vterm".
    allsimpl.
    unfold subst_aux; simpl.
    allrw not_over_or; repnd; GC.
    inversion aeq; subst; clear aeq.
    boolvar; tcsp.

  - Case "sterm".
    allsimpl; autorewrite with slow in *; GC.
    inversion aeq as [|? ? imp|]; clear aeq; subst.
    unfold subst_aux; allsimpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst.
    allrw @wf_oterm_iff; repnd.
    allsimpl.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      destruct bs'; allsimpl; cpx; allsimpl; GC.
      unfold subst_utok, subst_aux; simpl.
      repeat (boolvar; subst; allsimpl; auto).
      * unfold ren_atom; simpl; boolvar; tcsp.
      * unfold ren_atom; simpl; boolvar; tcsp.

    + unfold subst_aux; simpl.
      allrw map_map; unfold compose.
      rw @ren_utok_op_if_get_utok_none; auto.

      apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      destruct a0 as [l1 t1].
      destruct a as [l2 t2].
      allsimpl.
      applydup aeq0 in i1.
      applydup in_combine in i1; repnd.
      allrw lin_flat_map.

      assert (!LIn v l1) as nivl1.
      { intro i; destruct ni1; eexists; dands; eauto; simpl; rw in_app_iff; sp. }

      boolvar; tcsp.

      apply alphaeqbt_eq in i0.
      rw @alphaeqbt_all in i0.
      pose proof (i0 (allvars (lsubst_aux (subst_utokens_aux t1 [(a1, mk_var v)]) [(v, mk_utoken a2)]))) as aeq.
      inversion aeq as [? ? ? ? ? len1 len2 disj norep ae]; subst; allsimpl.
      allrw disjoint_app_r; repnd.
      apply alphaeq_vs_implies_alphaeq in ae.
      apply alphaeq_eq in ae.

      apply alphaeqbt_eq.
      apply (aeqbt _ vs); simpl; auto.
      { allrw @allvars_ren_utokens; allrw disjoint_app_r; dands; auto. }

      apply alphaeq_eq.
      rw @lsubst_aux_cswap_cswap; eauto 3 with slow; simpl; fold_terms.
      rw @cswap_subst_utokens_aux; simpl.
      rw @cswap_ren_utokens.

      apply (ind t1 (cswap (mk_swapping l1 vs) t1) l1); auto.
      { rw @osize_cswap; eauto 3 with slow. }
      { apply wf_term_cswap; apply wf in i2.
        apply wf_bterm_iff in i2; auto. }
      { rw @bound_vars_cswap.
        rw in_swapbvars; intro k; exrepnd.
        apply swapvars_eq in k0; eauto 2 with slow; subst.
        destruct ni1.
        eexists; dands; eauto; simpl; rw in_app_iff; sp. }
      { rw @free_vars_cswap; eauto 2 with slow.
        rw in_swapbvars; intro k; exrepnd.
        apply swapvars_eq in k0; eauto 2 with slow; subst.
        destruct ni2.
        eexists; dands; eauto; simpl; rw in_remove_nvars; sp. }
Qed.

Lemma simple_subst_subst_utokens_aeq_ren {o} :
  forall (t : @NTerm o) a1 a2 v,
    wf_term t
    -> !LIn v (free_vars t)
    -> alpha_eq
         (subst (subst_utokens t [(a1, mk_var v)]) v (mk_utoken a2))
         (ren_utokens [(a1,a2)] t).
Proof.
  introv wf ni.
  rw @cl_subst_subst_aux; eauto 3 with slow; unfold subst_aux.
  pose proof (unfold_subst_utokens [(a1,mk_var v)] t) as aeq; exrepnd; allsimpl.
  allrw disjoint_singleton_r.
  rw aeq0.
  apply simple_subst_aux_subst_utokens_aux_aeq_ren; eauto with slow.
  intro i.
  apply alphaeq_preserves_free_vars in aeq1; rw <- aeq1 in i; sp.
Qed.

Lemma differ_try_alpha_spfexc {o} :
  forall a f g c (t : @NTerm o) vs1 vs2 vs3 vs4,
    length vs1 = length vs2
    -> length vs3 = length vs4
    -> length vs1 = length vs3
    -> differ_try_alpha a f g c t (spfexc vs1 vs2 a) (spfexc vs3 vs4 a).
Proof.
  introv len1 len2 len4.
  eauto 4 with slow.
Qed.
Hint Resolve differ_try_alpha_spfexc : slow.

Lemma differ_try_alpha_alpha_eq1 {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) t,
    alpha_eq t1 t
    -> differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha a f g c t t2 t3.
Proof.
  introv aeq d.
  allunfold @differ_try_alpha; exrepnd.
  exists u1 u2 u3; dands; eauto 3 with slow.
Qed.

Lemma differ_try_alpha_alpha_eq2 {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) t,
    alpha_eq t2 t
    -> differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha a f g c t1 t t3.
Proof.
  introv aeq d.
  allunfold @differ_try_alpha; exrepnd.
  exists u1 u2 u3; dands; eauto 3 with slow.
Qed.

Lemma differ_try_alpha_alpha_eq3 {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) t,
    alpha_eq t3 t
    -> differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha a f g c t1 t2 t.
Proof.
  introv aeq d.
  allunfold @differ_try_alpha; exrepnd.
  exists u1 u2 u3; dands; eauto 3 with slow.
Qed.

Lemma differ_try_alpha_mk_fresh {o} :
  forall a f g c v (t1 t2 t3 : @NTerm o),
    differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha a f g c (mk_fresh v t1) (mk_fresh v t2) (mk_fresh v t3).
Proof.
  introv d.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_fresh v u1) (mk_fresh v u2) (mk_fresh v u3).
  dands; eauto 3 with slow; try (apply implies_alpha_eq_mk_fresh); auto.
  apply differ_try_oterm; simpl; tcsp.
  introv i; repndors; cpx.
Qed.

Definition get_utokens_utok_sub {o} (sub : @utok_sub o) :=
  flat_map get_utokens (utok_sub_range sub).

Definition differ_try_sk {o} a f g c (sk1 sk2 sk3 : @sosub_kind o) :=
  differ_try_b a f g c (sk2bterm sk1) (sk2bterm sk2) (sk2bterm sk3).

Inductive differ_try_sosubs {o} a f g c : @SOSub o -> @SOSub o -> @SOSub o -> Type :=
| dsosub_try_nil : differ_try_sosubs a f g c [] [] []
| dsosub_try_cons :
    forall v sk1 sk2 sk3 sub1 sub2 sub3,
      differ_try_sk a f g c sk1 sk2 sk3
      -> differ_try_sosubs a f g c sub1 sub2 sub3
      -> differ_try_sosubs a f g c ((v,sk1) :: sub1) ((v,sk2) :: sub2) ((v,sk3) :: sub3).
Hint Constructors differ_try_sosubs.

Lemma sosub_find_some_if_differ_try_sosubs {o} :
  forall a f g c (sub1 sub2 sub3 : @SOSub o) v sk,
    differ_try_sosubs a f g c sub1 sub2 sub3
    -> sosub_find sub1 v = Some sk
    -> {sk2 : sosub_kind
        & {sk3 : sosub_kind
        & differ_try_sk a f g c sk sk2 sk3
        # sosub_find sub2 v = Some sk2
        # sosub_find sub3 v = Some sk3}}.
Proof.
  induction sub1; destruct sub2, sub3; introv aeq sf; allsimpl; tcsp;
  try (complete (inversion aeq)).
  destruct a0, p, p0.
  destruct s, s0, s1.
  inversion aeq as [|? ? ? ? ? ? ? dsk dso]; subst; clear aeq.
  boolvar; subst; cpx; tcsp; try (complete (inversion dsk; subst; tcsp)).
  eexists; eexists; dands; eauto.
Qed.

Lemma differ_try_subs_combine {o} :
  forall a f g c (ts1 ts2 ts3 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> length ts1 = length ts3
    -> (forall t1 t2 t3,
          LIn (t1,t2,t3) (combine3 ts1 ts2 ts3)
          -> differ_try a f g c t1 t2 t3)
    -> differ_try_subs a f g c (combine vs ts1) (combine vs ts2) (combine vs ts3).
Proof.
  induction ts1; destruct ts2, ts3; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma sosub_find_none_if_differ_try_sosubs {o} :
  forall a f g c (sub1 sub2 sub3 : @SOSub o) v,
    differ_try_sosubs a f g c sub1 sub2 sub3
    -> sosub_find sub1 v = None
    -> (sosub_find sub2 v = None # sosub_find sub3 v = None).
Proof.
  induction sub1; destruct sub2, sub3; introv aeq sf; allsimpl; tcsp;
  try (complete (inversion aeq)).
  destruct a0, p, p0.
  destruct s, s0, s1.
  inversion aeq as [|? ? ? ? ? ? ? dsk dso]; subst; clear aeq.
  boolvar; subst; cpx; tcsp; inversion dsk; subst; tcsp.
Qed.

Lemma differ_try_apply_list {o} :
  forall a f g c (ts1 ts2 ts3 : list (@NTerm o)) t1 t2 t3,
    differ_try a f g c t1 t2 t3
    -> length ts1 = length ts2
    -> length ts1 = length ts3
    -> (forall x y z, LIn (x,y,z) (combine3 ts1 ts2 ts3) -> differ_try a f g c x y z)
    -> differ_try a f g c (apply_list t1 ts1) (apply_list t2 ts2) (apply_list t3 ts3).
Proof.
  induction ts1; destruct ts2, ts3; introv d len1 len2 i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ_try_oterm; simpl; auto; tcsp.
  introv k; repndors; cpx; tcsp; constructor; auto.
Qed.

Lemma differ_try_sosub_filter {o} :
  forall a f g c (sub1 sub2 sub3 : @SOSub o) vs,
    differ_try_sosubs a f g c sub1 sub2 sub3
    -> differ_try_sosubs a f g c (sosub_filter sub1 vs) (sosub_filter sub2 vs) (sosub_filter sub3 vs).
Proof.
  induction sub1; destruct sub2, sub3; introv d;
  inversion d as [|? ? ? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2, sk3; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ_try_sosub_filter : slow.

Lemma differ_try_sosub_aux {o} :
  forall a f g c (t : @SOTerm o) sub1 sub2 sub3,
    no_utokens t
    -> isprog f
    -> isprog g
    -> isprog c
    -> differ_try_sosubs a f g c sub1 sub2 sub3
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub3)
    -> disjoint (free_vars_sosub sub3) (bound_vars_sosub sub3)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub3)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> cover_so_vars t sub3
    -> differ_try a f g c (sosub_aux sub1 t) (sosub_aux sub2 t) (sosub_aux sub3 t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv nut df dg dc ds;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7 disj8 disj9;
  introv cov1 cov2 cov3; allsimpl; tcsp.

  - Case "sovar".
    allrw @cover_so_vars_sovar; repnd.
    allrw @no_utokens_sovar.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ_try_sosubs a f g c sub1 sub2 sub3) in Heqf1; auto.
      exrepnd.
      rw Heqf3.
      rw Heqf0.
      destruct s as [l1 t1].
      destruct sk2 as [l2 t2].
      destruct sk3 as [l3 t3].
      inversion Heqf2; subst.
      apply differ_try_lsubst_aux; auto.

      * apply differ_try_subs_combine; allrw map_length; auto;[].
        introv i.
        rw @map_combine3 in i.
        rw in_map_iff in i; exrepnd; cpx; allsimpl.
        apply in_combine3_same in i1; repnd; subst; allsimpl.
        disj_flat_map.
        apply ind; auto.

      * apply sosub_find_some in Heqf1; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto 3 with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

      * apply sosub_find_some in Heqf3; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto 3 with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

      * apply sosub_find_some in Heqf0; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto 3 with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

    + applydup (sosub_find_none_if_differ_try_sosubs a f g c sub1 sub2 sub3) in Heqf1; auto.
      repnd.
      rw Heqf0.
      rw Heqf2.
      apply differ_try_apply_list; allrw map_length; auto.
      introv i.
      rw @map_combine3 in i; rw in_map_iff in i; exrepnd; cpx.
      apply in_combine3_same in i1; repnd; subst; allsimpl.
      disj_flat_map.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm.
    allrw @no_utokens_soterm; repnd.
    apply differ_try_oterm; allrw map_length; tcsp; try (complete (rw nut0; sp));[].
    introv i.
    rw @map_combine3 in i; rw in_map_iff in i; exrepnd; cpx.
    apply in_combine3_same in i1; repnd; subst; allsimpl.
    destruct a2 as [l t].
    disj_flat_map.
    allsimpl; allrw disjoint_app_l; repnd.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.
    constructor; auto.
    applydup nut in i0; allsimpl.
    eapply ind; eauto 2 with slow.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub1 (vars2sovars l)) as sv.
      eapply subvars_disjoint_r;[exact sv|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub1 (vars2sovars l)) as sv1.
      pose proof (subvars_bound_vars_sosub_filter sub1 (vars2sovars l)) as sv2.
      eapply subvars_disjoint_r;[exact sv2|]; auto.
      eapply subvars_disjoint_l;[exact sv1|]; auto.

    + pose proof (subvars_bound_vars_sosub_filter sub1 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub2 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub2 (vars2sovars l)) as sv1.
      pose proof (subvars_bound_vars_sosub_filter sub2 (vars2sovars l)) as sv2.
      eapply subvars_disjoint_r;[exact sv2|]; auto.
      eapply subvars_disjoint_l;[exact sv1|]; auto.

    + pose proof (subvars_bound_vars_sosub_filter sub2 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub3 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub3 (vars2sovars l)) as sv1.
      pose proof (subvars_bound_vars_sosub_filter sub3 (vars2sovars l)) as sv2.
      eapply subvars_disjoint_r;[exact sv2|]; auto.
      eapply subvars_disjoint_l;[exact sv1|]; auto.

    + pose proof (subvars_bound_vars_sosub_filter sub3 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + apply cov1 in i0.
      apply cover_so_vars_sosub_filter; auto.

    + apply cov2 in i0.
      apply cover_so_vars_sosub_filter; auto.

    + apply cov3 in i0.
      apply cover_so_vars_sosub_filter; auto.
Qed.

Lemma differ_try_b_change_bound_vars {o} :
  forall a f g c vs (b1 b2 b3 : @BTerm o),
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try_b a f g c b1 b2 b3
    -> {u1 : BTerm
        & {u2 : BTerm
        & {u3 : BTerm
        & differ_try_b a f g c u1 u2 u3
        # alpha_eq_bterm b1 u1
        # alpha_eq_bterm b2 u2
        # alpha_eq_bterm b3 u3
        # disjoint (bound_vars_bterm u1) vs
        # disjoint (bound_vars_bterm u2) vs
        # disjoint (bound_vars_bterm u3) vs }}}.
Proof.
  introv ispf ispg ispc d.
  pose proof (differ_try_change_bound_vars
                a f g c vs (oterm Exc [b1]) (oterm Exc [b2]) (oterm Exc [b3])) as h.
  repeat (autodimp h hyp).
  - apply differ_try_oterm; simpl; tcsp.
    introv i; dorn i; tcsp; cpx.
  - exrepnd.
    inversion h2 as [| |? ? ? len1 imp1]; subst; allsimpl; cpx.
    inversion h3 as [| |? ? ? len2 imp2]; subst; allsimpl; cpx.
    inversion h4 as [| |? ? ? len3 imp3]; subst; allsimpl; cpx.
    pose proof (imp1 0) as k1; autodimp k1 hyp; allsimpl; clear imp1.
    pose proof (imp2 0) as k2; autodimp k2 hyp; allsimpl; clear imp2.
    pose proof (imp3 0) as k3; autodimp k3 hyp; allsimpl; clear imp3.
    allunfold @selectbt; allsimpl.
    allrw app_nil_r.
    inversion h1 as [|? ? ? spf|?|?|? ? ? ? i]; subst; allsimpl; GC.
    + allunfold @spfexc_pair; exrepnd; ginv.
    + exists x x0 x1; dands; auto.
Qed.

Lemma differ_try_sk_change_bound_vars {o} :
  forall a f g c vs (sk1 sk2 sk3 : @sosub_kind o),
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try_sk a f g c sk1 sk2 sk3
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
        & {u3 : sosub_kind
        & differ_try_sk a f g c u1 u2 u3
        # alphaeq_sk sk1 u1
        # alphaeq_sk sk2 u2
        # alphaeq_sk sk3 u3
        # disjoint (bound_vars_sk u1) vs
        # disjoint (bound_vars_sk u2) vs
        # disjoint (bound_vars_sk u3) vs }}}.
Proof.
  introv ispf ispg ispc d.
  unfold differ_try_sk in d.
  apply (differ_try_b_change_bound_vars a f g c vs) in d; exrepnd; allsimpl; auto.
  exists (bterm2sk u1) (bterm2sk u2) (bterm2sk u3).
  destruct u1, u2, u3, sk1, sk2, sk3; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ_try_sosubs_change_bound_vars {o} :
  forall a f g c vs (sub1 sub2 sub3 : @SOSub o),
    isprog f
    -> isprog g
    -> isprog c
    -> differ_try_sosubs a f g c sub1 sub2 sub3
    -> {sub1' : SOSub
        & {sub2' : SOSub
        & {sub3' : SOSub
        & differ_try_sosubs a f g c sub1' sub2' sub3'
        # alphaeq_sosub sub1 sub1'
        # alphaeq_sosub sub2 sub2'
        # alphaeq_sosub sub3 sub3'
        # disjoint (bound_vars_sosub sub1') vs
        # disjoint (bound_vars_sosub sub2') vs
        # disjoint (bound_vars_sosub sub3') vs }}}.
Proof.
  induction sub1; destruct sub2, sub3; introv ispf ispg ispc d; try (complete (inversion d)).
  - exists ([] : @SOSub o) ([] : @SOSub o) ([] : @SOSub o); dands; simpl; tcsp.
  - inversion d as [|? ? ? ? ? ? ? dsk dso]; subst; clear d.
    apply IHsub1 in dso; exrepnd; auto.
    apply (differ_try_sk_change_bound_vars a f g c vs) in dsk; exrepnd; auto.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2') ((v,u3) :: sub3'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto 3 with slow.
Qed.

Lemma differ_try_sosub {o} :
  forall a f g c (t : @SOTerm o) (sub1 sub2 sub3 : SOSub),
    isprog f
    -> isprog g
    -> isprog c
    -> no_utokens t
    -> differ_try_sosubs a f g c sub1 sub2 sub3
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> cover_so_vars t sub3
    -> differ_try_alpha a f g c (sosub sub1 t) (sosub sub2 t) (sosub sub3 t).
Proof.
  introv ispf ispg ispc nut d c1 c2 c3.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.
  pose proof (unfold_sosub sub3 t) as q.
  destruct q as [sub3' q]; destruct q as [t3 q]; repnd; rw q.

  pose proof (differ_try_sosubs_change_bound_vars
                a
                f g c
                (all_fo_vars t1
                             ++ all_fo_vars t2
                             ++ all_fo_vars t3
                             ++ free_vars_sosub sub1
                             ++ free_vars_sosub sub2
                             ++ free_vars_sosub sub3
                )
                sub1 sub2 sub3
                ispf ispg ispc d) as e.
  destruct e as [sub1'' e]; destruct e as [sub2'' e]; destruct e as [sub3'' e]; repnd.

  pose proof (fo_change_bvars_alpha_spec
                (free_vars_sosub sub1''
                                 ++ free_vars_sosub sub2''
                                 ++ free_vars_sosub sub3''
                                 ++ bound_vars_sosub sub1''
                                 ++ bound_vars_sosub sub2''
                                 ++ bound_vars_sosub sub3''
                                 ++ free_vars f
                                 ++ free_vars g
                )
                t) as ch.
  revert ch.
  fo_change t0; simpl; intro ch; repnd; GC.

  allrw disjoint_app_l; allrw disjoint_app_r; repnd.

  assert (so_alphaeq t1 t0) as a1 by eauto 3 with slow.
  assert (so_alphaeq t2 t0) as a2 by eauto 3 with slow.
  assert (so_alphaeq t3 t0) as a3 by eauto 3 with slow.

  pose proof (fovars_subvars_all_fo_vars t1) as sv1.
  pose proof (fovars_subvars_all_fo_vars t2) as sv2.
  pose proof (fovars_subvars_all_fo_vars t3) as sv3.
  pose proof (alphaeq_sosub_preserves_free_vars sub1 sub1'') as ev1; autodimp ev1 hyp.
  pose proof (alphaeq_sosub_preserves_free_vars sub2 sub2'') as ev2; autodimp ev2 hyp.
  pose proof (alphaeq_sosub_preserves_free_vars sub3 sub3'') as ev3; autodimp ev3 hyp.
  pose proof (fovars_subvars_all_fo_vars t0) as svt0.
  pose proof (all_fo_vars_eqvars t0) as evt0.
  pose proof (all_fo_vars_eqvars t1) as evt1.
  pose proof (all_fo_vars_eqvars t2) as evt2.
  pose proof (all_fo_vars_eqvars t3) as evt3.
  pose proof (so_alphaeq_preserves_free_vars t1 t0 a1) as efv1.
  pose proof (so_alphaeq_preserves_free_vars t2 t0 a2) as efv2.
  pose proof (so_alphaeq_preserves_free_vars t3 t0 a3) as efv3.
  applydup eqvars_app_r_implies_subvars in evt0 as evt0'; destruct evt0' as [evt0'1 evt0'2].
  applydup eqvars_app_r_implies_subvars in evt1 as evt1'; destruct evt1' as [evt1'1 evt1'2].
  applydup eqvars_app_r_implies_subvars in evt2 as evt2'; destruct evt2' as [evt2'1 evt2'2].
  applydup eqvars_app_r_implies_subvars in evt3 as evt3'; destruct evt3' as [evt3'1 evt3'2].

  assert (disjoint (fo_bound_vars t0) (free_vars_sosub sub1'')
          # disjoint (free_vars_sosub sub1'') (bound_vars_sosub sub1'')
          # disjoint (all_fo_vars t0) (bound_vars_sosub sub1'')
          # disjoint (fo_bound_vars t0) (free_vars_sosub sub2'')
          # disjoint (free_vars_sosub sub2'') (bound_vars_sosub sub2'')
          # disjoint (all_fo_vars t0) (bound_vars_sosub sub2'')
          # disjoint (fo_bound_vars t0) (free_vars_sosub sub3'')
          # disjoint (free_vars_sosub sub3'') (bound_vars_sosub sub3'')
          # disjoint (all_fo_vars t0) (bound_vars_sosub sub3'')) as disj.

  { dands; eauto 2 with slow.
    - rw <- ev1; eauto 3 with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact evt0|].
      apply disjoint_app_l; dands; eauto 2 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact evt1'2|]; eauto 3 with slow.
    - rw <- ev2; eauto 3 with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact evt0|].
      apply disjoint_app_l; dands; eauto 2 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact evt1'2|]; eauto 3 with slow.
    - rw <- ev3; eauto 3 with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact evt0|].
      apply disjoint_app_l; dands; eauto 2 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact evt1'2|]; eauto 3 with slow. }

  repnd.

  pose proof (sosub_aux_alpha_congr2 t1 t0 sub1' sub1'') as aeq1.
  repeat (autodimp aeq1 hyp); eauto 3 with slow.
  { rw disjoint_app_r; dands; eauto 3 with slow. }
  { rw disjoint_app_r; dands; eauto 3 with slow. }

  pose proof (sosub_aux_alpha_congr2 t2 t0 sub2' sub2'') as aeq2.
  repeat (autodimp aeq2 hyp); eauto 3 with slow.
  { rw disjoint_app_r; dands; eauto 3 with slow. }
  { rw disjoint_app_r; dands; eauto 3 with slow. }

  pose proof (sosub_aux_alpha_congr2 t3 t0 sub3' sub3'') as aeq3.
  repeat (autodimp aeq3 hyp); eauto 3 with slow.
  { rw disjoint_app_r; dands; eauto 3 with slow. }
  { rw disjoint_app_r; dands; eauto 3 with slow. }

  exists (sosub_aux sub1'' t0) (sosub_aux sub2'' t0) (sosub_aux sub3'' t0); dands;
  try (apply alphaeq_eq; complete auto).

  apply differ_try_sosub_aux; eauto 3 with slow.

  { allapply @get_utokens_so_soalphaeq.
    unfold no_utokens; rw <- h5; auto. }
Qed.

Lemma differ_try_mk_abs_substs {o} :
  forall a f g c (bs1 bs2 bs3 : list (@BTerm o)) vars,
    differ_try_bterms a f g c bs1 bs2 bs3
    -> length vars = length bs1
    -> differ_try_sosubs a f g c (mk_abs_subst vars bs1) (mk_abs_subst vars bs2) (mk_abs_subst vars bs3).
Proof.
  induction bs1; destruct bs2, bs3; destruct vars; introv d m; allsimpl; cpx; tcsp;
  try (complete (provefalse; apply differ_try_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx)).
  apply differ_try_bterms_cons in d; repnd.
  destruct s.
  inversion d0; subst.
  boolvar; auto.
Qed.

Lemma differ_try_mk_instance {o} :
  forall a f g c (t : @SOTerm o) vars bs1 bs2 bs3,
    isprog f
    -> isprog g
    -> isprog c
    -> no_utokens t
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> matching_bterms vars bs3
    -> socovered t vars
    -> differ_try_bterms a f g c bs1 bs2 bs3
    -> differ_try_alpha a f g c (mk_instance vars bs1 t) (mk_instance vars bs2 t) (mk_instance vars bs3 t).
Proof.
  introv ispf ispg ispc nut m1 m2 m3 sc dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ_try_mk_abs_substs o a f g c bs1 bs2 bs3 vars) in dbs; auto.

  apply differ_try_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_trans {o} :
  forall lib k j (a b c : @CTerm o),
    reduces_in_atmost_k_steps_excc lib a b k
    -> reduces_in_atmost_k_steps_excc lib b c j
    -> reduces_in_atmost_k_steps_excc lib a c (k + j).
Proof.
  introv r1 r2; destruct_cterms.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  eapply reduces_in_atmost_k_steps_exc_trans; eauto.
Qed.

Lemma reduces_ksteps_excc_can_implies {o} :
  forall lib k (t u : @CTerm o),
    iscanc u
    -> reduces_ksteps_excc lib t u k
    -> reduces_kstepsc lib t u k.
Proof.
  introv isc r; spcast.
  apply reduces_in_atmost_k_steps_excc_can_implies; auto.
Qed.

Lemma differ_try_subst_utokens_aux {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) sub,
    isprog f
    -> isprog g
    -> isprog c
    -> !LIn a (utok_sub_dom sub)
    -> !LIn a (get_utokens_utok_sub sub)
    -> disjoint (bound_vars t1) (free_vars_utok_sub sub)
    -> disjoint (bound_vars t2) (free_vars_utok_sub sub)
    -> disjoint (bound_vars t3) (free_vars_utok_sub sub)
    -> disjoint (get_utokens f) (utok_sub_dom sub)
    -> disjoint (get_utokens g) (utok_sub_dom sub)
    -> disjoint (get_utokens c) (utok_sub_dom sub)
    -> differ_try a f g c t1 t2 t3
    -> differ_try
         a f g c
         (subst_utokens_aux t1 sub)
         (subst_utokens_aux t2 sub)
         (subst_utokens_aux t3 sub).
Proof.
  nterm_ind t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv ispf ispg ispc nia1 nia2;
  introv disj1 disj2 disj3 duf dug duc d.

  - Case "vterm".
    inversion d as [|? ? ? r|?|?|]; subst; allsimpl; eauto with slow;[].

    allunfold @spfexc_pair; exrepnd; subst; allsimpl.
    allrw @subst_utokens_aux_lfresh; allsimpl; fold_terms.
    rw @subst_utok_if_not_in; auto.

  - Case "sterm".
    allsimpl.
    inversion d as [|? ? ? r|?|?|]; subst; allsimpl; eauto with slow;[].

    allunfold @spfexc_pair; exrepnd; subst; allsimpl.
    allrw @subst_utokens_aux_lfresh; allsimpl; fold_terms.
    rw @subst_utok_if_not_in; auto.

  - Case "oterm".
    inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|? ? ? spf|?|?|? ? ? ? len1 len2 na imp];
      subst; clear d; GC; fold_terms;[|idtac|].

    + allsimpl; allrw app_nil_r; fold_terms.
      repeat (allrw disjoint_app_l; allrw disjoint_cons_l; repnd).
      rw @subst_utok_if_not_in; auto;[]; fold_terms.
      rw (trivial_subst_utokens_aux f'); eauto 3 with slow;
      [|apply alphaeq_preserves_utokens in aeq1; rw <- aeq1; auto].
      rw (trivial_subst_utokens_aux g'); eauto 3 with slow;
      [|apply alphaeq_preserves_utokens in aeq2; rw <- aeq2; auto].
      rw (trivial_subst_utokens_aux c'); eauto 3 with slow;
      [|apply alphaeq_preserves_utokens in aeq3; rw <- aeq3; auto].

      constructor; auto.

      pose proof (ind1 arg1 []) as h; repeat (autodimp h hyp).

    + allunfold @spfexc_pair; exrepnd; subst.
      allrw @subst_utokens_aux_oterm; allsimpl.
      allrw @subst_utokens_aux_lfresh; allsimpl.
      rw @subst_utok_if_not_in; auto;[]; fold_terms.
      apply differ_try_exc.
      apply spfexc_pair_spfexc; auto.

    + allrw @subst_utokens_aux_oterm; allsimpl.
      remember (get_utok op1) as guo1; symmetry in Heqguo1; destruct guo1.

      * unfold subst_utok.
        remember (utok_sub_find sub g0) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
        { apply utok_sub_find_some in Heqsf.
          apply differ_try_refl; auto.
          introv i; destruct nia2.
          rw lin_flat_map; exists n; dands; auto.
          eapply implies_utok_sub_range; eauto. }
        apply get_utok_some in Heqguo1; subst; allsimpl; allrw not_over_or; repnd; GC.
        apply differ_try_oterm; allrw map_length; simpl; tcsp;[].
        introv i; rw @map_combine3 in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
        applydup imp in i1; applydup in_combine3 in i1; repnd.
        disj_flat_map.
        destruct a2 as [l1 u1].
        destruct a1 as [l2 u2].
        destruct a0 as [l3 u3].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? ? d1]; subst; clear i0.
        constructor; auto.

        pose proof (ind1 u1 l3) as q; autodimp q hyp.

      * apply differ_try_oterm; allrw map_length; auto.
        introv i; rw @map_combine3 in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
        applydup imp in i1; applydup in_combine3 in i1; repnd.
        disj_flat_map.
        destruct a2 as [l1 u1].
        destruct a1 as [l2 u2].
        destruct a0 as [l3 u3].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? ? d1]; subst; clear i0.
        constructor; auto.

        pose proof (ind1 u1 l3) as q; autodimp q hyp.
Qed.

Lemma differ_try_alpha_subst_utokens {o} :
  forall a f g c (t1 t2 t3 : @NTerm o) sub,
    isprog f
    -> isprog g
    -> isprog c
    -> !LIn a (utok_sub_dom sub)
    -> !LIn a (get_utokens_utok_sub sub)
    -> disjoint (get_utokens f) (utok_sub_dom sub)
    -> disjoint (get_utokens g) (utok_sub_dom sub)
    -> disjoint (get_utokens c) (utok_sub_dom sub)
    -> differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha
         a f g c
         (subst_utokens t1 sub)
         (subst_utokens t2 sub)
         (subst_utokens t3 sub).
Proof.
  introv ispf ispg ispc nia1 nia2 disj1 disj2 disj3 d.
  unfold differ_try_alpha in d; exrepnd.

  eapply differ_try_alpha_alpha_eq1;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d1|].
  eapply differ_try_alpha_alpha_eq2;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d2|].
  eapply differ_try_alpha_alpha_eq3;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d3|].
  clear dependent t1.
  clear dependent t2.
  clear dependent t3.

  pose proof (differ_try_change_bound_vars
                a f g c (free_vars_utok_sub sub)
                u1 u2 u3 ispf ispg ispc d0) as d; exrepnd.
  rename u0 into t1.
  rename u4 into t2.
  rename u5 into t3.

  eapply differ_try_alpha_alpha_eq1;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d3|].
  eapply differ_try_alpha_alpha_eq2;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d4|].
  eapply differ_try_alpha_alpha_eq3;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d5|].
  clear dependent u1.
  clear dependent u2.
  clear dependent u3.

  pose proof (unfold_subst_utokens sub t1) as h; exrepnd.
  pose proof (unfold_subst_utokens sub t2) as k; exrepnd.
  pose proof (unfold_subst_utokens sub t3) as q; exrepnd.
  rename t' into u1.
  rename t'0 into u2.
  rename t'1 into u3.
  rw h0; rw k0; rw q0.

  eapply differ_try_alpha_alpha_eq1;[apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u1 t1 sub sub); eauto 3 with slow|].
  eapply differ_try_alpha_alpha_eq2;[apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u2 t2 sub sub); eauto 3 with slow|].
  eapply differ_try_alpha_alpha_eq3;[apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u3 t3 sub sub); eauto 3 with slow|].

  apply differ_try_implies_differ_try_alpha.
  apply differ_try_subst_utokens_aux; auto.
Qed.

Lemma red_spexc_pair_implies_red {o} :
  forall lib a (t1 t2 : @NTerm o),
    red_spexc_pair lib a t1 t2
    -> {n1 : NTerm
        & {e1 : NTerm
        & {n2 : NTerm
        & {e2 : NTerm
        & (t1 =e>(n1,lib) e1)
        # (n1 =v>(lib) (mk_utoken a))
        # (e1 =v>(lib) mk_axiom)
        # (t2 =e>(n2,lib) e2)
        # (n2 =v>(lib) (mk_utoken a))
        # (e2 =v>(lib) mk_axiom)
        # red_spexc_pair lib a (mk_exception n1 e1) (mk_exception n2 e2)}}}}.
Proof.
  introv r.
  unfold red_spexc_pair in r; repnd.
  apply reduces_to_exc_spexc in r2.
  apply reduces_to_exc_spexc in r.
  exrepnd.
  exists n0 e0 n e; dands; eauto 3 with slow.
  applydup @preserve_program_exc2 in r6; allrw @isprogram_eq; repnd; auto.
  applydup @preserve_program_exc2 in r3; allrw @isprogram_eq; repnd; auto.
  unfold red_spexc_pair; dands; try (apply isprog_exception; auto).
  - apply reduces_to_exc_spexc_as_cequiv; try (apply isprog_exception; auto).
    apply cequiv_spexc_if; try (apply isprog_exception; auto).
    exists n0 e0; dands; eauto 3 with slow.
    apply reduces_to_symm.
  - apply reduces_to_exc_spexc_as_cequiv; try (apply isprog_exception; auto).
    apply cequiv_spexc_if; try (apply isprog_exception; auto).
    exists n e; dands; eauto 3 with slow.
    apply reduces_to_symm.
Qed.

Lemma red_spexc_pair_fresh {o} :
  forall lib a v (t1 t2 : @NTerm o),
    red_spexc_pair lib a t1 t2
    -> red_spexc_pair lib a (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv r.
  dup r as rsp.
  apply red_spexc_pair_implies_red in rsp; exrepnd.
  allunfold @red_spexc_pair; repnd.

  pose proof (fresh_atom o (a :: get_utokens t1
                              ++ get_utokens t2
                              ++ get_utokens n1
                              ++ get_utokens e1
                              ++ get_utokens n2
                              ++ get_utokens e2)) as fa;
    exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (reduces_to_fresh2 lib t1 (mk_exception n1 e1) v x) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  { rw @subst_trivial; eauto 2 with slow. }
  exrepnd.

  pose proof (reduces_to_fresh2 lib t2 (mk_exception n2 e2) v x) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { rw @subst_trivial; eauto 2 with slow. }
  exrepnd.

  pose proof (unfold_subst_utokens [(x,mk_var v)] (mk_exception n1 e1)) as l; exrepnd; allsimpl.
  rw l0 in h0; clear l0.
  rw @trivial_subst_utokens_aux in h0; allsimpl; allrw disjoint_singleton_r;
  [|apply alphaeq_preserves_utokens in l1; rw <- l1; simpl;
    allrw app_nil_r; allrw in_app_iff; complete sp].
  assert (alpha_eq z (mk_exception n1 e1)) as aeq1 by eauto 3 with slow.
  clear l1 l2 h0.

  pose proof (unfold_subst_utokens [(x,mk_var v)] (mk_exception n2 e2)) as l; exrepnd; allsimpl.
  rw l0 in q0; clear l0.
  rw @trivial_subst_utokens_aux in q0; allsimpl; allrw disjoint_singleton_r;
  [|apply alphaeq_preserves_utokens in l1; rw <- l1; simpl;
    allrw app_nil_r; allrw in_app_iff; complete sp].
  assert (alpha_eq z0 (mk_exception n2 e2)) as aeq2 by eauto 3 with slow.
  clear l1 l2 q0.

  assert (isprog z) as ispz.
  { apply alpha_eq_sym in aeq1; apply alpha_eq_preserves_isprog in aeq1; auto. }

  assert (isprog z0) as ispz0.
  { apply alpha_eq_sym in aeq2; apply alpha_eq_preserves_isprog in aeq2; auto. }

  dands; try (apply isprog_fresh_implies); eauto 2 with slow.

  - eapply reduces_to_exc_trans2;[exact h1|].
    apply reduces_to_exc_spexc_as_cequiv; try (apply isprog_fresh_implies); eauto 2 with slow.
    apply cequiv_spexc_if; try (apply isprog_fresh_implies); eauto 2 with slow.
    apply alpha_eq_sym in aeq1; apply alpha_eq_exception in aeq1; exrepnd; subst.
    allrw @isprog_exception_iff; repnd.
    exists (mk_fresh v a') (mk_fresh v e'); dands; eauto 3 with slow.

    + apply reduces_to_if_step; csunf; simpl; auto.

    + dup rsp2 as c.
      eapply compute_to_value_alpha in c;[| |exact aeq3]; exrepnd; eauto 3 with slow;[].
      allapply @alpha_eq_mk_utoken; subst.

      pose proof (reduces_to_fresh2 lib a' (mk_utoken a) v x) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow.
      { apply alphaeq_preserves_utokens in aeq3; rw <- aeq3; sp. }
      { rw @subst_trivial; eauto 2 with slow. }
      exrepnd.

      split; eauto 3 with slow;[].
      eapply reduces_to_trans;[exact xx1|].
      unfold subst_utokens in xx0; allsimpl.
      unfold subst_utok in xx0; allsimpl; boolvar; tcsp;[]; fold_terms.
      apply alpha_eq_sym in xx0; apply alpha_eq_mk_utoken in xx0; subst.
      apply reduces_to_if_step; csunf; simpl; auto.

    + dup rsp3 as c.
      eapply compute_to_value_alpha in c;[| |exact aeq1]; exrepnd; eauto 3 with slow;[].
      allapply @alpha_eq_mk_axiom; subst.

      pose proof (reduces_to_fresh2 lib e' mk_axiom v x) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow.
      { apply alphaeq_preserves_utokens in aeq1; rw <- aeq1; sp. }
      { rw @subst_trivial; eauto 2 with slow. }
      exrepnd.

      split; eauto 3 with slow;[].
      eapply reduces_to_trans;[exact xx1|].
      unfold subst_utokens in xx0; allsimpl.
      unfold subst_utok in xx0; allsimpl; boolvar; tcsp;[]; fold_terms.
      apply alpha_eq_sym in xx0; apply alpha_eq_mk_axiom in xx0; subst.
      apply reduces_to_if_step; csunf; simpl; auto.

  - eapply reduces_to_exc_trans2;[exact q1|].
    apply reduces_to_exc_spexc_as_cequiv; try (apply isprog_fresh_implies); eauto 2 with slow.
    apply cequiv_spexc_if; try (apply isprog_fresh_implies); eauto 2 with slow.
    apply alpha_eq_sym in aeq2; apply alpha_eq_exception in aeq2; exrepnd; subst.
    allrw @isprog_exception_iff; repnd.
    exists (mk_fresh v a') (mk_fresh v e'); dands; eauto 3 with slow.

    + apply reduces_to_if_step; csunf; simpl; auto.

    + dup rsp5 as c.
      eapply compute_to_value_alpha in c;[| |exact aeq3]; exrepnd; eauto 3 with slow;[].
      allapply @alpha_eq_mk_utoken; subst.

      pose proof (reduces_to_fresh2 lib a' (mk_utoken a) v x) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow.
      { apply alphaeq_preserves_utokens in aeq3; rw <- aeq3; sp. }
      { rw @subst_trivial; eauto 2 with slow. }
      exrepnd.

      split; eauto 3 with slow;[].
      eapply reduces_to_trans;[exact xx1|].
      unfold subst_utokens in xx0; allsimpl.
      unfold subst_utok in xx0; allsimpl; boolvar; tcsp;[]; fold_terms.
      apply alpha_eq_sym in xx0; apply alpha_eq_mk_utoken in xx0; subst.
      apply reduces_to_if_step; csunf; simpl; auto.

    + dup rsp6 as c.
      eapply compute_to_value_alpha in c;[| |exact aeq2]; exrepnd; eauto 3 with slow;[].
      allapply @alpha_eq_mk_axiom; subst.

      pose proof (reduces_to_fresh2 lib e' mk_axiom v x) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow.
      { apply alphaeq_preserves_utokens in aeq2; rw <- aeq2; sp. }
      { rw @subst_trivial; eauto 2 with slow. }
      exrepnd.

      split; eauto 3 with slow;[].
      eapply reduces_to_trans;[exact xx1|].
      unfold subst_utokens in xx0; allsimpl.
      unfold subst_utok in xx0; allsimpl; boolvar; tcsp;[]; fold_terms.
      apply alpha_eq_sym in xx0; apply alpha_eq_mk_axiom in xx0; subst.
      apply reduces_to_if_step; csunf; simpl; auto.
Qed.
Hint Resolve red_spexc_pair_fresh : slow.

Lemma iswfpk_utoken {o} :
  forall (a : get_patom_set o), iswfpk CompOpEq (mk_utoken a).
Proof.
  introv; unfold iswfpk; eauto 3 with slow.
Qed.
Hint Resolve iswfpk_utoken : slow.

Lemma reduces_to_lfresh_axiom {o} :
  forall (lib : @library o) (vs : list NVar),
    reduces_to lib (lfresh vs mk_axiom) mk_axiom.
Proof.
  introv; exists (length vs).
  apply reduces_in_atmost_k_steps_lfresh_axiom.
Qed.

Lemma reduces_to_lfresh_utoken {o} :
  forall lib (a : get_patom_set o) (vs : list NVar),
    reduces_to lib (lfresh vs (mk_utoken a)) (mk_utoken a).
Proof.
  introv; exists (length vs).
  apply reduces_in_atmost_k_steps_lfresh_utoken.
Qed.

Ltac ex_spfexc_h H :=
  match type of H with
    | spfexc_pair ?a ?t ?u =>
      let vs1 := fresh "vs1" in
      let vs2 := fresh "vs2" in
      let vs3 := fresh "vs3" in
      let vs4 := fresh "vs4" in
      unfold spfexc_pair in H;
        destruct H as [vs1 H];
        destruct H as [vs2 H];
        destruct H as [vs3 H];
        destruct H as [vs4 H];
        repnd;
        exists t u;
        subst;
        eexists; dands; eauto 3 with slow
  end.

Ltac ex_spfexc :=
  match goal with
    | [ H : spfexc_pair ?a ?t ?u |- _ ] => ex_spfexc_h H
  end.

Ltac ex_red_spexc_pair :=
  match goal with
    | [ H : red_spexc_pair ?lib ?a ?t ?u |- _ ] =>
      eexists; eexists; eexists; dands;
      [apply reduces_to_symm
      |apply reduces_to_symm
      |apply reduces_to_symm
      |];
      eauto 3 with slow
  end.

Ltac ex_red_spexc_pair2_h H :=
  match type of H with
    | red_spexc_pair ?lib ?a ?t ?u =>
      let r    := fresh "r"    in
      let n1   := fresh "n1"   in
      let e1   := fresh "e1"   in
      let n2   := fresh "n2"   in
      let e2   := fresh "e2"   in
      let ct1  := fresh "ct1"  in
      let cn1  := fresh "cn1"  in
      let ce1  := fresh "ce1"  in
      let ct2  := fresh "ct2"  in
      let cn2  := fresh "cn2"  in
      let ce2  := fresh "ce2"  in
      assert (red_spexc_pair lib a t u) as r by (exact H);
        apply red_spexc_pair_implies_red in r;
        destruct r as [n1 r];
        destruct r as [e1 r];
        destruct r as [n2 r];
        destruct r as [e2 r];
        destruct r as [ct1 r];
        destruct r as [cn1 r];
        destruct r as [ce1 r];
        destruct r as [ct2 r];
        destruct r as [cn2 r];
        destruct r as [ce2 r];
        exists (mk_exception n1 e1) (mk_exception n2 e2);
        eexists; dands;
        [idtac
        |idtac
        |apply reduces_to_symm
        |];
        try (complete (eapply reduces_to_trans;
                       [eapply reduces_to_prinarg;exact ct1|];
                       eauto 3 with slow));
        try (complete (eapply reduces_to_trans;
                       [eapply reduces_to_prinarg;exact ct2|];
                       eauto 3 with slow));
        try (complete (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_comp_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct1]
                       |]; eauto 3 with slow));
        try (complete (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_comp_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct2]
                       |]; eauto 3 with slow));
        try (complete (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_arith_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct1]
                       |]; eauto 3 with slow));
        try (complete (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_arith_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct2]
                       |]; eauto 3 with slow));
        eauto 3 with slow
  end.

Ltac ex_red_spexc_pair2 :=
  match goal with
    | [ H : red_spexc_pair ?lib ?a ?t ?u |- _ ] => ex_red_spexc_pair2_h H
  end.

Lemma differ_try_alpha_mk_eapply {o} :
  forall a f g c (a1 a2 a3 b1 b2 b3 : @NTerm o),
    differ_try_alpha a f g c a1 a2 a3
    -> differ_try_alpha a f g c b1 b2 b3
    -> differ_try_alpha a f g c (mk_eapply a1 b1) (mk_eapply a2 b2) (mk_eapply a3 b3).
Proof.
  introv da1 da2.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u4 u2) (mk_eapply u5 u3); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply differ_try_oterm; simpl; tcsp.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_try_preserves_iscan {o} :
  forall a f g c (t1 t2 t3 : @NTerm o),
    differ_try a f g c t1 t2 t3
    -> iscan t1
    -> ((iscan t2 # iscan t3)
        [+] spfexc_pair a t2 t3).
Proof.
  introv diff isc.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  inversion diff; subst; simpl; auto.
Qed.


Lemma differ_try_lam_implies {o} :
  forall a f g c v b (t1 t2 : @NTerm o),
    differ_try a f g c (mk_lam v b) t1 t2
    -> {b1 : NTerm
        & {b2 : NTerm
        & t1 = mk_lam v b1
        # t2 = mk_lam v b2
        # differ_try a f g c b b1 b2 }}
       [+] (spfexc_pair a t1 t2).
Proof.
  introv d.
  inversion d as [|?|?|?|? ? ? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.

  pose proof (imp (bterm [v] b) x0 x) as d1; autodimp d1 hyp.
  clear imp.

  inversion d1 as [? ? ? ? d2]; subst; clear d1.
  fold_terms.

  left; eexists; eexists; dands; eauto.
Qed.

Lemma differ_try_nseq_implies {o} :
  forall a f g c s (t1 t2 : @NTerm o),
    differ_try a f g c (mk_nseq s) t1 t2
    -> (t1 = mk_nseq s
        # t2 = mk_nseq s)
       [+] (spfexc_pair a t1 t2).
Proof.
  introv d.
  inversion d as [|?|?|?|? ? ? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.
Qed.

Lemma differ_try_nat_implies {o} :
  forall a f g c n (t1 t2 : @NTerm o),
    differ_try a f g c (mk_nat n) t1 t2
    -> (t1 = mk_nat n
        # t2 = mk_nat n)
       [+] (spfexc_pair a t1 t2).
Proof.
  introv d.
  inversion d as [|?|?|?|? ? ? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.
Qed.

Lemma differ_try_alpha_mk_lam {o} :
  forall a f g c v (t1 t2 t3 : @NTerm o),
    differ_try_alpha a f g c t1 t2 t3
    -> differ_try_alpha a f g c (mk_lam v t1) (mk_lam v t2) (mk_lam v t3).
Proof.
  introv d.
  allunfold @differ_try_alpha; exrepnd.
  exists (mk_lam v u1) (mk_lam v u2) (mk_lam v u3); dands;
  try (apply implies_alpha_eq_mk_lam; eauto with slow).
  apply differ_try_oterm; simpl; tcsp.
  introv i; repndors; cpx.
Qed.

Lemma differ_try_step {o} :
  forall lib a f g c (t1 t2 t3 : @NTerm o) u k,
    isprog f
    -> isprog g
    -> isprog c
    -> wf_term t1
    -> wf_term t2
    -> wf_term t3
    -> eq_fun2TE lib a f g
    -> differ_try a f g c t1 t2 t3
    -> compute_step lib t1 = csuccess u
    -> has_value_like_k lib k u
    -> (forall t1 t2 t3 v m, (* induction hypothesis *)
          m < S k
          -> wf_term t1
          -> wf_term t2
          -> wf_term t3
          -> isvalue_like v
          -> reduces_in_atmost_k_steps lib t1 v m
          -> differ_try a f g c t1 t2 t3
          -> {v2 : NTerm
              & {v3 : NTerm
              & reduces_to lib t2 v2
              # reduces_to lib t3 v3
              # differ_try_alpha a f g c v v2 v3}})
    -> {t2' : NTerm
        & {t3' : NTerm
        & {u' : NTerm
        & reduces_to lib t2 t2'
        # reduces_to lib t3 t3'
        # reduces_to lib u u'
        # differ_try_alpha a f g c u' t2' t3'}}}.
Proof.
  nterm_ind1s t1 as [v|s ind|op bs ind] Case;
  introv ispf ispg ispc wt1 wt2 wt3 eqf;
  introv d comp hv indhyp.

  - Case "vterm".
    simpl.
    inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    inversion d as [|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp];
      clear d; subst; fold_terms;[|].

    { ex_spfexc. }

    exists (sterm s) (sterm s) (sterm s); dands; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase; ginv.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp];
        clear d; subst; fold_terms;[|].

      { ex_spfexc. }

      exists (oterm (Can can) bs2) (oterm (Can can) bs3) (oterm (Can can) bs); dands; eauto 3 with slow.

    + SCase "NCan".

      assert (forall (t1 t2 t3 v : NTerm) (m : nat),
                m < S k
                -> wf_term t1
                -> wf_term t2
                -> wf_term t3
                -> isvalue_like v
                -> reduces_in_atmost_k_steps lib t1 v m
                -> differ_try_alpha a f g c t1 t2 t3
                -> {v2, v3 : NTerm
                    $ reduces_to lib t2 v2
                    # reduces_to lib t3 v3
                    # differ_try_alpha a f g c v v2 v3}) as indhyp'.
      { introv x w1 w2 w3 isv r d'.
        unfold differ_try_alpha in d'; exrepnd.
        eapply reduces_in_atmost_k_steps_alpha in r;[| |exact d'1]; exrepnd;eauto 2 with slow;[].
        apply (indhyp _ _ _ t2' m) in d'0; eauto 2 with slow.
        exrepnd.

        applydup @alphaeq_preserves_wf_term in d'1;auto;[].
        applydup @alphaeq_preserves_wf_term in d'2;auto;[].
        applydup @alphaeq_preserves_wf_term in d'3;auto;[].

        eapply reduces_to_alpha in d'4;[| |apply alpha_eq_sym; exact d'2]; eauto 2 with slow;[].
        eapply reduces_to_alpha in d'5;[| |apply alpha_eq_sym; exact d'3]; eauto 2 with slow;[].
        exrepnd.
        eexists; eexists; dands; eauto.
        allunfold @differ_try_alpha; exrepnd.
        exists u0 u4 u5; dands; eauto 3 with slow. }
      clear indhyp; rename indhyp' into indhyp.

      destruct bs as [|b1 bs];
        try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (simpl in comp; ginv));
      [ (* non-fresh case *) | (* fresh case *) ].

      {
      destruct t1 as [v1|f1|op1 bs1].

      * destruct t2 as [v2|f2|op2 bs2];
        try (complete (inversion d; subst; allunfold @spfexc_pair; exrepnd; ginv)).

      * destruct t2 as [v2|f2|op2 bs2];
        try (complete (inversion d; subst; allunfold @spfexc_pair; exrepnd; ginv));[].

        csunf comp; allsimpl.

        dopid_noncan ncan SSCase; allsimpl; ginv.

        { SSCase "NApply".
          clear ind.
          apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl;[].

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].
          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          cpx; ginv; allsimpl.

          pose proof (imp (nobnd (sterm f1)) x0 x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd arg) y0 y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? ? d4]; subst; clear d2.
          inversion d3 as [|? ? ? spf|?|?|]; subst; clear d3.
          { ex_spfexc. }

          fold_terms.

          exists (mk_eapply (sterm f1) t0)
                 (mk_eapply (sterm f1) t4)
                 (mk_eapply (sterm f1) arg).
          dands; eauto 3 with slow.
          apply differ_try_implies_differ_try_alpha.
          apply differ_try_oterm; simpl; tcsp.
          introv j; repndors; cpx; constructor; auto.
        }

        { SSCase "NEApply".
          apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl;[].

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].
          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; ginv.
          simpl in len1, len2; cpx.
          simpl in imp.
          fold_terms.

          pose proof (imp (nobnd (sterm f1)) x0 x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd b) y0 y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? ? d4]; subst; clear d2.
          inversion d3 as [|? ? ? spf|?|?|]; subst; clear d3.
          { ex_spfexc. }
          fold_terms.

          repndors; exrepnd; subst.

          - apply compute_step_eapply2_success in comp1; repnd; GC.
            repndors; exrepnd; subst; ginv; allsimpl; GC.
            inversion d4 as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d4; GC;[|].
            { ex_spfexc. }
            cpx; clear imp; fold_terms.

            exists (f0 n) (f0 n) (f0 n); dands; eauto 3 with slow.

            { apply reduces_to_if_step.
              csunf; simpl.
              dcwf h; simpl; boolvar; try omega.
              rw @Znat.Nat2Z.id; auto. }

            { apply reduces_to_if_step.
              csunf; simpl.
              dcwf h; simpl; boolvar; try omega.
              rw @Znat.Nat2Z.id; auto. }

            { apply differ_try_alpha_refl; auto.
              allrw @nt_wf_sterm_iff.
              pose proof (wt4 n) as h; clear wt4; repnd.
              rw h; simpl; tcsp. }

          - apply isexc_implies2 in comp0; exrepnd; subst.
            inversion d4 as [|?|?|?|?]; subst; allsimpl; clear d4.
            { ex_spfexc. }
            exists (oterm Exc bs2) (oterm Exc bs3) (oterm Exc l); dands; eauto 3 with slow.

          - pose proof (ind b b []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow;[].
            allrw <- @wf_eapply_iff; repnd.
            pose proof (h t0 t4 x k) as ih; clear h.
            applydup @preserve_nt_wf_compute_step in comp1; auto.
            repeat (autodimp ih hyp); eauto 3 with slow.
            { apply has_value_k_like_eapply_sterm_implies in hv; exrepnd; eauto 3 with slow;[].
              eapply has_value_like_k_lt; eauto. }
            exrepnd.

            exists (mk_eapply (sterm f1) t2')
                   (mk_eapply (sterm f1) t3')
                   (mk_eapply (sterm f1) u').
            dands; eauto 3 with slow.
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply differ_try_alpha_mk_eapply; eauto 3 with slow. }
        }

        { SSCase "NFix".
          apply compute_step_fix_success in comp; repnd; subst; allsimpl.

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].
          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          cpx; allsimpl; fold_terms.
          pose proof (imp (nobnd (sterm f1)) x0 x) as d1; autodimp d1 hyp.
          clear imp.

          inversion d1 as [? ? ? ? d2]; subst; clear d1.
          inversion d2 as [|? ? ? spf|?|?|]; subst; clear d2.
          { ex_spfexc. }
          fold_terms.

          exists (mk_apply (sterm f1) (mk_fix (sterm f1)))
                 (mk_apply (sterm f1) (mk_fix (sterm f1)))
                 (mk_apply (sterm f1) (mk_fix (sterm f1))).
          dands; eauto 3 with slow.
          apply differ_try_alpha_refl; simpl; tcsp.
        }

        { SSCase "NCbv".
          apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.

          inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[| |].

          { inversion d1; subst; clear d1;
            allapply @has_value_like_k_subst_less_seq; tcsp.
          }

          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          { cpx; allsimpl.

            pose proof (imp (nobnd (sterm f1)) x1 x0) as d1; autodimp d1 hyp.
            pose proof (imp (bterm [v] x) y0 y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d3; subst; clear d3.
            { ex_spfexc. }
            inversion d2 as [? ? ? ? d4]; subst; clear d2.
            fold_terms.

            exists (subst t2 v (sterm f1))
                   (subst t3 v (sterm f1))
                   (subst x v (sterm f1)).
            dands; eauto 3 with slow. }
        }

        { SSCase "NTryCatch".
          apply compute_step_try_success in comp; exrepnd; subst; allsimpl.

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].
          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          cpx; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x1 x0) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a0) y0 y) as d2; autodimp d2 hyp.
          pose proof (imp (bterm [v] x) z0 z) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? ? d]; subst; clear d1.
          inversion d2 as [? ? ? ? d4]; subst; clear d2.
          inversion d3 as [? ? ? ? d5]; subst; clear d3.

          allrw <- @wf_try_iff; repnd.

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d; GC;[|].

          { applydup @if_has_value_like_k_ncompop_can_same in hv; exrepnd; eauto 3 with slow;[].

            repndors;[|].

            - unfold ispk in hv0; exrepnd; subst.

              pose proof (indhyp a0 t0 t4 (pk2term pk) j) as h.
              repeat (autodimp h hyp); eauto 3 with slow; exrepnd.
              apply differ_try_alpha_pk2term in h1.

              repndors;repnd;subst;[|].

              + ex_spfexc;
                eapply reduces_to_trans;
                [apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                |idtac
                |apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                |].

                * eapply reduces_to_trans;
                  [eapply reduce_to_prinargs_comp;
                    [apply computes_to_value_if_reduces_to;[exact h0|]
                    |idtac
                    |apply reduces_to_lfresh_utoken]
                  |]; eauto 3 with slow;[].
                  apply reduces_to_if_step.
                  csunf; simpl; rw @pk2term_eq; dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                  unfold compute_step_comp; simpl.
                  allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; allrw not_over_or; tcsp.

                * eapply reduces_to_trans;
                  [eapply reduce_to_prinargs_comp;
                    [apply computes_to_value_if_reduces_to;[exact h2|]
                    |idtac
                    |apply reduces_to_lfresh_utoken]
                  |]; eauto 3 with slow;[].
                  apply reduces_to_if_step.
                  csunf; simpl; rw @pk2term_eq; dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                  unfold compute_step_comp; simpl.
                  allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; allrw not_over_or; tcsp.

              + ex_spfexc_h h1; allunfold @spfexc_pair; exrepnd; subst;
                eapply reduces_to_trans;
                [apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                |idtac
                |apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                |].

                * eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;exact h0|].
                  eauto 3 with slow.

                * eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;exact h2|].
                  eauto 3 with slow.

            - applydup @reduces_in_atmost_k_steps_preserves_wf in hv2; auto.
              apply wf_isexc_implies in hv0; exrepnd; subst; auto.

              pose proof (indhyp a0 t0 t4 (mk_exception a1 e) j) as h.
              repeat (autodimp h hyp); eauto 3 with slow; exrepnd.
              apply differ_try_alpha_exception in h1.

              repndors; exrepnd; subst.

              + exists (mk_exception n1 e1) (mk_exception n2 e2) (mk_exception a1 e).
                allunfold @spfexc_pair; exrepnd; subst; dands; eauto 3 with slow.

                * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                  eapply reduces_to_trans;[apply reduces_to_prinarg;exact h0|].
                  apply reduces_to_if_step; csunf; simpl; auto.

                * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                  eapply reduces_to_trans;[apply reduces_to_prinarg;exact h2|].
                  apply reduces_to_if_step; csunf; simpl; auto.

                * eapply reduces_to_trans;[apply reduces_to_prinarg;exists j; exact hv2|].
                  apply reduces_to_if_step; csunf; simpl; auto.

                * apply implies_differ_try_alpha_exception; auto.

              + ex_spfexc_h h1; allunfold @spfexc_pair; exrepnd; subst.

                * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                  eapply reduces_to_trans;[apply reduces_to_prinarg;exact h0|].
                  apply reduces_to_if_step; csunf; simpl; auto.

                * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                  eapply reduces_to_trans;[apply reduces_to_prinarg;exact h2|].
                  apply reduces_to_if_step; csunf; simpl; auto.
          }

          exists (mk_atom_eq t0 t0 (sterm f1) mk_bot)
                 (mk_atom_eq t4 t4 (sterm f1) mk_bot)
                 (mk_atom_eq a0 a0 (sterm f1) mk_bot);
            dands; eauto 4 with slow.

          apply differ_try_implies_differ_try_alpha.
          apply differ_try_oterm; simpl; tcsp;[].

          introv i; repndors; ginv; tcsp; constructor; auto.
          apply differ_try_refl; simpl; tcsp.
        }

        { SSCase "NCanTest".
          apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.

          inversion d as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].
          { ex_spfexc;[].
            allunfold @spfexc; allunfold @mk_exception; ginv; fold_terms.
            apply differ_try_alpha_spfexc; auto. }

          cpx; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x0 x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a0) y0 y) as d2; autodimp d2 hyp.
          pose proof (imp (nobnd b) z0 z) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? ? d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          { ex_spfexc. }
          inversion d2 as [? ? ? ? d4]; subst; clear d2.
          inversion d3 as [? ? ? ? d5]; subst; clear d3.
          fold_terms.

          exists t0 t4 b.
          dands; eauto 3 with slow.
        }

      * (* Now destruct op2 *)
        dopid op1 as [can1|ncan1|exc1|abs1] SSCase; ginv.

        { SSCase "Can".

          (* Because the principal argument is canonical we can destruct ncan *)
          dopid_noncan ncan SSSCase.

          - SSSCase "NApply".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; allsimpl; fold_terms.

            { inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              cpx; GC; allsimpl.
              allrw @wf_term_apply_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

              pose proof (imp (nobnd (mk_lam v b)) (nobnd a2) (nobnd a1)) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd b0) (nobnd b2) (nobnd b1)) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [?|? ? ? r|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              cpx; allsimpl.
              destruct x as [l1 t1].
              destruct x0 as [l2 t2].
              allrw @wf_term_lambda_iff; exrepnd; ginv; fold_terms.

              pose proof (imp1 (bterm [v0] a0) (bterm [v2] a2) (bterm [v1] a1)) as d1.
              autodimp d1 hyp.
              clear imp1.
              inversion d1 as [? ? ? ? d2]; subst; clear d1.

              exists (subst a2 v1 b2) (subst a1 v1 b1) (subst a0 v1 b0).
              dands; eauto 3 with slow.
            }

            { inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              cpx; GC; allsimpl.
              allrw @wf_term_apply_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

              pose proof (imp (nobnd (mk_nseq f0)) (nobnd a2) (nobnd a1)) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd b) (nobnd b1) (nobnd b0)) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [?|? ? ? r|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              cpx; allsimpl.
              clear imp1.
              fold_terms.

              exists (mk_eapply (mk_nseq f0) b1) (mk_eapply (mk_nseq f0) b0) (mk_eapply (mk_nseq f0) b).
              dands; eauto 3 with slow.

              apply differ_try_implies_differ_try_alpha.
              apply differ_try_oterm; simpl; tcsp.
              introv j; repndors; cpx; tcsp; constructor; auto.
              apply differ_try_refl; simpl; tcsp.
            }

          - SSSCase "NEApply".
            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst.
            rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; ginv.

            inversion d as [?|? ? ? r|?|?|? ? ? ? len1 len2 nia imp1]; subst; clear d; GC;[|].
            { ex_spfexc. }
            simpl in len1, len2; cpx; simpl in imp1.

            pose proof (imp1 (nobnd (oterm (Can can1) bs1)) x0 x) as d1; autodimp d1 hyp.
            pose proof (imp1 (nobnd b) y0 y) as d2; autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d4]; subst; clear d2.
            fold_terms.
            allrw <- @wf_eapply_iff; repnd.
            apply eapply_wf_def_oterm_implies in comp2.

            destruct comp2; exrepnd; ginv; fold_terms;[|].

            { apply differ_try_lam_implies in d3; dorn d3;[|]; exrepnd; subst; fold_terms.

              { repndors; exrepnd; subst.

                + apply compute_step_eapply2_success in comp1; repnd; GC.
                  repndors; exrepnd; subst; ginv; allsimpl; GC.
                  allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                  applydup @differ_try_preserves_iscan in d4; auto.
                  repndors;repnd; [|].

                  { exists (subst b1 v0 t0)
                           (subst b2 v0 t4)
                           (subst b0 v0 b).
                    dands; eauto 3 with slow.
                    { apply eapply_lam_can_implies.
                      unfold computes_to_can; dands; eauto 3 with slow. }
                    { apply eapply_lam_can_implies.
                      unfold computes_to_can; dands; eauto 3 with slow. }
                  }

                  { ex_spfexc. }

                + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                  apply differ_try_exception in d4; repndors; exrepnd; subst;[|].

                  { exists (mk_exception n1 e1)
                           (mk_exception n2 e2)
                           (mk_exception a0 e).
                    dands; eauto 3 with slow.
                    apply implies_differ_try_alpha_exception; eauto 3 with slow.
                  }

                  { ex_spfexc. }

                + pose proof (ind b b []) as h; clear ind.
                  repeat (autodimp h hyp); eauto 3 with slow.
                  pose proof (h t0 t4 x k) as ih; clear h.
                  applydup @preserve_nt_wf_compute_step in comp1; auto.
                  repeat (autodimp ih hyp); eauto 3 with slow.
                  { apply has_value_like_k_eapply_lam_implies in hv; exrepnd; eauto 3 with slow;[].
                    eapply has_value_like_k_lt; eauto. }
                  exrepnd.

                  exists (mk_eapply (mk_lam v b1) t2')
                         (mk_eapply (mk_lam v b2) t3')
                         (mk_eapply (mk_lam v t) u').
                  dands; eauto 3 with slow.
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply differ_try_alpha_mk_eapply; eauto 3 with slow.
                    apply differ_try_alpha_mk_lam; eauto 3 with slow. }
              }

              { ex_spfexc. }
            }

            { apply differ_try_nseq_implies in d3; dorn d3;[|]; exrepnd; subst; fold_terms.

              { repndors; exrepnd; subst.

                + apply compute_step_eapply2_success in comp1; repnd; GC.
                  repndors; exrepnd; subst; ginv; allsimpl; GC.
                  allapply @differ_try_nat_implies; repndors; repnd; subst; [|].

                  { exists (@mk_nat o (f0 n))
                           (@mk_nat o (f0 n))
                           (@mk_nat o (f0 n)).
                    dands; eauto 3 with slow;
                    try (complete (apply reduces_to_if_step; csunf; simpl; dcwf h;
                                   simpl; boolvar; try omega;
                                   rw @Znat.Nat2Z.id; auto)).
                    eapply differ_try_alpha_refl; simpl; eauto 3 with slow; tcsp.
                  }

                  { ex_spfexc. }

                + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                  apply differ_try_exception in d4; repndors; exrepnd; subst;[|].

                  { exists (mk_exception n1 e1)
                           (mk_exception n2 e2)
                           (mk_exception a0 e).
                    dands; eauto 3 with slow.
                    apply implies_differ_try_alpha_exception; eauto 3 with slow.
                  }

                  { ex_spfexc. }

                + pose proof (ind b b []) as h; clear ind.
                  repeat (autodimp h hyp); eauto 3 with slow.
                  pose proof (h t0 t4 x k) as ih; clear h.
                  applydup @preserve_nt_wf_compute_step in comp1; auto.
                  repeat (autodimp ih hyp); eauto 3 with slow.
                  { apply has_value_like_k_eapply_nseq_implies in hv; exrepnd; eauto 3 with slow;[].
                    eapply has_value_like_k_lt; eauto. }
                  exrepnd.

                  exists (mk_eapply (mk_nseq s0) t2')
                         (mk_eapply (mk_nseq s0) t3')
                         (mk_eapply (mk_nseq s0) u').
                  dands; eauto 3 with slow.
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply implies_eapply_red_aux; eauto 3 with slow. }
                  { apply differ_try_alpha_mk_eapply; eauto 3 with slow. }
              }

              { ex_spfexc. }
            }

(*          - SSSCase "NApseq".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_apseq_success in comp; repndors; exrepnd; subst; allsimpl; fold_terms.

            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw <- @wf_apseq_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_nat n0)) x0 x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.

            inversion d3 as [?|? ? ? r|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.
            clear imp1.
            fold_terms.

            exists (@mk_nat o (n n0)) (@mk_nat o (n n0)) (@mk_nat o (n n0)).
            dands; eauto 3 with slow.

            { apply reduces_to_if_step; csunf; simpl.
              rw @Znat.Nat2Z.id.
              boolvar; try omega; auto. }

            { apply reduces_to_if_step; csunf; simpl.
              rw @Znat.Nat2Z.id.
              boolvar; try omega; auto. }

            { apply differ_try_implies_differ_try_alpha.
              apply differ_try_oterm; simpl; tcsp. } *)

          - SSSCase "NFix".
            csunf comp; allsimpl.
            apply compute_step_fix_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp];
              subst; allsimpl; clear d; fold_terms; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_fix_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d2]; subst; clear d1.

            inversion d2 as [?|? ? ? r|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d2; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.

            exists (mk_apply (oterm (Can can1) bs2) (mk_fix (oterm (Can can1) bs2)))
                   (mk_apply (oterm (Can can1) bs3) (mk_fix (oterm (Can can1) bs3)))
                   (mk_apply (oterm (Can can1) bs1) (mk_fix (oterm (Can can1) bs1))).
            dands; eauto 3 with slow.

            apply differ_try_implies_differ_try_alpha.
            apply differ_try_oterm; simpl; tcsp.
            introv j; repndors; cpx; tcsp.

            { constructor; auto ; constructor; allsimpl; auto. }

            { constructor; auto.
              apply differ_try_oterm; simpl; tcsp.
              introv j; repndors; cpx; tcsp. }

          - SSSCase "NSpread".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_spread_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_pair a0 b)) (nobnd a3) (nobnd a2)) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v1,v2] b0) (bterm [v4,v5] b2) (bterm [v0,v3] b1)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.
            destruct x as [l1 t1].
            destruct x0 as [l2 t2].
            allrw @wf_term_pair_iff; exrepnd; ginv; fold_terms; ginv.

            pose proof (imp1 (nobnd a1) (nobnd a3) (nobnd a2)) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b3) (nobnd b5) (nobnd b4)) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.

            exists (lsubst b2 [(v0,a3),(v3,b5)])
                   (lsubst b1 [(v0,a2),(v3,b4)])
                   (lsubst b0 [(v0,a1),(v3,b3)]);
            dands; eauto 4 with slow.

          - SSSCase "NDsup".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_dsup_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_sup a0 b)) (nobnd a3) (nobnd a2)) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v1,v2] b0) (bterm [v4,v5] b2) (bterm [v0,v3] b1)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.
            destruct x as [l1 t1].
            destruct x0 as [l2 t2].
            allrw @wf_term_sup_iff; exrepnd; ginv; fold_terms; ginv.

            pose proof (imp1 (nobnd a1) (nobnd a3) (nobnd a2)) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b3) (nobnd b5) (nobnd b4)) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.

            exists (lsubst b2 [(v0,a3),(v3,b5)])
                   (lsubst b1 [(v0,a2),(v3,b4)])
                   (lsubst b0 [(v0,a1),(v3,b3)]);
            dands; eauto 4 with slow.

          - SSSCase "NDecide".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @terms5.wf_term_decide_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (oterm (Can can1) [nobnd d0])) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v0] b1) (bterm [v6] b4) (bterm [v4] b0)) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v3] b2) (bterm [v7] b5) (bterm [v5] b3)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d4; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.
            destruct x0 as [l1 t1].
            destruct x as [l2 t2].

            pose proof (imp1 (nobnd d0) (bterm l1 t1) (bterm l2 t2)) as d1.
            autodimp d1 hyp.
            clear imp1.
            inversion d1 as [? ? ? ? d2]; subst; clear d1.

            repndors; repnd; subst.

            + exists (lsubst b4 [(v4,t1)])
                     (lsubst b0 [(v4,t2)])
                     (lsubst b1 [(v4,d0)]);
                dands; eauto 4 with slow.

            + exists (lsubst b5 [(v5,t1)])
                     (lsubst b3 [(v5,t2)])
                     (lsubst b2 [(v5,d0)]);
                dands; eauto 4 with slow.

          - SSSCase "NCbv".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl; fold_terms.

            allrw <- @wf_cbv_iff; repnd.

            inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|idtac|].

            { eapply alphaeq_preserves_has_value_like_k in hv;
              [| |apply cbv_subst_bound_nat_try_aux_alpha_eq;eauto 3 with slow];
              [|apply nt_wf_subst; eauto 2 with slow];[].

              inversion d1 as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst;[|]; clear d1.

              { ex_spfexc. }

              allsimpl.

              apply has_value_like_k_mk_less in hv; repndors; eauto 2 with slow;
              try (apply wf_try; eauto 3 with slow; apply wf_apply; eauto 3 with slow);
              [|idtac|]; exrepnd;
              try (complete (allapply @computes_to_exception_in_max_k_steps_can; tcsp));
              [].

              allapply @reduces_atmost_can.
              allunfold @mk_integer; ginv; fold_terms.
              allsimpl; cpx; GC; fold_terms.

              clear imp.

              boolvar.

              { allapply @has_value_like_k_vbot; tcsp. }

              pose proof (Wf_Z.Z_of_nat_complete_inf i1) as hi1.
              autodimp hi1 hyp; exrepnd; subst; fold_terms.

              eapply eq_fun2TE_alpha_eq in eqf;[| | |exact aeq1|exact aeq2];
              eauto 3 with slow;[].

              pose proof (eqf n) as q.
              repndors; exrepnd;[|].

              - exists v1 v2 v1.
                dands; eauto 3 with slow.

                + eapply reduces_to_trans;
                  [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                  allunfold @computes_to_value; repnd.
                  eapply reduces_to_trans;[eapply reduces_to_prinarg;exact q5|].
                  apply isvalue_implies_iscan in q0; apply iscan_implies in q0; repndors; exrepnd; subst.

                  { eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                  { eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                + eapply reduces_to_trans;
                  [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                  allunfold @computes_to_value; repnd.
                  eapply reduces_to_trans;[eapply reduces_to_prinarg;exact q4|].
                  apply isvalue_implies_iscan in q2; apply iscan_implies in q2; repndors; exrepnd; subst.

                  { eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                  { eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                + pose proof (cbv_subst_bound_nat_try_aux_alpha_eq a v z1 e1 f') as aeq.
                  unfsubst; simpl.
                  allrw <- @beq_var_refl; fold_terms.
                  match goal with
                    | [ |- context[mk_fix ?x] ] => remember (mk_fix x) as b
                  end; clear Heqb.
                  rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[].
                  rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[].
                  eapply reduces_to_if_split2;
                    [csunf;simpl;dcwf h; simpl;unfold compute_step_comp;simpl;auto|];[].
                  boolvar; tcsp; try omega;[].
                  unfold nobnd.
                  eapply reduces_to_trans;
                    [apply reduces_to_prinarg;
                      apply computes_to_value_implies_reduces_to;
                      exact q0|].
                  allunfold @computes_to_value; repnd.
                  apply isvalue_implies_iscan in q0; apply iscan_implies in q0; repndors; exrepnd; subst.

                  { eapply reduces_to_trans;
                    [apply reduces_to_if_step;csunf;simpl;auto|];[].
                    apply reduces_to_if_step.
                    csunf; simpl; auto.
                    dcwf h; simpl.
                    unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                  { eapply reduces_to_trans;
                    [apply reduces_to_if_step;csunf;simpl;auto|];[].
                    apply reduces_to_if_step.
                    csunf; simpl; auto.
                    dcwf h; simpl.
                    unfold compute_step_comp; simpl; boolvar; ginv; tcsp. }

                + eapply differ_try_alpha_alpha_eq3;[exact q3|].
                  apply differ_try_alpha_refl; auto.

              - apply cequiv_spexc in q.
                apply cequiv_spexc in q0.
                exrepnd.

                exists (spexc a) (spexc a)
                       (subst
                          (mk_less (mk_var v) mk_zero (mk_vbot z1)
                                   (mk_try (mk_apply f' (mk_var v)) (mk_utoken a) e1 c')) v
                          (mk_nat n)).
                dands; tcsp; eauto 3 with slow.

                + eapply reduces_to_trans;
                  [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                  allunfold @computes_to_value; repnd.
                  eapply reduces_to_trans;[eapply reduces_to_prinarg;exact q4|].
                  eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                  eapply reduces_to_trans;
                    [eapply reduce_to_prinargs_comp_can;
                      [apply reduces_to_symm
                      |idtac
                      |exact q9]
                    |]; eauto 3 with slow;[].
                  apply reduces_to_if_step; csunf; simpl.
                  dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp.

                + eapply reduces_to_trans;
                  [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                  allunfold @computes_to_value; repnd.
                  eapply reduces_to_trans;[eapply reduces_to_prinarg;exact q1|].
                  eapply reduces_to_trans;[apply reduces_to_if_step; csunf; simpl;auto|].
                  eapply reduces_to_trans;
                    [eapply reduce_to_prinargs_comp_can;
                      [apply reduces_to_symm
                      |idtac
                      |exact q7]
                    |]; eauto 3 with slow;[].
                  apply reduces_to_if_step; csunf; simpl.
                  dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; ginv; tcsp.
            }

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_cbv_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a1) (nobnd a0)) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] x) (bterm [v0] b0) (bterm [v1] b)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

            { ex_spfexc. }

            exists (lsubst b0 [(v1,oterm (Can can1) bs2)])
                   (lsubst b [(v1,oterm (Can can1) bs3)])
                   (lsubst x [(v1,oterm (Can can1) bs1)]);
              dands; eauto 4 with slow.

          - SSSCase "NSleep".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_sleep_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_integer z)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d2; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl; fold_terms.

            exists (@mk_axiom o) (@mk_axiom o) (@mk_axiom o).
            dands; eauto 3 with slow.
            apply differ_try_alpha_refl; simpl; tcsp.

          - SSSCase "NTUni".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_tuni_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_nat n)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d2; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl; fold_terms.

            exists (@mk_uni o n) (@mk_uni o n) (@mk_uni o n).
            dands; eauto 3 with slow;
            try (complete (apply reduces_to_if_step; csunf; simpl; unfold compute_step_tuni;
                           simpl; boolvar; tcsp; try omega; allrw @Znat.Nat2Z.id; auto)).
            apply differ_try_alpha_refl; simpl; tcsp.

          - SSSCase "NMinus".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_minus_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (mk_integer z)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d2; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl; fold_terms.

            exists (@mk_integer o (- z))
                   (@mk_integer o (- z))
                   (@mk_integer o (- z));
              dands; eauto 3 with slow.
            apply differ_try_alpha_refl; simpl; tcsp.

          - SSSCase "NFresh".
            clear ind indhyp.
            csunf comp; allsimpl; ginv.

          - SSSCase "NTryCatch".
            csunf comp; allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_try_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a3) (nobnd a2)) as d1.
            autodimp d1 hyp.
            pose proof (imp (nobnd b) (nobnd b1) (nobnd b0)) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v0] c0) (bterm [v2] c2) (bterm [v1] c1)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? ? d6]; subst; clear d3.

            inversion d4 as [?|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d4; GC;[|].

            { applydup @if_has_value_like_k_ncompop_can_same in hv; exrepnd; eauto 3 with slow;[].

              repndors;[|].

              - unfold ispk in hv0; exrepnd; subst.

                pose proof (indhyp b b1 b0 (pk2term pk) j) as h.
                repeat (autodimp h hyp); eauto 3 with slow; exrepnd.
                apply differ_try_alpha_pk2term in h1.

                repndors;repnd;subst;[|].

                + ex_spfexc;
                  eapply reduces_to_trans;
                  [apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                  |idtac
                  |apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                  |].

                  * eapply reduces_to_trans;
                    [eapply reduce_to_prinargs_comp;
                      [apply computes_to_value_if_reduces_to;[exact h0|]
                      |idtac
                      |apply reduces_to_lfresh_utoken]
                    |]; eauto 3 with slow;[].
                    apply reduces_to_if_step.
                    csunf; simpl; rw @pk2term_eq; dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; allrw not_over_or; tcsp.

                  * eapply reduces_to_trans;
                    [eapply reduce_to_prinargs_comp;
                      [apply computes_to_value_if_reduces_to;[exact h2|]
                      |idtac
                      |apply reduces_to_lfresh_utoken]
                    |]; eauto 3 with slow;[].
                    apply reduces_to_if_step.
                    csunf; simpl; rw @pk2term_eq; dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; allrw not_over_or; tcsp.

                + ex_spfexc_h h1; allunfold @spfexc_pair; exrepnd; subst;
                  eapply reduces_to_trans;
                  [apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                  |idtac
                  |apply implies_reduces_to_trycatch;apply computes_to_exception_refl
                  |].

                  * eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;exact h0|].
                    eauto 3 with slow.

                  * eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;exact h2|].
                    eauto 3 with slow.

              - applydup @reduces_in_atmost_k_steps_preserves_wf in hv2; auto.
                apply wf_isexc_implies in hv0; exrepnd; subst; auto.

                pose proof (indhyp b b1 b0 (mk_exception a0 e) j) as h.
                repeat (autodimp h hyp); eauto 3 with slow; exrepnd.
                apply differ_try_alpha_exception in h1.

                repndors; exrepnd; subst.

                + exists (mk_exception n1 e1) (mk_exception n2 e2) (mk_exception a0 e).
                  allunfold @spfexc_pair; exrepnd; subst; dands; eauto 3 with slow.

                  * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact h0|].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact h2|].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  * eapply reduces_to_trans;[apply reduces_to_prinarg;exists j; exact hv2|].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  * apply implies_differ_try_alpha_exception; auto.

                + ex_spfexc_h h1; allunfold @spfexc_pair; exrepnd; subst.

                  * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact h0|].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  * eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact h2|].
                    apply reduces_to_if_step; csunf; simpl; auto.
            }

            exists (mk_atom_eq b1 b1 (oterm (Can can1) bs2) mk_bot)
                   (mk_atom_eq b0 b0 (oterm (Can can1) bs3) mk_bot)
                   (mk_atom_eq b b (oterm (Can can1) bs1) mk_bot);
            dands; eauto 4 with slow.

            apply differ_try_implies_differ_try_alpha.
            apply differ_try_oterm; simpl; tcsp;[].

            introv i; repndors; ginv; tcsp; constructor; auto.
            apply differ_try_refl; simpl; tcsp.

          - SSSCase "NParallel".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.
            allrw @wf_term_parallel_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.
            allsimpl.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            pose proof (imp (nobnd b) (nobnd b1) (nobnd b0)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d3]; subst; clear d1.

            inversion d3 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

            { ex_spfexc. }

            exists (@mk_axiom o) (@mk_axiom o) (@mk_axiom o).
            dands; eauto 3 with slow.
            apply differ_try_alpha_refl; simpl; tcsp.

          - SSSCase "NCompOp".
            apply compute_step_ncompop_can1_success in comp; repnd.
            repndors; exrepnd; subst.

            + apply compute_step_compop_success_can_can in comp1;
              exrepnd; subst; allsimpl; ginv; GC.

              repndors; exrepnd; subst; allrw @get_param_from_cop_some; subst;
              allsimpl; fold_terms; allrw <- @pk2term_eq.

              * inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

                { ex_spfexc. }

                cpx; allsimpl.

                pose proof (imp (nobnd (mk_integer n1)) x0 x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd (mk_integer n2)) y0 y) as d2.
                autodimp d2 hyp.
                pose proof (imp (nobnd t4) z0 z) as d3.
                autodimp d3 hyp.
                pose proof (imp (nobnd t5) u0 u) as d4.
                autodimp d4 hyp.
                clear imp.

                inversion d1 as [? ? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? ? d6]; subst; clear d2.
                inversion d3 as [? ? ? ? d7]; subst; clear d3.
                inversion d4 as [? ? ? ? d8]; subst; clear d4.

                inversion d5 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d5; GC;[|].

                { ex_spfexc. }

                cpx.
                clear imp1.
                inversion d6 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d6; GC;[|].

                { ex_spfexc. }

                cpx.
                clear imp1.

                exists (if Z_lt_le_dec n1 n2 then t7 else t9)
                       (if Z_lt_le_dec n1 n2 then t8 else t10)
                       (if Z_lt_le_dec n1 n2 then t4 else t5).
                dands; eauto 3 with slow.
                boolvar; eauto 3 with slow.

              * inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

                { ex_spfexc. }

                cpx; allsimpl.

                pose proof (imp (nobnd (pk2term pk1)) x0 x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd (pk2term pk2)) y0 y) as d2.
                autodimp d2 hyp.
                pose proof (imp (nobnd t4) z0 z) as d3.
                autodimp d3 hyp.
                pose proof (imp (nobnd t5) u0 u) as d4.
                autodimp d4 hyp.
                clear imp.

                inversion d1 as [? ? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? ? d6]; subst; clear d2.
                inversion d3 as [? ? ? ? d7]; subst; clear d3.
                inversion d4 as [? ? ? ? d8]; subst; clear d4.

                apply differ_try_pk2term in d5; repndors; exrepnd; subst;[|].

                { apply differ_try_pk2term in d6; repndors; exrepnd; subst;[|].

                  { exists (if param_kind_deq pk1 pk2 then t7 else t9)
                           (if param_kind_deq pk1 pk2 then t8 else t10)
                           (if param_kind_deq pk1 pk2 then t4 else t5).
                    dands; eauto 3 with slow;
                    try (apply reduces_to_if_step; csunf; simpl; allrw @pk2term_eq;
                         dcwf h; simpl;
                         unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto).
                    boolvar; eauto 3 with slow. }

                  { ex_spfexc;
                    try (eapply reduces_to_trans;
                         [eapply reduce_to_prinargs_comp_can;
                           [apply reduces_to_symm
                           |idtac
                           |exact ct1]
                         |]; eauto 3 with slow);
                    try (eapply reduces_to_trans;
                         [eapply reduce_to_prinargs_comp_can;
                           [apply reduces_to_symm
                           |idtac
                           |exact ct2]
                         |]; eauto 3 with slow);
                    try (apply reduces_to_if_step; csunf; simpl; allrw @pk2term_eq;
                         dcwf h; simpl;
                         unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto). }
                }

                { ex_spfexc;
                  try (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_comp_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct1]
                       |]; eauto 3 with slow);
                  try (eapply reduces_to_trans;
                       [eapply reduce_to_prinargs_comp_can;
                         [apply reduces_to_symm
                         |idtac
                         |exact ct2]
                       |]; eauto 3 with slow);
                  try (apply reduces_to_if_step; csunf; simpl; allrw @pk2term_eq;
                       dcwf h; simpl;
                       unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto). }

            + inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              destruct bs2 as [|u1 bs2]; allsimpl; cpx;[].
              destruct bs2 as [|u2 bs2]; allsimpl; cpx;[].
              destruct bs3 as [|v1 bs3]; allsimpl; cpx;[].
              destruct bs3 as [|v2 bs3]; allsimpl; cpx;[].

              pose proof (imp (nobnd (oterm (Can can1) bs1)) u1 v1) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd t) u2 v2) as d2.
              autodimp d2 hyp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|?|? ? ? ? len3 len4 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              pose proof (ind t t []) as q; clear ind.
              repeat (autodimp q hyp);eauto 3 with slow;[].

              apply if_has_value_like_k_ncompop_can1 in hv; exrepnd.
              allrw @wf_term_ncompop_iff; exrepnd; ginv.
              allsimpl.
              pose proof (imp (nobnd c1) (nobnd c3) (nobnd c2)) as h1; autodimp h1 hyp.
              pose proof (imp (nobnd d) (nobnd d1) (nobnd d0)) as h2; autodimp h2 hyp.
              inversion h1 as [? ? ? ? h3]; subst; clear h1.
              inversion h2 as [? ? ? ? h4]; subst; clear h2.

              pose proof (q b1 b0 t' j) as ih; clear q.
              repeat (autodimp ih hyp); eauto 2 with slow;[|].

              { introv l w1 w2 w3 isv r d'.
                apply (indhyp t1 t2 t3 v m); eauto 3 with slow; try omega. }

              exrepnd.
              exists (mk_compop c0 (oterm (Can can1) bs4) t2' c3 d1)
                     (mk_compop c0 (oterm (Can can1) bs5) t3' c2 d0)
                     (mk_compop c0 (oterm (Can can1) bs1) u' c1 d).
              dands; eauto 3 with slow.

              { eapply reduce_to_prinargs_comp_can; eauto 3 with slow. }
              { eapply reduce_to_prinargs_comp_can; eauto 3 with slow. }
              { eapply reduce_to_prinargs_comp_can; eauto 3 with slow. }
              { apply implies_differ_try_alpha_compop; eauto 3 with slow. }

            + allrw @wf_term_ncompop_iff; exrepnd; ginv.
              allunfold @nobnd.
              repeat (destruct bs'; ginv);[].
              apply wf_isexc_implies in comp1; exrepnd; subst; auto;[].
              inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              cpx; allsimpl.

              pose proof (imp (nobnd (oterm (Can can1) bs1)) x0 x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd (mk_exception a0 e)) y0 y) as d2.
              autodimp d2 hyp.
              pose proof (imp (nobnd c1) z0 z) as d3.
              autodimp d3 hyp.
              pose proof (imp (nobnd d0) u0 u) as d4.
              autodimp d4 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? ? d6]; subst; clear d2.
              inversion d3 as [? ? ? ? d7]; subst; clear d3.
              inversion d4 as [? ? ? ? d8]; subst; clear d4.

              inversion d5 as [|?|?|?|? ? ? ? len3 len4 nia imp1]; subst; allsimpl; clear d5; GC;[|].

              { ex_spfexc. }

              apply differ_try_exception in d6; repndors; exrepnd; subst;
              [|ex_spfexc;
                 try (eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ct1]
                      |]; eauto 3 with slow);
                 try (eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ct2]
                      |]; eauto 3 with slow);
                 try (apply reduces_to_if_step; csunf; simpl; allrw @pk2term_eq;
                      dcwf h; simpl;
                      unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto)
              ];[].

              exists (mk_exception n1 e1) (mk_exception n2 e2) (mk_exception a0 e).
              dands; eauto 3 with slow;
              try (complete (apply reduces_to_if_step; csunf; simpl; dcwf h));[].
              apply implies_differ_try_alpha_exception; eauto 3 with slow.

          - SSSCase "NArithOp".
            apply compute_step_narithop_can1_success in comp; repnd.
            repndors; exrepnd; subst.

            + apply compute_step_arithop_success_can_can in comp1;
              exrepnd; subst; allsimpl; ginv; GC.

              allrw @get_param_from_cop_some; subst;
              allsimpl; fold_terms; allrw <- @pk2term_eq.

              inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              cpx; allsimpl.

              pose proof (imp (nobnd (mk_integer n1)) x0 x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd (mk_integer n2)) y0 y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              cpx.
              clear imp1.
              inversion d4 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d4; GC;[|].

              { ex_spfexc. }

              cpx.
              clear imp1.

              exists (@mk_integer o (get_arith_op a0 n1 n2))
                     (@mk_integer o (get_arith_op a0 n1 n2))
                     (@mk_integer o (get_arith_op a0 n1 n2)).
              dands; eauto 3 with slow.
              apply differ_try_implies_differ_try_alpha.
              apply differ_try_oterm; simpl; tcsp.

            + inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              allrw @wf_term_narithop_iff; exrepnd.
              repeat (destruct bs'; allsimpl; ginv).
              allsimpl.

              pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a3) (nobnd a2)) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd b) (nobnd b1) (nobnd b0)) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|?|? ? ? ? len3 len4 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              pose proof (ind b b []) as q; clear ind.
              repeat (autodimp q hyp);eauto 3 with slow;[].
              apply if_has_value_like_k_narithop_can1 in hv; exrepnd.
              pose proof (q b1 b0 t' j) as ih; clear q.
              repeat (autodimp ih hyp); eauto 2 with slow;[|].

              { introv l w1 w2 w3 isv r d'.
                apply (indhyp t1 t2 t3 v m); eauto 3 with slow; try omega. }

              exrepnd.
              exists (mk_arithop a0 (oterm (Can can1) bs2) t2')
                     (mk_arithop a0 (oterm (Can can1) bs3) t3')
                     (mk_arithop a0 (oterm (Can can1) bs1) u').
              dands; eauto 3 with slow.

              { eapply reduce_to_prinargs_arith_can; eauto 3 with slow. }
              { eapply reduce_to_prinargs_arith_can; eauto 3 with slow. }
              { eapply reduce_to_prinargs_arith_can; eauto 3 with slow. }
              { apply implies_differ_try_alpha_arithop; eauto 3 with slow. }

            + allrw @wf_term_narithop_iff; exrepnd; ginv.
              allunfold @nobnd.
              repeat (destruct bs'; ginv);[].
              apply wf_isexc_implies in comp1; exrepnd; subst; auto;[].
              inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

              { ex_spfexc. }

              cpx; allsimpl.

              pose proof (imp (nobnd (oterm (Can can1) bs1)) x0 x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd (mk_exception a1 e)) y0 y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|?|? ? ? ? len3 len4 nia imp1]; subst; allsimpl; clear d3; GC;[|].

              { ex_spfexc. }

              apply differ_try_exception in d4; repndors; exrepnd; subst;
              [|ex_spfexc;
                 try (eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_arith_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ct1]
                      |]; eauto 3 with slow);
                 try (eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_arith_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ct2]
                      |]; eauto 3 with slow);
                 try (apply reduces_to_if_step; csunf; simpl; allrw @pk2term_eq;
                      dcwf h; simpl;
                      unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto)
              ];[].

              exists (mk_exception n1 e1) (mk_exception n2 e2) (mk_exception a1 e).
              dands; eauto 3 with slow;
              try (complete (apply reduces_to_if_step; csunf; simpl; dcwf h));[].
              apply implies_differ_try_alpha_exception; eauto 3 with slow.

          - SSSCase "NCanTest".
            clear ind indhyp.
            csunf comp; allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl; fold_terms.
            inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; GC; allsimpl.

            allrw @wf_term_cantest_iff; exrepnd; allunfold @nobnd; ginv; fold_terms.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) (nobnd a2) (nobnd a1)) as d1.
            autodimp d1 hyp.
            pose proof (imp (nobnd b) (nobnd b1) (nobnd b0)) as d2.
            autodimp d2 hyp.
            pose proof (imp (nobnd c1) (nobnd c3) (nobnd c2)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|?|? ? ? ? len1 len2 nia imp1]; subst; allsimpl; clear d4; GC;[|].

            { ex_spfexc. }

            exists (if canonical_form_test_for c0 can1 then b1 else c3)
                   (if canonical_form_test_for c0 can1 then b0 else c2)
                   (if canonical_form_test_for c0 can1 then b else c1);
            dands; eauto 4 with slow.
            remember (canonical_form_test_for c0 can1) as cc; destruct cc; eauto 3 with slow.
        }

        { SSCase "NCan".
          rw @compute_step_ncan_ncan in comp.
          remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp'.
          symmetry in Heqcomp'; destruct comp'; ginv;[].

          dup hv as hv'.
          apply if_has_value_like_k_ncan_primarg in hv; exrepnd.
          applydup @differ_try_ncan_ncan in d as d'; repndors; exrepnd; subst;
          try (complete ex_spfexc);[].
          allsimpl.

          apply wf_oterm_iff in wt1; repnd; allsimpl.
          pose proof (wt1 (bterm [] (oterm (NCan ncan1) bs1))) as wb1; autodimp wb1 hyp.
          apply wf_oterm_iff in wt2; repnd; allsimpl.
          pose proof (wt2 (nobnd t1)) as wb2; autodimp wb2 hyp.
          apply wf_oterm_iff in wt3; repnd; allsimpl.
          pose proof (wt3 (nobnd t0)) as wb3; autodimp wb3 hyp.
          allrw @wf_bterm_iff.

          pose proof (ind (oterm (NCan ncan1) bs1) (oterm (NCan ncan1) bs1) []) as q.
          repeat (autodimp q hyp); eauto 3 with slow; clear ind;[].
          pose proof (q t1 t0 n j) as ih; clear q.
          repeat (autodimp ih hyp).

          { introv l w1 w2 w3 isv r d'.
            apply (indhyp t2 t3 t4 v m); eauto 3 with slow; try omega. }

          exrepnd.

          inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|idtac|].

          - clear wt1 wt2 wt3 wt5.
            fold_terms.
            applydup @has_value_like_k_bound_nat_try_aux in hv'; exrepnd; eauto 3 with slow.
            repndors; exrepnd.

            + eapply reduces_in_atmost_k_steps_if_reduces_to in hv'2;[|exact ih3|]; eauto 3 with slow; exrepnd.
              pose proof (indhyp u' t2' t3' (mk_nat n0) k') as q.

              applydup @compute_step_preserves_wf in Heqcomp'; auto;[].
              applydup @reduces_to_preserves_wf in ih1; auto;[].
              applydup @reduces_to_preserves_wf in ih2; auto;[].
              applydup @reduces_to_preserves_wf in ih3; auto;[].
              repeat (autodimp q hyp); eauto 3 with slow; try omega;[].
              exrepnd.
              apply differ_try_alpha_nat in q1; repndors; repnd; subst;[|].

              * eapply eq_fun2TE_alpha_eq in eqf;[| | |exact aeq1|exact aeq2]; eauto 3 with slow;[].
                pose proof (eqf n0) as r.
                repeat (autodimp r hyp); eauto 3 with slow.

                repndors; exrepnd.

                { allunfold @computes_to_value; repnd.
                  exists v1 v2 v1.
                  dands; eauto 3 with slow.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih1|exact q0]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact r5|].
                    apply isvalue_implies_iscan in r0; apply iscan_implies in r0; repndors; exrepnd; subst.

                    { eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih2|exact q2]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact r4|].
                    apply isvalue_implies_iscan in r2; apply iscan_implies in r2; repndors; exrepnd; subst.

                    { eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih3|exists k'; exact hv'1]
                    |]; fold_terms.
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_try_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact r5
                      |]; fold_terms.
                    apply isvalue_implies_iscan in r0; apply iscan_implies in r0; repndors; exrepnd; subst.

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply differ_try_alpha_alpha_eq3;[exact r3|].
                    apply differ_try_alpha_refl; auto.
                }

                { rename r0 into ceq1.
                  rename r into ceq2.
                  apply cequiv_spexc in ceq1.
                  apply cequiv_spexc in ceq2.
                  exrepnd.

                  exists (spexc a) (spexc a)
                         (mk_cbv n x1
                                 (mk_less (mk_var x1) mk_zero (mk_vbot z1)
                                          (mk_try (mk_apply f' (mk_var x1)) (mk_utoken a) e1 c'))).
                  dands; eauto 3 with slow.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih1|exact q0]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    allunfold @computes_to_value; repnd.
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact ceq4|].
                    eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ceq9]
                      |]; eauto 3 with slow;[].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih2|exact q2]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    allunfold @computes_to_value; repnd.
                    eapply reduces_to_trans;[apply reduces_to_prinarg;exact ceq0|].
                    eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ceq7]
                      |]; eauto 3 with slow;[].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; allsimpl; unfold compute_step_comp; simpl; boolvar; tcsp.
                }

              * ex_spfexc; dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

            + unfold computes_to_exception_in_max_k_steps in hv'1.
              eapply reduces_in_atmost_k_steps_if_reduces_to in hv'1;[|exact ih3|]; eauto 3 with slow; exrepnd.
              pose proof (indhyp u' t2' t3' (mk_exception n0 e) k') as q.

              applydup @compute_step_preserves_wf in Heqcomp'; auto;[].
              applydup @reduces_to_preserves_wf in ih1; auto;[].
              applydup @reduces_to_preserves_wf in ih2; auto;[].
              applydup @reduces_to_preserves_wf in ih3; auto;[].
              repeat (autodimp q hyp); eauto 3 with slow; try omega;[].
              exrepnd.
              apply differ_try_alpha_exception in q1; repndors;[|]; exrepnd; subst.

              * exists (mk_exception n1 e0) (mk_exception n2 e4) (mk_exception n0 e).
                dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih3|exists k'; exact hv'2]
                  |]; fold_terms.
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { apply implies_differ_try_alpha_exception; auto. }

              * ex_spfexc; dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

          - ex_spfexc; ginv.

          - cpx.
            exists (oterm (NCan ncan) (nobnd t2' :: bs0))
                   (oterm (NCan ncan) (nobnd t3' :: bs2))
                   (oterm (NCan ncan) (nobnd u' :: bs)).
            dands; eauto 3 with slow.

            { eapply reduces_to_prinarg; auto. }
            { eapply reduces_to_prinarg; auto. }
            { eapply reduces_to_prinarg; auto. }

            { unfold differ_try_alpha in ih0; exrepnd.
              exists (oterm (NCan ncan) (nobnd u1 :: bs))
                     (oterm (NCan ncan) (nobnd u2 :: bs0))
                     (oterm (NCan ncan) (nobnd u3 :: bs2)).
              dands; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply differ_try_oterm; simpl; try omega; tcsp;[].
                introv i; repndors; ginv; tcsp.
                constructor; auto.
            }
        }

        { SSCase "Exc".
          csunf comp; allsimpl.
          apply compute_step_catch_success in comp.
          repndors; exrepnd; subst; fold_terms;[|].

          - inversion d as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

            { ex_spfexc. }

            cpx; allsimpl.
            pose proof (imp (nobnd (mk_exception a' e)) x0 x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd a0) y0 y) as d2; autodimp d2 hyp.
            pose proof (imp (bterm [v] b) z0 z) as d3; autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? ? d6]; subst; clear d3.

            apply differ_try_exception in d4; repndors; exrepnd; subst.

            + exists (mk_atom_eq t0 n1 (subst t5 v e1) (mk_exception n1 e1))
                     (mk_atom_eq t4 n2 (subst t6 v e2) (mk_exception n2 e2))
                     (mk_atom_eq a0 a' (subst b v e) (mk_exception a' e)).
              dands; eauto 3 with slow.

              apply implies_differ_try_alpha_compop; eauto 3 with slow.
              apply implies_differ_try_alpha_exception; eauto 3 with slow.

            + allrw <- @wf_try_iff; repnd.
              allrw @wf_exception_iff; repnd.

              applydup @if_has_value_like_k_ncompop in hv; auto;
              try (apply wf_exception_iff; dands; auto);
              try (apply wf_term_subst; auto);[].
              exrepnd.
              repndors.

              * pose proof (indhyp a0 t0 t4 v0 j) as q.
                repeat (autodimp q hyp); try omega; eauto 3 with slow;[].
                exrepnd.
                eapply differ_try_alpha_iswfpk in q1;[|exact hv0].
                repndors; repnd; subst.

                { ex_spfexc; dands; eauto 3 with slow.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;
                      [apply reduce_to_prinargs_comp;
                        [apply computes_to_value_if_reduces_to;[exact q0|]
                        |idtac
                        |apply reduces_to_lfresh_utoken]
                      |]; eauto 3 with slow;[].
                    apply reduces_to_if_step.
                    allunfold @iswfpk.
                    allunfold @ispk; exrepnd; subst.
                    allrw @pk2term_eq; allsimpl.
                    csunf; simpl.
                    dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; tcsp.
                    allrw not_over_or; sp.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;
                      [apply reduce_to_prinargs_comp;
                        [apply computes_to_value_if_reduces_to;[exact q2|]
                        |idtac
                        |apply reduces_to_lfresh_utoken]
                      |];eauto 3 with slow;[].
                    apply reduces_to_if_step.
                    csunf; simpl.
                    allunfold @iswfpk.
                    allunfold @ispk.
                    exrepnd; subst.
                    allrw @pk2term_eq.
                    dcwf h; simpl; allrw @co_wf_pk2can; ginv;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; subst; allsimpl; tcsp.
                    allrw not_over_or; sp.
                }

                { ex_spfexc_h q1; allunfold @spfexc_pair; exrepnd; subst.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q0] |].
                    eapply reduces_to_if_step; csunf; simpl; auto.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q2] |].
                    eapply reduces_to_if_step; csunf; simpl; auto.
                }

              * pose proof (indhyp a0 t0 t4 v0 j) as q.
                repeat (autodimp q hyp); try omega; eauto 3 with slow;[].
                exrepnd.
                applydup @reduces_in_atmost_k_steps_preserves_wf in hv2; auto;[].
                apply wf_isexc_implies in hv0; auto;[].
                exrepnd; subst.
                apply differ_try_alpha_exception in q1; exrepnd.
                repndors; exrepnd; subst.

                { exists (mk_exception n1 e1)
                         (mk_exception n2 e2)
                         (mk_exception a1 e0).
                  dands; eauto 3 with slow; allunfold @spfexc_pair; exrepnd; subst.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q0] |].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q2] |].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  - eapply reduces_to_trans;[eapply reduces_to_prinarg;[exists j;exact hv2] |].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  - apply implies_differ_try_alpha_exception; eauto 3 with slow.
                }

                { ex_spfexc_h q1; allunfold @spfexc_pair; exrepnd; subst.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q0] |].
                    apply reduces_to_if_step; csunf; simpl; auto.

                  - eapply reduces_to_trans;[apply reduces_to_if_step;csunf;simpl;auto|].
                    eapply reduces_to_trans;[eapply reduces_to_prinarg;[exact q2] |].
                    apply reduces_to_if_step; csunf; simpl; auto.
                }

          - inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; fold_terms;GC;[|idtac|].

            { inversion d1 as [|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; GC.
              { ex_spfexc. }
              exists (oterm Exc bs2) (oterm Exc bs3) (oterm Exc bs1).
              dands; eauto 3 with slow.
            }

            { ex_spfexc. }

            destruct bs2; allsimpl; cpx.
            destruct bs3; allsimpl; cpx.

            pose proof (imp (nobnd (oterm Exc bs1)) b b0) as d1; autodimp d1 hyp.
            inversion d1 as [? ? ? ? d2]; subst; clear d1.
            inversion d2 as [|?|?|?|? ? ? ? len3 len4 nia imp1]; subst; allsimpl; GC.
            { ex_spfexc.
              - apply reduces_to_if_step; csunf; simpl.
                rw @compute_step_catch_if_diff; auto.
              - apply reduces_to_if_step; csunf; simpl.
                rw @compute_step_catch_if_diff; auto. }
            exists (oterm Exc bs4) (oterm Exc bs5) (oterm Exc bs1).
            dands; eauto 3 with slow.
            { apply reduces_to_if_step; csunf; simpl.
              rw @compute_step_catch_if_diff; auto. }
            { apply reduces_to_if_step; csunf; simpl.
              rw @compute_step_catch_if_diff; auto. }
        }

        { SSCase "Abs".
          rw @compute_step_ncan_abs in comp.
          remember (compute_step_lib lib abs1 bs1) as comp'.
          symmetry in Heqcomp'; destruct comp'; ginv;[].

          dup hv as hv'.
          apply if_has_value_like_k_ncan_primarg in hv; exrepnd.
          applydup @differ_try_ncan_abs in d as d'; repndors; exrepnd; subst;
          try (complete ex_spfexc);[].
          allsimpl.

          apply wf_oterm_iff in wt1; repnd; allsimpl.
          pose proof (wt1 (bterm [] (oterm (Abs abs1) bs1))) as wb1; autodimp wb1 hyp.
          apply wf_oterm_iff in wt2; repnd; allsimpl.
          pose proof (wt2 (nobnd t1)) as wb2; autodimp wb2 hyp.
          apply wf_oterm_iff in wt3; repnd; allsimpl.
          pose proof (wt3 (nobnd t0)) as wb3; autodimp wb3 hyp.
          allrw @wf_bterm_iff.
          applydup @wf_compute_step_lib in Heqcomp' as wn; auto;[].

          pose proof (ind (oterm (Abs abs1) bs1) (oterm (Abs abs1) bs1) []) as q.
          repeat (autodimp q hyp); eauto 3 with slow; clear ind;[].
          pose proof (q t1 t0 n j) as ih; clear q.
          repeat (autodimp ih hyp).

          { introv l w1 w2 w3 isv r d'.
            apply (indhyp t2 t3 t4 v m); eauto 3 with slow; try omega. }

          exrepnd.

          inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|?|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|idtac|].

          - clear wt1 wt2 wt3 wt5.
            fold_terms.
            applydup @has_value_like_k_bound_nat_try_aux in hv'; exrepnd; eauto 3 with slow;[].
            repndors; exrepnd.

            + eapply reduces_in_atmost_k_steps_if_reduces_to in hv'2;[|exact ih3|]; eauto 3 with slow; exrepnd;[].
              pose proof (indhyp u' t2' t3' (mk_nat n0) k') as q.

              applydup @reduces_to_preserves_wf in ih1; auto;[].
              applydup @reduces_to_preserves_wf in ih2; auto;[].
              applydup @reduces_to_preserves_wf in ih3; auto;[].
              repeat (autodimp q hyp); eauto 3 with slow; try omega;[].
              exrepnd.
              apply differ_try_alpha_nat in q1; repndors; repnd; subst;[|].

              * eapply eq_fun2TE_alpha_eq in eqf;[| | |exact aeq1|exact aeq2]; eauto 3 with slow;[].
                pose proof (eqf n0) as r.
                repeat (autodimp r hyp); eauto 3 with slow.

                repndors; exrepnd.

                { allunfold @computes_to_value; repnd.
                  exists v1 v2 v1.
                  dands; eauto 3 with slow.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih1|exact q0]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact r5
                      |]; fold_terms.
                    apply isvalue_implies_iscan in r0; apply iscan_implies in r0; repndors; exrepnd; subst.

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih2|exact q2]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact r4
                      |]; fold_terms.
                    apply isvalue_implies_iscan in r2; apply iscan_implies in r2; repndors; exrepnd; subst.

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih3|exists k'; exact hv'1]
                    |]; fold_terms.
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_try_aux_nat|]; eauto 3 with slow.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact r5
                      |]; fold_terms.
                    apply isvalue_implies_iscan in r0; apply iscan_implies in r0; repndors; exrepnd; subst.

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                    { eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl.
                      unfold compute_step_comp; simpl; boolvar; tcsp. }

                  - eapply differ_try_alpha_alpha_eq3;[exact r3|].
                    apply differ_try_alpha_refl; auto.
                }

                { rename r0 into ceq1.
                  rename r into ceq2.
                  apply cequiv_spexc in ceq1.
                  apply cequiv_spexc in ceq2.
                  exrepnd.

                  exists (spexc a) (spexc a)
                         (mk_cbv n x1
                                 (mk_less (mk_var x1) mk_zero (mk_vbot z1)
                                          (mk_try (mk_apply f' (mk_var x1)) (mk_utoken a) e1 c'))).
                  dands; eauto 3 with slow.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih1|exact q0]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    allunfold @computes_to_value; repnd.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact ceq4
                      |]; fold_terms.
                    eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                    eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ceq9]
                      |]; eauto 3 with slow;[].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; simpl.
                    unfold compute_step_comp; simpl; boolvar; tcsp.

                  - eapply reduces_to_trans;
                    [eapply reduces_to_prinarg;
                      eapply reduces_to_trans;[exact ih2|exact q2]
                    |].
                    eapply reduces_to_trans;
                      [apply reduces_to_bound_nat_aux_nat|]; eauto 3 with slow.
                    allunfold @computes_to_value; repnd.
                    eapply reduces_to_trans;
                      [eapply reduces_to_prinarg;exact ceq0
                      |]; fold_terms.
                    eapply reduces_to_trans;
                      [apply reduces_to_if_step; csunf; simpl; auto|].
                    eapply reduces_to_trans;
                      [eapply reduce_to_prinargs_comp_can;
                        [apply reduces_to_symm
                        |idtac
                        |exact ceq7]
                      |]; eauto 3 with slow;[].
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; simpl.
                    unfold compute_step_comp; simpl; boolvar; tcsp.
                }

              * ex_spfexc; dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

            + unfold computes_to_exception_in_max_k_steps in hv'1.
              eapply reduces_in_atmost_k_steps_if_reduces_to in hv'1;[|exact ih3|]; eauto 3 with slow; exrepnd.
              pose proof (indhyp u' t2' t3' (mk_exception n0 e) k') as q.

              applydup @reduces_to_preserves_wf in ih1; auto;[].
              applydup @reduces_to_preserves_wf in ih2; auto;[].
              applydup @reduces_to_preserves_wf in ih3; auto;[].
              repeat (autodimp q hyp); eauto 3 with slow; try omega;[].
              exrepnd.
              apply differ_try_alpha_exception in q1; repndors;[|]; exrepnd; subst.

              * exists (mk_exception n1 e0) (mk_exception n2 e4) (mk_exception n0 e).
                dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih3|exists k'; exact hv'2]
                  |]; fold_terms.
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { apply implies_differ_try_alpha_exception; auto. }

              * ex_spfexc; dands; eauto 3 with slow.

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih1|exact q0]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

                { eapply reduces_to_trans;
                  [eapply reduces_to_prinarg;
                    eapply reduces_to_trans;[exact ih2|exact q2]
                  |].
                  apply reduces_to_if_step; csunf; simpl; auto. }

          - ex_spfexc; ginv.

          - cpx.
            exists (oterm (NCan ncan) (nobnd t2' :: bs0))
                   (oterm (NCan ncan) (nobnd t3' :: bs2))
                   (oterm (NCan ncan) (nobnd u' :: bs)).
            dands; eauto 3 with slow.

            { eapply reduces_to_prinarg; auto. }
            { eapply reduces_to_prinarg; auto. }
            { eapply reduces_to_prinarg; auto. }

            { unfold differ_try_alpha in ih0; exrepnd.
              exists (oterm (NCan ncan) (nobnd u1 :: bs))
                     (oterm (NCan ncan) (nobnd u2 :: bs0))
                     (oterm (NCan ncan) (nobnd u3 :: bs2)).
              dands; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv i; repndors; ginv; eauto 3 with slow;
                try (apply alphaeqbt_nilv2; auto).
                allrw @in_combine_same; repnd; subst; eauto 3 with slow.

              - apply differ_try_oterm; simpl; try omega; tcsp;[].
                introv i; repndors; ginv; tcsp.
                constructor; auto.
            }
        }
      }

      { (* fresh case *)
        apply compute_step_ncan_bterm_cons_success in comp; repnd; subst; GC; fold_terms.

        inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

        { ex_spfexc. }

        cpx; allsimpl.
        pose proof (imp (bterm [n] t1) x0 x) as d1; autodimp d1 hyp.
        clear imp.
        inversion d1 as [? ? ? ? d2]; subst; clear d1.
        fold_terms.

        repndors; exrepnd; subst;[|idtac|].

        - apply has_value_like_k_fresh_id in hv; sp.

        - applydup @differ_try_isvalue_like in d2; auto.
          repndors; repnd.

          + exists (pushdown_fresh n t2)
                   (pushdown_fresh n t3)
                   (pushdown_fresh n t1).
            dands; eauto 3 with slow;
            try (complete (apply reduces_to_if_step; apply compute_step_fresh_if_isvalue_like; auto)).

          + unfold spfexc_pair in d0; exrepnd; subst.
            exists (spfexc (n :: vs1) (n :: vs2) a)
                   (spfexc (n :: vs3) (n :: vs4) a)
                   (pushdown_fresh n t1).
            dands; eauto 3 with slow;[].
            apply differ_try_implies_differ_try_alpha.
            apply differ_try_exc.
            apply spfexc_pair_spfexc; simpl; try omega.

        - (* one reduction step under fresh *)
          pose proof (fresh_atom o (a :: get_utokens t1
                                      ++ get_utokens t2
                                      ++ get_utokens t3
                                      ++ get_utokens f
                                      ++ get_utokens g
                                      ++ get_utokens c)) as fa; exrepnd.
          allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a'.

          pose proof (ind t1 (subst t1 n (mk_utoken a')) [n]) as q; clear ind.
          repeat (autodimp q hyp);[rw @simple_osize_subst;eauto 3 with slow|];[].
          allrw @wf_fresh_iff.
          applydup @compute_step_preserves_wf in comp2; auto;
          [|apply wf_term_subst; eauto 3 with slow];[].
          pose proof (has_value_like_k_fresh_implies
                        lib k (get_fresh_atom t1) n
                        (subst_utokens x [(get_fresh_atom t1, mk_var n)])) as hvf.
          repeat (autodimp hvf hyp).
          { apply wf_subst_utokens; eauto 3 with slow. }
          { introv i; apply get_utokens_subst_utokens_subset in i; allsimpl.
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r.
            allrw in_remove; sp. }

          assert (!LIn n (free_vars x)) as ninx.
          { apply compute_step_preserves in comp2; repnd; eauto 3 with slow;[].
            introv i; apply subvars_eq in comp3; apply comp3 in i.
            apply eqset_free_vars_disjoint in i; allsimpl; boolvar; allsimpl;
            allrw app_nil_r; allrw in_remove_nvars; allsimpl; tcsp. }

          eapply alphaeq_preserves_has_value_like_k in hvf;
            [| |apply simple_subst_subst_utokens_aeq; auto];
            [|apply nt_wf_subst; eauto 2 with slow;[];
              apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow].

          pose proof (compute_step_subst_utoken
                        lib t1 x
                        [(n,mk_utoken (get_fresh_atom t1))]) as comp'.
          repeat (autodimp comp' hyp); eauto 3 with slow.
          { apply nr_ut_sub_cons; auto; introv i; apply get_fresh_atom_prop. }
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; apply get_fresh_atom_prop. }
          exrepnd; allsimpl.
          pose proof (comp'0 [(n,mk_utoken a')]) as comp''; allsimpl; clear comp'0.
          repeat (autodimp comp'' hyp).
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; auto. }
          exrepnd.
          allrw @fold_subst.

          pose proof (get_fresh_atom_prop t1) as gfpat1.
          remember (get_fresh_atom t1) as at1.
          clear Heqat1.
          dup comp'1 as aeq1.
          apply (alpha_eq_subst_utokens_same _ _ [(at1,mk_var n)]) in aeq1.
          dup aeq1 as aeq'.
          apply alpha_eq_sym in aeq1.
          eapply alpha_eq_trans in aeq1;
            [|apply alpha_eq_sym; apply simple_alphaeq_subst_utokens_subst;
              introv i; apply comp'4 in i; sp].
          dup aeq1 as aeq''.
          apply (lsubst_alpha_congr2 _ _ [(n,mk_utoken a')]) in aeq1.
          allrw @fold_subst.
          dup aeq1 as aeq'''.
          apply alpha_eq_sym in aeq1; eapply alpha_eq_trans in aeq1;
          [|apply alpha_eq_sym; apply simple_subst_subst_utokens_aeq_ren; auto].
          assert (alpha_eq s (ren_utokens [(at1,a')] x)) as aeq2 by (eauto 3 with slow).

          pose proof (q (subst t2 n (mk_utoken a'))
                        (subst t3 n (mk_utoken a'))
                        s k) as ih; clear q.
          repeat (autodimp ih hyp); try (apply wf_term_subst; eauto 3 with slow).
          { repeat unfsubst.
            apply differ_try_lsubst_aux; simpl; auto.
            apply dsub_try_cons; auto;[].
            apply differ_try_oterm; simpl; tcsp. }
          { eapply alphaeq_preserves_has_value_like_k;[|apply alpha_eq_sym;exact aeq2|]; eauto 3 with slow;[].
            apply has_value_like_k_ren_utokens; simpl; eauto 3 with slow.
            apply disjoint_singleton_l; rw in_remove; introv i; repnd.
            apply compute_step_preserves_utokens in comp2; eauto 3 with slow;[].
            apply comp2 in i.
            apply get_utokens_subst in i; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp. }
          { introv ltm w1 w2 w3 isv r d.
            apply (indhyp t0 t4 t5 v m); eauto 3 with slow; try omega. }
          exrepnd.

          applydup @reduces_to_fresh2 in ih1; auto.
          applydup @reduces_to_fresh2 in ih2; auto.
          exrepnd.

          applydup @compute_step_preserves_wf in comp''1 as wf1; eauto 4 with slow;[].

          eapply reduces_to_alpha in ih3;[| |eapply alpha_eq_trans;[exact comp''0|exact aeq'''] ];
          eauto 3 with slow;[].

          exrepnd.
          applydup @reduces_to_fresh2 in ih3; auto;
          [|apply wf_subst_utokens; eauto 3 with slow
           |introv i; apply get_utokens_subst_utokens_subset in i; allsimpl;
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r;
            allrw in_remove; repnd;
            apply compute_step_preserves_utokens in comp2;[|eauto 4 with slow];
            apply comp2 in i;
            apply get_utokens_subst in i; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp].
          exrepnd.

          exists (mk_fresh n z0)
                 (mk_fresh n z)
                 (mk_fresh n z1); dands; eauto 3 with slow.
          eapply differ_try_alpha_alpha_eq1;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih10|].
          eapply differ_try_alpha_alpha_eq1;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_subst_utokens_same;exact ih8|].
          eapply differ_try_alpha_alpha_eq2;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih7|].
          eapply differ_try_alpha_alpha_eq3;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih6|].
          apply differ_try_alpha_mk_fresh.
          apply differ_try_alpha_subst_utokens; simpl; tcsp;
          apply disjoint_singleton_r; auto.
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.
      inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

      { ex_spfexc. }

      exists (oterm Exc bs2) (oterm Exc bs3) (oterm Exc bs); dands; eauto 3 with slow;[].
      apply differ_try_implies_differ_try_alpha.
      apply differ_try_oterm; simpl; tcsp.

    + SCase "Abs".
      csunf comp; allsimpl.
      inversion d as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? d1 aeq1 aeq2 aeq3|? ? ? spf|?|?|? ? ? ? len1 len2 nia imp]; subst; allsimpl; clear d; GC;[|].

      { ex_spfexc. }

      pose proof (differ_try_bterms_implies_eq_map_num_bvars a f g c bs bs2 bs3) as e.
      autodimp e hyp.
      { unfold differ_try_bterms, br_bterms3, br_list3; dands; auto. }
      apply compute_step_lib_success in comp; exrepnd; subst.
      exists (mk_instance vars bs2 rhs)
             (mk_instance vars bs3 rhs)
             (mk_instance vars bs rhs).
      dands; eauto 3 with slow.
      { apply reduces_to_if_step; csunf; simpl.
        eapply compute_step_lib_success_change_bs;[|exact comp0]; auto. }
      { apply reduces_to_if_step; csunf; simpl.
        eapply compute_step_lib_success_change_bs;[|exact comp0]; auto. }
      dup comp0 as fe2.
      dup comp0 as fe3.
      eapply found_entry_change_bs in fe2;[|exact e0].
      eapply found_entry_change_bs in fe3;[|exact e].
      applydup @found_entry_implies_matching_entry in comp0.
      applydup @found_entry_implies_matching_entry in fe2.
      applydup @found_entry_implies_matching_entry in fe3.
      apply differ_try_mk_instance; auto; try (complete (allunfold @matching_entry; sp)).
      { unfold correct_abs in correct; sp. }
      { allunfold @correct_abs; sp. }
      unfold differ_try_bterms, br_bterms3, br_list3; sp.
Qed.

Lemma differ_try_reduces_in_atmost_k_steps_aux {o} :
  forall lib a f g c k (t1 t2 t3 : @NTerm o) u,
    isprog f
    -> isprog g
    -> isprog c
    -> wf_term t1
    -> wf_term t2
    -> wf_term t3
    -> eq_fun2TE lib a f g
    -> differ_try a f g c t1 t2 t3
    -> reduces_in_atmost_k_steps lib t1 u k
    -> isvalue_like u
    -> {t2' : NTerm
        & {t3' : NTerm
        & reduces_to lib t2 t2'
        # reduces_to lib t3 t3'
        # differ_try_alpha a f g c u t2' t3'}}.
Proof.
  induction k as [n ind] using comp_ind_type;
  introv ispf ispg ispc w1 w2 w3 eqf d r isv.
  destruct n as [|k].
  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t2 t3; dands; eauto 3 with slow.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    pose proof (differ_try_step lib a f g c t1 t2 t3 u0 k) as h.
    repeat (autodimp h hyp).
    { unfold has_value_like_k; exists u.
      unfold computes_to_val_like_in_max_k_steps; dands; auto. }
    { introv ltm wt1 wt2 wt3 i rt d'.
      pose proof (ind m ltm t0 t4 t5 v) as q.
      repeat (autodimp q hyp). }
    exrepnd.
    dup r0 as r.
    eapply reduces_in_atmost_k_steps_if_reduces_to in r;[|exact h3|exact isv].
    exrepnd.
    assert (k' < S k) as ltk by omega.

    applydup @compute_step_preserves_wf in r1;auto;[].
    applydup @reduces_to_preserves_wf in h1;auto;[].
    applydup @reduces_to_preserves_wf in h2;auto;[].
    applydup @reduces_to_preserves_wf in h3;auto;[].

    assert (forall (t1 t2 t3 v : NTerm) (m : nat),
              m < S k
              -> wf_term t1
              -> wf_term t2
              -> wf_term t3
              -> isvalue_like v
              -> reduces_in_atmost_k_steps lib t1 v m
              -> differ_try_alpha a f g c t1 t2 t3
              -> {v2, v3 : NTerm
                  $ reduces_to lib t2 v2
                  # reduces_to lib t3 v3
                  # differ_try_alpha a f g c v v2 v3}) as ind'.
    { introv ltm wt1 wt2 wt3 i rt d'.
      unfold differ_try_alpha in d'; exrepnd.
        eapply reduces_in_atmost_k_steps_alpha in rt;[|eauto 3 with slow|exact d'1]; exrepnd;[].
        applydup @alphaeq_preserves_wf_term in d'1;auto;[].
        applydup @alphaeq_preserves_wf_term in d'2;auto;[].
        applydup @alphaeq_preserves_wf_term in d'3;auto;[].
        applydup @alpha_eq_preserves_isvalue_like in rt0;auto;[].
        pose proof (ind m ltm u1 u2 u3 t2'0) as h.
        repeat (autodimp h hyp).
        exrepnd.
        eapply reduces_to_alpha in h7;[|eauto 3 with slow|apply alpha_eq_sym; exact d'2];[].
        eapply reduces_to_alpha in h9;[|eauto 3 with slow|apply alpha_eq_sym; exact d'3];[].
        exrepnd.
        exists t2'3 t2'2; dands; auto.
        eapply differ_try_alpha_alpha_eq1;[apply alpha_eq_sym;exact rt0|].
        eapply differ_try_alpha_alpha_eq2;[exact h11|].
        eapply differ_try_alpha_alpha_eq3;[exact h10|].
        auto. }
    clear ind; rename ind' into ind.

    pose proof (ind u' t2' t3' u k' ltk) as h.
    repeat (autodimp h hyp);[].
    exrepnd.
    exists v2 v3; dands; eauto 3 with slow.
    { eapply reduces_to_trans;[exact h1|];auto. }
    { eapply reduces_to_trans;[exact h2|];auto. }
Qed.

Lemma eq_fun2natE_implies_eq_fun2TE {o} :
  forall lib a (f g : @NTerm o),
    eq_fun2natE lib a f g
    -> eq_fun2TE lib a f g.
Proof.
  introv e; introv.
  pose proof (e n) as h.
  repndors; exrepnd;[left|right]; auto.
  eexists; eexists; dands; eauto.
  simpl; tcsp.
Qed.

Lemma differ_try_reduces_in_atmost_k_steps {o} :
  forall lib a f g c k (t1 t2 t3 : @NTerm o) u,
    isprog f
    -> isprog g
    -> isprog c
    -> wf_term t1
    -> wf_term t2
    -> wf_term t3
    -> eq_fun2natE lib a f g
    -> differ_try a f g c t1 t2 t3
    -> reduces_in_atmost_k_steps lib t1 u k
    -> isvalue_like u
    -> {t2' : NTerm
        & {t3' : NTerm
        & reduces_to lib t2 t2'
        # reduces_to lib t3 t3'
        # differ_try_alpha a f g c u t2' t3'}}.
Proof.
  introv ispf ispg w1 w2 w3 eqf d r isv.
  apply (differ_try_reduces_in_atmost_k_steps_aux lib a f g c k t1 t2 t3); auto.
  apply eq_fun2natE_implies_eq_fun2TE; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
