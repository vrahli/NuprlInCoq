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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export continuity.
Require Export stronger_continuity_defs1.
Require Export stronger_continuity_defs3.
Require Export List.
Require Export list.  (* WTF!! *)



Lemma cequiv_bound_nat_bound {o} :
  forall lib (a : get_patom_set o) (x e z : NVar) (k : nat) (f : @NTerm o),
    (forall t n,
       n < k
       -> computes_to_value lib t (mk_nat n)
       -> {j : nat & computes_to_value lib (mk_apply f t) (mk_nat j)})
    -> cequiv
         lib
         (bound_nat a x e z (bound x (mk_utoken a) (mk_nat k) f))
         (mk_lam x (mk_less (mk_var x) mk_zero (mk_vbot z)
                            (mk_less (mk_var x) (mk_nat k)
                                     (mk_apply f (mk_var x))
                                     (spexc a)))).
Proof.
  introv imp.

Abort.

Lemma cequiv_sp_bound_nat_c_bound_c {o} :
  forall lib v z (e n f : @CTerm o),
    cequivc
      lib
      (sp_bound_nat_c v z (bound_c e n f v))
      (bound2_c v z n f e).
Proof.
  introv.

  apply cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_vbot_substc.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_apply_bound_c]
    |].
  rw @boundl_c_eq; auto.
Qed.

Lemma substc_mkcv_axiom {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_axiom v) = mkc_axiom.
Proof.
  introv; destruct_cterms.
  apply cterm_eq; simpl.
  unfsubst.
Qed.

Lemma spM_in_modulus_fun_type_u {o} :
  forall lib (F : @CTerm o),
    member lib F (mkc_fun nat2nat mkc_tnat)
    -> member lib (spM_c F) modulus_fun_type_u.
Proof.
  introv mF.

  unfold modulus_fun_type_u.
  apply equality_in_function2.
  fold (@modulus_fun_type_u o).
  dands; try (apply type_modulus_fun_type_u).
  introv e.
  rename a into n.
  rename a' into m.
  eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply substc_mkcv_fun].
  allrw @csubst_mk_cv.
  apply equality_in_fun.
  dands.

  - eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply substc_mkcv_fun|].
    allrw @mkcv_tnat_substc.
    apply type_mkc_fun.
    dands.
    + eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply mkcv_natk_substc|].
      rw @mkc_var_substc.
      apply equality_in_tnat in e.
      unfold equality_of_nat in e; exrepnd; spcast.
      apply type_mkc_natk.
      allrw @mkc_nat_eq.
      exists (Z.of_nat k); spcast; auto.
    + introv inh.
      apply type_tnat.

  - introv inh.
      apply tequality_bunion; dands.
      * apply type_tnat.
      * apply type_mkc_unit.

  - introv e1.
    allrw <- @mkc_apply2_eq.
    rename a into f.
    rename a' into g.
    eapply alphaeqc_preserving_equality in e1;[|apply substc_mkcv_fun].
    eapply alphaeqc_preserving_equality in e1;
      [|apply alphaeqc_mkc_fun;[apply mkcv_natk_substc|apply alphaeqc_refl] ].
    allrw @mkcv_tnat_substc.
    allrw @mkc_var_substc.

    apply equality_in_tnat in e.
    unfold equality_of_nat in e; exrepnd; spcast.

    (* let's get rid of [n] and [m] now *)
    eapply cequivc_preserving_equality in e1;
      [|apply cequivc_mkc_fun;[|apply cequivc_refl];
        apply cequivc_mkc_natk;
        apply computes_to_valc_implies_cequivc; exact e2].

    fold (@natk2nat o (mkc_nat k)) in e1.

    eapply equality_respects_cequivc_left;
      [apply implies_cequivc_apply2;[apply cequivc_refl|idtac|apply cequivc_refl];
       apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact e2|].

    eapply equality_respects_cequivc_right;
      [apply implies_cequivc_apply2;[apply cequivc_refl|idtac|apply cequivc_refl];
       apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact e0|].

    clear dependent n.
    clear dependent m.

    (* let's beta-reduce *)
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym; apply cequivc_apply2_spM_c|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym; apply cequivc_apply2_spM_c|].

    (* now let's apply bound to [f] and [g] *)
    pose proof (equality_in_natk2nat_implies_equality_bound lib f g k e1) as h.
    allrw @test_c_eq.

    destruct (fresh_atom o (getc_utokens F ++ getc_utokens f ++ getc_utokens g)) as [a nia].
    allrw in_app_iff; allrw not_over_or; repnd.

    (* let's get rid of fresh in the conclusion *)
    assert (equality
              lib
              (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) f))
              (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) g))
              (mkc_bunion mkc_tnat mkc_unit)) as equ;
      [|pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) f) a) as h1;
         repeat (autodimp h1 hyp);
         [ destruct_cterms; allsimpl;
           allunfold @getcv_utokens; allunfold @getc_utokens; allsimpl; allrw app_nil_r;
           allrw in_app_iff; tcsp
         | apply equality_refl in equ; apply member_bunion_nat_unit_implies_cis_spcan_not_atom; auto
         |];
         pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) g) a) as h2;
         repeat (autodimp h2 hyp);
         [ destruct_cterms; allsimpl;
           allunfold @getcv_utokens; allunfold @getc_utokens; allsimpl; allrw app_nil_r;
           allrw in_app_iff; tcsp
         | apply equality_sym in equ; apply equality_refl in equ; apply member_bunion_nat_unit_implies_cis_spcan_not_atom; auto
         |];
         spcast;
         eapply equality_respects_cequivc_left;[apply cequivc_sym;exact h1|];
         eapply equality_respects_cequivc_right;[apply cequivc_sym;exact h2|];
         complete auto
      ].

    repeat (rw @substc_test_try2_cv).

    pose proof (h a nvarx) as q.
    clear h.

    pose proof (apply_nat2natE_aux2
                  lib F
                  (bound_c (mkc_utoken a) (mkc_nat k) f nvarx)
                  (bound_c (mkc_utoken a) (mkc_nat k) g nvarx)
                  a nvarx nvarz) as ee.
    repeat (autodimp ee hyp); try (complete (intro xx; ginv));[].
    clear q.

    eapply equality_respects_cequivc_left in ee;
      [|apply implies_cequivc_apply;
         [apply cequivc_refl
         |apply cequiv_sp_bound_nat_c_bound_c]
      ].

    eapply equality_respects_cequivc_right in ee;
      [|apply implies_cequivc_apply;
         [apply cequivc_refl
         |apply cequiv_sp_bound_nat_c_bound_c]
      ].

    apply equality_in_natE_implies in ee; repndors.

    { unfold equality_of_nat_tt in ee; exrepnd.
      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;
          apply computes_to_valc_implies_cequivc;
          eapply computes_to_valc_mkc_try;
          [exact ee1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
        |].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;
          apply computes_to_valc_implies_cequivc;
          eapply computes_to_valc_mkc_try;
          [exact ee0|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
        |].
      apply equality_in_disjoint_bunion; eauto 3 with slow.
      dands; eauto 3 with slow. }

    { repnd.
      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;
          apply simpl_cequivc_mkc_try;
          [exact ee0|apply cequivc_refl]
        |].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;
          apply simpl_cequivc_mkc_try;
          [exact ee|apply cequivc_refl]
        |].

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

      allrw @substc_mkcv_axiom.
      apply equality_in_disjoint_bunion; eauto 3 with slow.
      dands; eauto 3 with slow.
      right.
      apply equality_in_unit; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }
Qed.

Definition get_ints_from_computes_to_value {o}
           (lib : @library o)
           (t u : @NTerm o)
           (comp : computes_to_value lib t u) : list Z :=
  match comp with
    | (c,_) => get_ints_from_computation lib t u c
  end.

Definition get_ints_from_computes_to_valc {o}
           (lib : @library o)
           (t u : @CTerm o)
           (comp : computes_to_valc lib t u) : list Z :=
  get_ints_from_computes_to_value lib (get_cterm t) (get_cterm u) comp.

Lemma cequivc_nat {o} :
  forall lib (t t' : @CTerm o) (n : nat),
    computes_to_valc lib t (mkc_nat n)
    -> cequivc lib t t'
    -> computes_to_valc lib t' (mkc_nat n).
Proof.
  introv comp ceq; destruct_cterms;
  allunfold @computes_to_valc; allunfold @cequivc; allsimpl.
  eapply cequiv_nat; eauto.
Qed.

Definition force_nat {o} (arg : @NTerm o) x z (f : @NTerm o) :=
  mk_cbv arg x (mk_less (mk_var x)
                        mk_zero
                        (mk_vbot z)
                        (mk_apply f (mk_var x))).

Definition force_nat_c {o} (arg : @CTerm o) x z (f : @CTerm o) : CTerm :=
  mkc_cbv
    arg
    x
    (mkcv_less
       [x]
       (mkc_var x)
       (mkcv_zero [x])
       (mkcv_vbot [x] z)
       (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))).

Lemma get_cterm_force_nat_c {o} :
  forall (arg : @CTerm o) x z f,
    get_cterm (force_nat_c arg x z f)
    = force_nat (get_cterm arg) x z (get_cterm f).
Proof.
  introv; destruct_cterms; simpl; auto.
Qed.

Definition lam_force_nat_c {o} x z (f : @CTerm o) : CTerm :=
  mkc_lam
    x
    (mkcv_cbv
       [x]
       (mkc_var x)
       x
       (mkcv_dup1
          x
          (mkcv_less
             [x]
             (mkc_var x)
             (mkcv_zero [x])
             (mkcv_vbot [x] z)
             (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))))).

Lemma cequivc_mkc_apply_lam_force_nat_c {o} :
  forall lib x z (f arg : @CTerm o),
    cequivc
      lib
      (mkc_apply (lam_force_nat_c x z f) arg)
      (force_nat_c arg x z f).
Proof.
  introv.
  eapply cequivc_trans;[unfold lam_force_nat_c;apply cequivc_beta|].
  rw @mkcv_cbv_substc_same.
  rw @mkc_var_substc.
  rw @mkcv_cont1_dup1; eauto 3 with slow.
Qed.

Lemma equality_lam_force_nat_c_in_nat2nat {o} :
  forall lib x z (f : @CTerm o),
    member lib f nat2nat
    -> equality lib f (lam_force_nat_c x z f) nat2nat.
Proof.
  introv mem.
  apply equality_in_fun; dands; eauto 3 with slow.
  introv equ.
  apply equality_in_tnat in equ.
  unfold equality_of_nat in equ; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
      apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact equ1]
    |].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_apply_lam_force_nat_c|].

  unfold force_nat_c.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply simpl_cequivc_mkc_cbv;
     apply computes_to_valc_implies_cequivc;exact equ0|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow;[].
  rw @mkcv_less_substc.
  rw @substc_mkcv_zero.
  rw @mkcv_vbot_substc.
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @mkc_var_substc.

  rw @mkc_zero_eq.

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  boolvar; tcsp.

  allrw @equality_in_fun; repnd.
  clear mem1 mem0.
  apply mem; eauto 3 with slow.
Qed.

Lemma eq_mkc_nat_implies {o} :
  forall k1 k2, @mkc_nat o k1 = mkc_nat k2 -> k1 = k2.
Proof.
  introv e.
  inversion e as [q].
  allapply Znat.Nat2Z.inj; auto.
Qed.

Definition bound2_cbv_c {o} x z (n f e : @CTerm o) :=
  mkc_lam
    x
    (mkcv_cbv
       [x]
       (mkc_var x)
       x
       (mkcv_dup1
          x
          (mkcv_less
             [x]
             (mkc_var x)
             (mkcv_zero [x])
             (mkcv_vbot [x] z)
             (mkcv_less
                [x]
                (mkc_var x)
                (mk_cv [x] n)
                (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))
                (mk_cv [x] (mkc_exception e mkc_axiom)))))).

Lemma cequiv_bound2_c_cbv {o} :
  forall lib x z (n f e : @CTerm o),
    cequivc
      lib
      (bound2_c x z n f e)
      (bound2_cbv_c x z n f e).
Proof.
  introv.
  apply cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_cbv_substc_same.
  allrw @mkcv_cont1_dup1.
  allrw @mkcv_apply_substc.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_vbot_substc.

  apply approxc_implies_cequivc; apply approxc_assume_hasvalue; intro hv.

  - apply hasvalue_likec_less in hv.
    repndors; exrepnd.

    + clear hv1 hv3 hv2.
      eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv0
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply implies_cequivc_apply;
            [apply cequivc_refl
            |apply reduces_toc_implies_cequivc;exact hv0]
          |apply cequivc_refl]
        ]
      |].

      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].

      clear dependent u.

      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_int|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_cbv]; eauto 3 with slow;[].

      allrw @mkcv_less_substc.
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_int].

      boolvar; eauto 3 with slow; try (apply approxc_refl).

    + clear hv1.

      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc|].

      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_cbv_exc
        ].
      apply approxc_refl.

    + apply (computes_to_valc_and_excc_false _ _ _ mkc_zero) in hv2; tcsp.
      apply computes_to_valc_refl; eauto 3 with slow.

  - apply @hasvalue_likec_cbv in hv.
    apply @hasvalue_likec_implies_or in hv.
    repndors.

    + apply hasvaluec_computes_to_valc_implies in hv; exrepnd.
      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply computes_to_valc_implies_cequivc;
          exact hv0|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_mkc_less;
             [apply cequivc_sym
             |apply cequivc_refl
             |apply implies_cequivc_apply;
               [apply cequivc_refl
               |apply cequivc_sym]
             |apply cequivc_refl]
           ];
           apply computes_to_valc_implies_cequivc;
           exact hv0
        ].
      rw @computes_to_valc_iff_reduces_toc in hv0; repnd.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv;complete auto|].

      allrw @mkcv_less_substc.
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      apply approxc_refl.

    + allrw @raises_exceptionc_as_computes_to_excc; exrepnd.
      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply reduces_toc_implies_cequivc;
          exact hv1|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl];
           apply reduces_toc_implies_cequivc;
           exact hv1
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_exc].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv_exc|].
      apply approxc_refl.
Qed.

Definition sp_force_nat {o} (arg : @NTerm o) x z (f : @NTerm o) :=
  mk_cbv arg x (mk_less (mk_var x) mk_zero (mk_vbot z) (mk_apply f (mk_var x))).

Definition bound2_cbv {o} arg x z (n : nat) (f : @NTerm o) a : NTerm :=
  mk_cbv
    arg
    x
    (mk_less
       (mk_var x)
       mk_zero
       (mk_vbot z)
       (mk_less (mk_var x) (mk_nat n) (mk_apply f (mk_var x)) (spexc a))).

Lemma alpha_eq_sp_force_nat {o} :
  forall (arg1 arg2 : @NTerm o) x1 x2 z1 z2 f1 f2,
    isprog f1
    -> alpha_eq f1 f2
    -> alpha_eq arg1 arg2
    -> alpha_eq (sp_force_nat arg1 x1 z1 f1) (sp_force_nat arg2 x2 z2 f2).
Proof.
  introv ispf aeq1 aeq2.
  applydup @alpha_eq_preserves_isprog in aeq1; auto.
  unfold sp_force_nat, mk_cbv, mk_less, mk_apply, mk_vbot, mk_lam, mk_fix, mk_zero, nobnd.

  prove_alpha_eq4.
  introv ln.
  repeat (destruct n; tcsp); eauto 3 with slow;[].
  clear ln.

  pose proof (ex_fresh_var (x1 :: x2
                               :: z1
                               :: z2
                               :: free_vars f1
                               ++ bound_vars f1
                               ++ free_vars f2
                               ++ bound_vars f2)) as h;
    exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v]); simpl; auto.

  { unfold all_vars; simpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw @remove_nvars_eq; allsimpl.
    allrw disjoint_singleton_l; allsimpl.
    repeat (allrw in_app_iff; simpl).
    tcsp. }

  allrw <- beq_var_refl.
  allrw memvar_singleton.
  repeat (rw (lsubst_aux_trivial_cl_term2 f1); eauto 2 with slow).
  repeat (rw (lsubst_aux_trivial_cl_term2 f2); eauto 2 with slow).

  prove_alpha_eq4.
  introv ln.

  repeat (destruct n; tcsp; try omega); eauto 3 with slow;
  clear ln;
  apply alphaeqbt_nilv2;
  prove_alpha_eq4;
  introv ln;
  repeat (destruct n; tcsp; try omega); eauto 3 with slow;[].
  clear ln.

  apply alphaeqbt_nilv2.
  prove_alpha_eq4.
  introv ln.
  repeat (destruct n; tcsp; try omega); eauto 3 with slow;[].
  clear ln.

  pose proof (ex_fresh_var (x1 :: x2
                               :: z1
                               :: z2
                               :: [])) as h;
    exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v0]); simpl; auto.

  { unfold all_vars; simpl; repeat (boolvar; allsimpl);
    allrw disjoint_singleton_l; allsimpl; tcsp. }

  repeat (boolvar; simpl); tcsp; eauto 2 with slow.
Qed.

Lemma alpha_eq_bound2_cbv {o} :
  forall (arg1 arg2 : @NTerm o) x1 x2 z1 z2 b f1 f2 a,
    isprog f1
    -> alpha_eq f1 f2
    -> alpha_eq arg1 arg2
    -> alpha_eq (bound2_cbv arg1 x1 z1 b f1 a) (bound2_cbv arg2 x2 z2 b f2 a).
Proof.
  introv ispf aeq1 aeq2.
  applydup @alpha_eq_preserves_isprog in aeq1; auto.
  unfold bound2_cbv, mk_cbv, mk_less, mk_apply, mk_vbot, mk_lam, mk_fix, mk_zero, nobnd.

  prove_alpha_eq4.
  introv ln.
  repeat (destruct n; tcsp); eauto 3 with slow;[].
  clear ln.

  pose proof (ex_fresh_var (x1 :: x2
                               :: z1
                               :: z2
                               :: free_vars f1
                               ++ bound_vars f1
                               ++ free_vars f2
                               ++ bound_vars f2)) as h;
    exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v]); simpl; auto.

  { unfold all_vars; simpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw @remove_nvars_eq; allsimpl.
    allrw disjoint_singleton_l; allsimpl.
    repeat (allrw in_app_iff; simpl).
    tcsp. }

  allrw <- beq_var_refl.
  allrw memvar_singleton.
  repeat (rw (lsubst_aux_trivial_cl_term2 f1); eauto 2 with slow).
  repeat (rw (lsubst_aux_trivial_cl_term2 f2); eauto 2 with slow).

  prove_alpha_eq4.
  introv ln.
  repeat (destruct n; tcsp; try omega); eauto 3 with slow;
  clear ln;
  apply alphaeqbt_nilv2;
  prove_alpha_eq4;
  introv ln;
  repeat (destruct n; tcsp; try omega); eauto 3 with slow;
  clear ln;
  apply alphaeqbt_nilv2;
  prove_alpha_eq4;
  introv ln;
  repeat (destruct n; tcsp; try omega); eauto 3 with slow;[].
  clear ln.

  pose proof (ex_fresh_var (x1 :: x2
                               :: z1
                               :: z2
                               :: [])) as h;
    exrepnd.
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

  apply (al_bterm_aux [v0]); simpl; auto.

  { unfold all_vars; simpl; repeat (boolvar; allsimpl);
    allrw disjoint_singleton_l; allsimpl; tcsp. }

  repeat (boolvar; simpl); tcsp; eauto 2 with slow.
Qed.

Lemma so_alphaeq_preserves_no_utokens {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> no_utokens t1
    -> no_utokens t2.
Proof.
  introv aeq nout.
  apply get_utokens_so_soalphaeq in aeq.
  allunfold @no_utokens.
  rw aeq in nout; auto.
Qed.
Hint Resolve so_alphaeq_preserves_no_utokens : slow.

Definition computation_fails {o} lib (t : @NTerm o) :=
  {s : String.string
   & {u : NTerm
   & {k : nat
   & compute_at_most_k_steps lib k t = cfailure s u}}}.

Lemma alpha_eq_subst_sp_force_nat_alpha_eq {o} :
  forall v z (f : @NTerm o) t,
    isprog f
    -> alpha_eq
         (subst (mk_less (mk_var v) mk_zero (mk_vbot z) (mk_apply f (mk_var v))) v t)
         (mk_less t mk_zero (mk_vbot z) (mk_apply f t)).
Proof.
  introv isp.
  pose proof (unfold_lsubst
                [(v,t)]
                (mk_less (mk_var v) mk_zero (mk_vbot z) (mk_apply f (mk_var v))))
    as unf; exrepnd.
  unfold subst.
  rw unf0; clear unf0.
  allapply @alpha_eq_mk_less; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.
  allapply @alpha_eq_mk_vbot; exrepnd; subst.
  allapply @alpha_eq_mk_zero; subst.
  allapply @alpha_eq_mk_apply; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.

  allsimpl; cpx; ginv.

  allrw app_nil_r.
  allrw disjoint_cons_l.
  repnd.
  rename a' into f'.

  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.

  unfold mk_less, mk_apply, mk_vbot, mk_zero, mk_nat, mk_integer, mk_fix, mk_lam, mk_var, nobnd.
  repeat (prove_alpha_eq4; eauto 2 with slow).

  { pose proof (ex_fresh_var (v :: z :: [])) as fv.
    exrepnd; allsimpl; allrw not_over_or; repnd; GC.
   rw (@lsubst_aux_trivial_cl_term2 o c'); eauto 3 with slow.
  }
Qed.

Lemma wf_bound2_cbv {o} :
  forall (arg : @NTerm o) x z b f a,
    wf_term (bound2_cbv arg x z b f a) <=> (wf_term arg # wf_term f).
Proof.
  introv.
  unfold bound2_cbv.
  rw <- @wf_cbv_iff.
  repeat (rw <- @wf_less_iff).
  rw <- @wf_apply_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma wf_sp_force_nat {o} :
  forall (arg : @NTerm o) x z f,
    wf_term (sp_force_nat arg x z f) <=> (wf_term arg # wf_term f).
Proof.
  introv.
  rw <- @wf_cbv_iff.
  repeat (rw <- @wf_less_iff).
  rw <- @wf_apply_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma hasvalue_like_vbot {o} :
  forall (lib : @library o) z,
    !hasvalue_like lib (mk_vbot z).
Proof.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_to_vbot_if_isvalue_like in hv1; sp.
Qed.

Lemma not_hasvalue_like_fresh {o} :
  forall lib (v : NVar), !@hasvalue_like o lib (mk_fresh v (mk_var v)).
Proof.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_in_atmost_k_step_fresh_id in hv1; sp.
Qed.

Lemma hasvalue_like_subst_less_seq {o} :
  forall lib (f : @ntseq o) v a b c,
    hasvalue_like
      lib
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

  unfold hasvalue_like, reduces_to in comp; exrepnd.

  destruct k.

  - allrw @reduces_in_atmost_k_steps_0; repnd; subst.
    unfold isvalue_like in comp0; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp2; allsimpl; ginv.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)