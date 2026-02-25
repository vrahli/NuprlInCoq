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


Require Export stronger_continuity_defs_typ.
Require Export terms5.
Require Export cvterm3.

Require Export list. (* WTF? *)


Definition all_vars_utok_sub {o} (sub : @utok_sub o) :=
  forall a t, LIn (a,t) sub -> isvariable t.

Definition free_from_atom {o} lib (t : @NTerm o) (a : @get_patom_set o) :=
  {u : NTerm & cequiv lib t u # !LIn a (get_utokens u)}.

Definition free_from_atom_c {o} lib (t : @CTerm o) (a : @get_patom_set o) :=
  {u : CTerm & cequivc lib t u # !LIn a (getc_utokens u)}.

Definition modulus_fun_type_u {o} : @CTerm o :=
  mkc_function
    mkc_tnat
    nvarx
    (mkcv_fun
       [nvarx]
       (mkcv_fun [nvarx] (mkcv_natk [nvarx] (mkc_var nvarx)) (mkcv_tnat [nvarx]))
       (mk_cv [nvarx] (mkc_bunion mkc_tnat mkc_unit))).

Lemma x_in_l : forall x e n f, subvars [x] [x,e,n,f].
Proof.
  introv; unfold subvars, sub_vars, subsetb; simpl.
  repeat (boolvar; simpl; tcsp).
Qed.

Lemma n_in_l : forall x e n f, subvars [n] [x,e,n,f].
Proof.
  introv; unfold subvars, sub_vars, subsetb; simpl.
  repeat (boolvar; simpl; tcsp).
Qed.

Lemma f_in_l : forall x e n f, subvars [f] [x,e,n,f].
Proof.
  introv; unfold subvars, sub_vars, subsetb; simpl.
  repeat (boolvar; simpl; tcsp).
Qed.

Lemma e_in_l : forall x e n f, subvars [e] [x,e,n,f].
Proof.
  introv; unfold subvars, sub_vars, subsetb; simpl.
  repeat (boolvar; simpl; tcsp).
Qed.


(*

  boundl(x,e,n,f) :=
    if x < n then f x else exception(e,Ax)

 *)
Definition boundl {o} (x e n f : @NTerm o) : @NTerm o :=
  mk_less x
          n
          (mk_apply f x)
          (mk_exception e mk_axiom).

Definition boundl2 {o} z (x e n f : @NTerm o) : @NTerm o :=
  mk_less x
          mk_zero
          (mk_vbot z)
          (boundl x e n f).

(*

  bound(e,n,f) :=
    \x. if x < n then f x else exception(e,Ax)

 *)
Definition bound {o} (x : NVar) (e n f : @NTerm o) : @NTerm o :=
  mk_lam x (boundl (mk_var x) e n f).

Definition bound2 {o} (x z : NVar) (e n f : @NTerm o) : @NTerm o :=
  mk_lam x (boundl2 z (mk_var x) e n f).

Definition bound2_c {o} x z (n f e : @CTerm o) :=
  mkc_lam
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
          (mk_cv [x] (mkc_exception e mkc_axiom)))).

Lemma get_cterm_bound2_c_eq {o} :
  forall x z (e n f : @CTerm o),
    get_cterm (bound2_c x z n f e) =
    bound2 x z (get_cterm e) (get_cterm n) (get_cterm f).
Proof.
  introv.
  simpl.
  rw @get_cterm_mkc_exception; auto.
Qed.

(*
Definition boundc {o} (x e n f : NVar) : @CVTerm o [e,n,f] :=
  let l := [x,e,n,f] in
  mkcv_lam [e,n,f]
           x
           (mkcv_less l
                      (mkcv_sub [x] l (x_in_l x e n f) (mkc_var x))
                      (mkcv_sub [n] l (n_in_l x e n f) (mkc_var n))
                      (mkcv_apply l
                                  (mkcv_sub [f] l (f_in_l x e n f) (mkc_var f))
                                  (mkcv_sub [x] l (x_in_l x e n f) (mkc_var x)))
                      (mkcv_exception l
                                      (mkcv_sub [e] l (e_in_l x e n f) (mkc_var e))
                                      (mkcv_ax l))).
*)

(*

  app_bound(F,e,n,f) := F(bound(e,n,f))

 *)
Definition app_bound2 {o} (F : NTerm) (x z : NVar) (e n f : @NTerm o) : NTerm :=
  mk_apply F (bound2 x z e n f).

(*
Definition inl_boundc {o} (F : CTerm) (y x e n f : NVar) : @CVTerm o [e,n,f] :=
  let l := [e,n,f] in
  mkcv_cbv l
           (mkcv_apply l (mk_cv l F) (boundc x e n f))
           y
           (mkcv_inl (y :: l) (mk_cv_app_r l [y] (mkc_var y))).
*)

(*

  test(F,n,f) :=
    fresh(e.try(inl_bound(e,n,f),e,c.inr(Ax)))

 *)
Definition test_try2 {o} (F : @NTerm o) (c x z : NVar) (e n f : @NTerm o) : NTerm :=
  mk_try (app_bound2 F x z e n f)
         e
         c
         mk_axiom.

Definition test2 {o} (F : @NTerm o) (c x z e : NVar) (n f : @NTerm o) : NTerm :=
  mk_fresh e (test_try2 F c x z (mk_var e) n f).

Definition primrec {o} (p k m : NVar) (n b c : @NTerm o) :=
  mk_apply (mk_fix
              (mk_lam
                 p
                 (mk_lam
                    k
                    (mk_int_eq
                       (mk_var k)
                       mk_zero
                       b
                       (mk_cbv
                          (mk_sub (mk_var k) mk_one)
                          m
                          (mk_apply2 c (mk_var m) (mk_apply (mk_var p) (mk_var m))))))))
           n.

Lemma isprog_vars_primrec {o} :
  forall vs (n b c : @NTerm o) p k m,
    isprog_vars vs (primrec p k m n b c)
    <=> (isprog_vars vs n
         # isprog_vars (p :: k :: vs) b
         # isprog_vars (p :: k :: m :: vs) c).
Proof.
  introv.
  unfold primrec.
  rw @isprog_vars_apply.
  rw @isprog_vars_fix.
  allrw @isprog_vars_lam_iff.
  rw @isprog_vars_mk_int_eq.
  rw @isprog_vars_cbv_iff.
  rw @isprog_vars_apply2.
  rw @isprog_vars_apply.
  rw @isprog_vars_sub.
  split; intro h; repnd; dands; eauto 4 with slow.
  - eapply isprog_vars_subvars;[|exact h3].
    rw subvars_prop; introv i; allrw in_app_iff; allsimpl; tcsp.
  - eapply isprog_vars_subvars;[|exact h5].
    rw subvars_prop; introv i; allsimpl; allrw in_app_iff; allsimpl; tcsp.
  - eapply isprog_vars_subvars;[|exact h1].
    rw subvars_prop; introv i; allsimpl; allrw in_app_iff; allsimpl; tcsp.
  - eapply isprog_vars_subvars;[|exact h].
    rw subvars_prop; introv i; allsimpl; allrw in_app_iff; allsimpl; tcsp.
  - apply isprog_vars_var_iff; simpl; allrw in_app_iff; simpl; tcsp.
Qed.

Definition cpM_aux {o} (F : @NTerm o) (p k m i r c x z e : NVar) (n f : NTerm) : NTerm :=
  primrec p k m
          n
          (test2 F c x z e n f)
          (mk_lam i
                  (mk_lam r
                          (mk_isint
                             (test2 F c x z e (mk_var i) f)
                             mk_axiom
                             (mk_var r)))).

Definition cpM {o} (F : @NTerm o) : NTerm :=
  mk_lam
    nvarn
    (mk_lam
       nvarf
       (cpM_aux F nvarp nvark nvarm nvari nvarr nvarc nvarx nvarz nvare
                (mk_var nvarn) (mk_var nvarf))).

Definition spM {o} (F : @NTerm o) : NTerm :=
  mk_lam
    nvarn
    (mk_lam
       nvarf
       (test2 F nvarc nvarx nvarz nvare
              (mk_var nvarn) (mk_var nvarf))).

Lemma isprog_vars_boundl {o} :
  forall x e n f,
    wf_term x
    -> wf_term e
    -> wf_term n
    -> wf_term f
    -> @isprog_vars o (free_vars x ++ free_vars e ++ free_vars n ++ free_vars f) (boundl x e n f).
Proof.
  introv wx we wn wf.
  unfold boundl.
  apply isprog_vars_less_implies; dands; eauto 3 with slow.
  - apply implies_isprog_vars; eauto with slow.
  - apply isprog_vars_apply; dands; eauto 5 with slow.
  - apply isprog_vars_exception_implies; eauto 3 with slow.
    apply implies_isprog_vars; eauto with slow.
Qed.

Lemma isprog_vars_boundl2 {o} :
  forall z x e n f,
    wf_term x
    -> wf_term e
    -> wf_term n
    -> wf_term f
    -> @isprog_vars o (free_vars x ++ free_vars e ++ free_vars n ++ free_vars f) (boundl2 z x e n f).
Proof.
  introv wx we wn wf.
  apply isprog_vars_less_implies; dands; eauto 3 with slow.
  apply isprog_vars_boundl; auto.
Qed.

Lemma isprog_vars_bound {o} :
  forall x e n f,
    wf_term e
    -> wf_term n
    -> wf_term f
    -> @isprog_vars o (free_vars e ++ free_vars n ++ free_vars f) (bound x e n f).
Proof.
  introv we wn wf.
  unfold bound.
  apply isprog_vars_lam.
  eapply isprog_vars_subvars;[|apply isprog_vars_boundl]; eauto 3 with slow.
Qed.

Lemma isprog_vars_bound2 {o} :
  forall x z e n f,
    wf_term e
    -> wf_term n
    -> wf_term f
    -> @isprog_vars o (free_vars e ++ free_vars n ++ free_vars f) (bound2 x z e n f).
Proof.
  introv we wn wf.
  unfold bound2.
  apply isprog_vars_lam.
  eapply isprog_vars_subvars;[|apply isprog_vars_boundl2]; eauto 3 with slow.
Qed.

Lemma isprog_vars_app_bound2 {o} :
  forall (F : @NTerm o) x z e n f,
    isprog F
    -> wf_term e
    -> wf_term n
    -> wf_term f
    -> isprog_vars (free_vars e ++ free_vars n ++ free_vars f)
                   (app_bound2 F x z e n f).
Proof.
  introv isp we wn wf.
  apply isprog_vars_apply; dands; eauto 3 with slow.
  apply isprog_vars_bound2; auto.
Qed.

Lemma isprog_vars_test_try2 {o} :
  forall (F : @NTerm o) c x z e n f,
    isprog F
    -> wf_term e
    -> wf_term n
    -> wf_term f
    -> isprog_vars (free_vars e ++ free_vars n ++ free_vars f) (test_try2 F c x z e n f).
Proof.
  introv ispF wfe wfn wff.
  apply isprog_vars_try_implies; eauto 3 with slow.
  eapply isprog_vars_subvars;[|apply isprog_vars_app_bound2; eauto 3 with slow]; auto.
Qed.

Lemma isprog_vars_test2 {o} :
  forall (F : @NTerm o) c x z e n f,
    isprog F
    -> wf_term n
    -> wf_term f
    -> isprog_vars (free_vars n ++ free_vars f) (test2 F c x z e n f).
Proof.
  introv ispF wn wf.
  apply isprog_vars_fresh_implies.
  eapply isprog_vars_subvars;[|apply isprog_vars_test_try2; eauto 3 with slow].
  simpl; auto.
Qed.

Lemma implies_isprog_vars_cpM_aux {o} :
  forall (F : @NTerm o) p k m i r c x z e n f,
    isprog F
    -> wf_term n
    -> wf_term f
    -> isprog_vars (free_vars n ++ free_vars f) (cpM_aux F p k m i r c x z e n f).
Proof.
  introv isp wn wf.
  unfold cpM_aux.
  apply isprog_vars_primrec; dands; eauto 3 with slow.
  - eapply isprog_vars_subvars;[|apply isprog_vars_test2]; auto.
    rw subvars_prop; simpl; tcsp.
  - repeat (apply isprog_vars_lam).
    apply isprog_vars_isint; dands; eauto 3 with slow.
    eapply isprog_vars_subvars;[|apply isprog_vars_test2]; eauto 3 with slow.
    simpl; rw subvars_prop; introv h; allsimpl; allrw in_app_iff; tcsp.
Qed.

Lemma implies_isprog_cpM {o} :
  forall (F : @NTerm o), isprog F -> isprog (cpM F).
Proof.
  introv isp.

  unfold cpM.
  apply isprog_lam.
  apply isprog_vars_lam.
  eapply isprog_vars_subvars;[|apply implies_isprog_vars_cpM_aux];eauto 3 with slow.
  simpl; auto; rw subvars_prop; simpl; tcsp.
Qed.

Definition cpM_c {o} (F : @CTerm o) :=
  let (f,x) := F in
  exist isprog (cpM f) (implies_isprog_cpM f x).

Lemma implies_isprog_spM {o} :
  forall (F : @NTerm o), isprog F -> isprog (spM F).
Proof.
  introv isp.

  unfold spM.
  apply isprog_lam.
  apply isprog_vars_lam.
  eapply isprog_vars_subvars;[|apply isprog_vars_test2]; eauto 3 with slow.
  rw subvars_prop; simpl; tcsp.
Qed.

Definition spM_c {o} (F : @CTerm o) :=
  let (f,x) := F in
  exist isprog (spM f) (implies_isprog_spM f x).

Lemma implies_isprog_varse_test_try2 {o} :
  forall (F : @NTerm o) c x z e n f,
    isprog F
    -> isprog n
    -> isprog f
    -> isprog_vars [e] (test_try2 F c x z (mk_var e) n f).
Proof.
  introv ispF ispn ispf.
  apply isprog_vars_try_implies; eauto 3 with slow.
  eapply isprog_vars_subvars;[|apply isprog_vars_app_bound2; eauto 3 with slow].
  allapply @closed_if_isprog.
  rw ispn; rw ispf.
  simpl; auto.
Qed.

Definition test_try2_cv {o} (F : @CTerm o) (c x z e : NVar) (n f : @CTerm o) : CVTerm [e] :=
  let (tF,pF) := F in
  let (tn,pn) := n in
  let (tf,pf) := f in
  exist (isprog_vars [e])
        (test_try2 tF c x z (mk_var e) tn tf)
        (implies_isprog_varse_test_try2 tF c x z e tn tf pF pn pf).

Lemma implies_isprog_bound {o} :
  forall x (e n f : @NTerm o),
    isprog e
    -> isprog n
    -> isprog f
    -> isprog (bound x e n f).
Proof.
  introv ispe ispn ispf.
  apply isprog_vars_nil_implies_isprog.
  eapply isprog_vars_subvars;[|apply isprog_vars_bound]; eauto 3 with slow.
  apply closed_if_isprog in ispe; rw ispe.
  apply closed_if_isprog in ispn; rw ispn.
  apply closed_if_isprog in ispf; rw ispf.
  simpl; auto.
Qed.

Lemma implies_isprog_bound2 {o} :
  forall x z (e n f : @NTerm o),
    isprog e
    -> isprog n
    -> isprog f
    -> isprog (bound2 x z e n f).
Proof.
  introv ispe ispn ispf.
  apply isprog_vars_nil_implies_isprog.
  eapply isprog_vars_subvars;[|apply isprog_vars_bound2]; eauto 3 with slow.
  apply closed_if_isprog in ispe; rw ispe.
  apply closed_if_isprog in ispn; rw ispn.
  apply closed_if_isprog in ispf; rw ispf.
  simpl; auto.
Qed.

Definition bound_c {o} (e n f : @CTerm o) (x : NVar) : CTerm :=
  let (te,pe) := e in
  let (tn,pn) := n in
  let (tf,pf) := f in
  exist isprog (bound x te tn tf) (implies_isprog_bound x te tn tf pe pn pf).

Lemma substc_test_try2_cv {o} :
  forall (F : @CTerm o) (n f a : CTerm),
    substc a nvare (test_try2_cv F nvarc nvarx nvarz nvare n f)
    = mkc_try (mkc_apply F (bound2_c nvarx nvarz n f a)) a nvarc (mkcv_axiom nvarc).
Proof.
  introv; destruct_cterms.
  apply cterm_eq; simpl.
  unfsubst; simpl; auto.
  repeat (rw @lsubst_aux_trivial_cl2; eauto 3 with slow).
Qed.

Lemma implies_isprog_test2 {o} :
  forall (F n f: @NTerm o) c x z e,
    isprog F
    -> isprog n
    -> isprog f
    -> isprog (test2 F c x z e n f).
Proof.
  introv ispF ispn ispf.
  apply isprog_vars_nil_implies_isprog.
  eapply isprog_vars_subvars;[|apply isprog_vars_test2]; eauto 3 with slow.
  apply closed_if_isprog in ispn; rw ispn.
  apply closed_if_isprog in ispf; rw ispf.
  simpl; auto.
Qed.

Definition test2_c {o} (F n f : @CTerm o) (c x z e : NVar) : CTerm :=
  let (tF,pF) := F in
  let (tn,pn) := n in
  let (tf,pf) := f in
  exist isprog (test2 tF c x z e tn tf) (implies_isprog_test2 tF tn tf c x z e pF pn pf).

Lemma test_c_eq {o} :
  forall (F n f : @CTerm o) (c x z e : NVar),
    test2_c F n f c x z e
    = mkc_fresh e (test_try2_cv F c x z e n f).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma implies_isprog_boundl {o} :
  forall (x e n f : @NTerm o),
    isprog x
    -> isprog e
    -> isprog n
    -> isprog f
    -> isprog (boundl x e n f).
Proof.
  introv ispx ispe ispn ispf.
  apply isprog_vars_nil_implies_isprog.
  eapply isprog_vars_subvars;[|apply isprog_vars_boundl]; eauto 3 with slow.
  apply closed_if_isprog in ispx; rw ispx.
  apply closed_if_isprog in ispe; rw ispe.
  apply closed_if_isprog in ispn; rw ispn.
  apply closed_if_isprog in ispf; rw ispf.
  simpl; auto.
Qed.

Lemma implies_isprog_boundl2 {o} :
  forall z (x e n f : @NTerm o),
    isprog x
    -> isprog e
    -> isprog n
    -> isprog f
    -> isprog (boundl2 z x e n f).
Proof.
  introv ispx ispe ispn ispf.
  apply isprog_vars_nil_implies_isprog.
  eapply isprog_vars_subvars;[|apply isprog_vars_boundl2]; eauto 3 with slow.
  apply closed_if_isprog in ispx; rw ispx.
  apply closed_if_isprog in ispe; rw ispe.
  apply closed_if_isprog in ispn; rw ispn.
  apply closed_if_isprog in ispf; rw ispf.
  simpl; auto.
Qed.

Definition boundl_c {o} (x e n f : @CTerm o) : CTerm :=
  let (tx,px) := x in
  let (te,pe) := e in
  let (tn,pn) := n in
  let (tf,pf) := f in
  exist isprog (boundl tx te tn tf) (implies_isprog_boundl tx te tn tf px pe pn pf).

Definition boundl2_c {o} z (x e n f : @CTerm o) : CTerm :=
  let (tx,px) := x in
  let (te,pe) := e in
  let (tn,pn) := n in
  let (tf,pf) := f in
  exist isprog (boundl2 z tx te tn tf) (implies_isprog_boundl2 z tx te tn tf px pe pn pf).

Lemma boundl_c_eq {o} :
  forall (x e n f : @CTerm o),
    boundl_c x e n f
    = mkc_less x n (mkc_apply f x) (mkc_exception e mkc_axiom).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Lemma boundl2_c_eq {o} :
  forall z (x e n f : @CTerm o),
    boundl2_c z x e n f
    = mkc_less x mkc_zero (mkc_vbot z) (boundl_c x e n f).
Proof.
  introv.
  rw @boundl_c_eq.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Lemma cequivc_apply_bound_c {o} :
  forall lib (e n f : @CTerm o) x a,
    cequivc
      lib
      (mkc_apply (bound_c e n f x) a)
      (boundl_c a e n f).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  unfold bound.

  eapply cequiv_trans;
    [apply cequiv_beta_isp; eauto 3 with slow;
     eapply isprog_vars_subvars;[|apply isprog_vars_boundl; eauto 3 with slow];
     simpl; allapply @closed_if_isprog; allrw; simpl; auto|].
  rw @cl_subst_subst_aux; eauto 3 with slow.
  unfold subst_aux; simpl; fold_terms.
  boolvar; tcsp.
  rw (lsubst_aux_trivial_cl2 x1); eauto 3 with slow.
  rw (lsubst_aux_trivial_cl2 x2); eauto 3 with slow.
  rw (lsubst_aux_trivial_cl2 x3); eauto 3 with slow.

  apply cequiv_refl.
  apply isprogram_eq.
  apply implies_isprog_boundl; auto.
Qed.

Lemma cequivc_apply_bound2_c {o} :
  forall lib (e n f : @CTerm o) x z a,
    cequivc
      lib
      (mkc_apply (bound2_c x z n f e) a)
      (boundl2_c z a e n f).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.

  eapply cequiv_trans;
    [apply cequiv_beta_isp; eauto 3 with slow;
     eapply isprog_vars_subvars;[|apply isprog_vars_boundl2; eauto 3 with slow];
     simpl; allapply @closed_if_isprog; allrw; simpl; auto|].
  rw @cl_subst_subst_aux; eauto 3 with slow.
  unfold subst_aux; simpl; fold_terms.
  boolvar; tcsp.

  { rw (lsubst_aux_trivial_cl2 x1); eauto 3 with slow.
    rw (lsubst_aux_trivial_cl2 x2); eauto 3 with slow.
    rw (lsubst_aux_trivial_cl2 x3); eauto 3 with slow.

    apply cequiv_refl.
    apply isprogram_eq.
    apply implies_isprog_boundl2; auto. }

  { allrw not_over_or; repnd; GC.
    simpl; boolvar; tcsp.
    rw (lsubst_aux_trivial_cl2 x1); eauto 3 with slow.
    rw (lsubst_aux_trivial_cl2 x2); eauto 3 with slow.
    rw (lsubst_aux_trivial_cl2 x3); eauto 3 with slow.

    apply cequiv_refl.
    apply isprogram_eq.
    apply implies_isprog_boundl2; auto. }
Qed.

(* replace [e] by utoken [a] and [nat2nat] by [nat2nat a] below *)
Lemma equality_in_natk2nat_implies_equality_bound {o} :
  forall lib (f g : @CTerm o) k,
    equality lib f g (natk2nat (mkc_nat k))
    -> forall a x,
         equality lib
                  (bound_c (mkc_utoken a) (mkc_nat k) f x)
                  (bound_c (mkc_utoken a) (mkc_nat k) g x)
                  (nat2natE a).
Proof.
  introv equ; introv.
  unfold nat2natE.
  apply equality_in_fun.
  dands; eauto 3 with slow.
  introv i.

  (* beta reduce *)
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_apply_bound_c|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_apply_bound_c|].
  allrw @boundl_c_eq.

  (* let's get rid of [a0] and [a'] *)
  rw @equality_in_tnat in i.
  unfold equality_of_nat in i; exrepnd; spcast.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_less;
     [apply computes_to_valc_implies_cequivc;exact i1
     |apply cequivc_refl
     |apply implies_cequivc_apply;
       [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact i1]
     |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less;
     [apply computes_to_valc_implies_cequivc;exact i0
     |apply cequivc_refl
     |apply implies_cequivc_apply;
       [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact i0]
     |apply cequivc_refl]
    |].
  clear dependent a0.
  clear dependent a'.

  allrw @mkc_nat_eq.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_mkc_less_int|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_mkc_less_int|].
  allrw <- @mkc_nat_eq.

  boolvar.

  - assert (k0 < k) as ltk by lia.
    unfold natk2nat in equ.
    apply equality_in_fun in equ; repnd.
    clear equ0 equ1.
    pose proof (equ (mkc_nat k0) (mkc_nat k0)) as h; clear equ.
    autodimp h hyp.
    { apply equality_in_natk.
      exists k0 (Z.of_nat k); dands; spcast; tcsp; allrw <- @mkc_nat_eq;
      apply computes_to_valc_refl; eauto 2 with slow. }
    allrw @equality_in_tnat.
    apply equality_in_natE; tcsp.

  - apply equality_in_natE; right.
    fold (spexc a); dands; spcast; eauto with slow.
Qed.

Definition ntry_app_c {o} (a : get_patom_set o) x e (f : @CTerm o) :=
  mkc_lam x (mkcv_try [x]
                      (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))
                      (mkcv_utoken [x] a)
                      e
                      (mkcv_zero [e,x])).

Definition implies_equal_ntry_app_c {o} :
  forall lib a x e (f g : @CTerm o),
    e <> x
    -> equality lib f g (nat2natE a)
    -> equality lib (ntry_app_c a x e f) (ntry_app_c a x e g) nat2nat.
Proof.
  introv d equ.
  unfold nat2nat.
  unfold nat2natE in equ.
  allrw @equality_in_fun; repnd; dands; tcsp.
  clear equ1 equ0.

  introv en.
  unfold ntry_app_c.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].

  repeat (rw @mkcv_try_substc; auto).
  repeat (rw @mkcv_apply_substc).
  repeat (rw @csubst_mk_cv).
  repeat (rw @mkc_var_substc).
  repeat (rw @mkcv_utoken_substc).
  unfold mkcv_zero.
  repeat (rw @substc2_mk_cv).
  fold (@mkcv_zero o [e]).

  applydup equ in en.
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
    exists k; dands; spcast; apply computes_to_valc_refl; eauto 2 with slow.

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

Lemma type_modulus_fun_type {o} :
  forall (lib : @library o), type lib modulus_fun_type.
Proof.
  introv.
  unfold modulus_fun_type.
  apply tequality_function; dands.
  - apply type_tnat.
  - introv e.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].

    apply tequality_fun.
    dands.

    + eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      allrw @mkcv_tnat_substc.

      apply tequality_fun.
      dands.

      * eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        allrw @mkc_var_substc.

        apply equality_in_tnat in e.
        unfold equality_of_nat in e; exrepnd; spcast.
        apply tequality_mkc_natk.
        allrw @mkc_nat_eq.
        exists (Z.of_nat k) (Z.of_nat k); dands; spcast; auto.
        introv i.
        destruct (Z_lt_le_dec k0 (Z.of_nat k)); tcsp.

      * introv inh; apply type_tnat.

    + introv inh.
      allrw @csubst_mk_cv.
      apply tequality_mkc_union; dands.
      * apply type_tnat.
      * apply type_mkc_unit.
Qed.

Lemma type_modulus_fun_type_u {o} :
  forall (lib : @library o), type lib modulus_fun_type_u.
Proof.
  introv.
  unfold modulus_fun_type_u.
  apply tequality_function; dands.
  - apply type_tnat.
  - introv e.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].

    apply tequality_fun.
    dands.

    + eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      allrw @mkcv_tnat_substc.

      apply tequality_fun.
      dands.

      * eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        allrw @mkc_var_substc.

        apply equality_in_tnat in e.
        unfold equality_of_nat in e; exrepnd; spcast.
        apply tequality_mkc_natk.
        allrw @mkc_nat_eq.
        exists (Z.of_nat k) (Z.of_nat k); dands; spcast; auto.
        introv i.
        destruct (Z_lt_le_dec k0 (Z.of_nat k)); tcsp.

      * introv inh; apply type_tnat.

    + introv inh.
      allrw @csubst_mk_cv.
      apply tequality_bunion; dands.
      * apply type_tnat.
      * apply type_mkc_unit.
Qed.


(* Given a function [f] of type [nat2natE(a)], we can turn it into
   a function of type [nat2nat] as follows:
     \x.try(f(x),a,c.0)
   where 0 could be any nat.
 *)
Definition ntry_app {o} (a : get_patom_set o) x e (f : @NTerm o) :=
  mk_lam x (mk_try (mk_apply f (mk_var x)) (mk_utoken a) e mk_zero).

Definition eta_fun {o} x (f : @NTerm o) := mk_lam x (mk_apply f (mk_var x)).

Definition eta_fun_c {o} x (f : @CTerm o) :=
  mkc_lam x (mkcv_apply [x] (mk_cv [x] f) (mkc_var x)).

Lemma cequivc_apply2_spM_c {o} :
  forall lib (F a b : @CTerm o),
    cequivc
      lib
      (mkc_apply2 (spM_c F) a b)
      (test2_c F a b nvarc nvarx nvarz nvare).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  unfold spM.

  eapply cequiv_trans;
    [apply cequiv_beta2; auto;
     apply isprog_vars_lam;
     eapply isprog_vars_subvars;[|apply isprog_vars_test2]; eauto 3 with slow;
     simpl; rw subvars_prop; simpl; tcsp|].
  rw @cl_subst_subst_aux; eauto 3 with slow.
  unfold subst_aux; simpl; fold_terms.
  rw (lsubst_aux_trivial_cl2 x1); eauto 3 with slow.

  eapply cequiv_trans;
    [apply cequiv_beta_isp; eauto 3 with slow;
     eapply isprog_vars_subvars;[|apply isprog_vars_test2; eauto 3 with slow];
     simpl; allapply @closed_if_isprog; allrw; simpl; auto|].
  rw @cl_subst_subst_aux; eauto 3 with slow.
  unfold subst_aux; simpl; fold_terms.
  rw (lsubst_aux_trivial_cl2 x1); eauto 3 with slow.
  rw (lsubst_aux_trivial_cl2 x0); eauto 3 with slow.

  apply cequiv_refl.
  apply isprogram_eq.
  apply implies_isprog_test2; auto.
Qed.
