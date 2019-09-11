(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
           Abhishek Anand

 *)


Require Export cequiv_stable.
(*Require Export computation_dec.*)
Require Export sequents_tacs.
Require Export per_props_cequiv.
Require Export per_props_uni.


Definition chaltsc_bar {o} lib (a : @CTerm o) :=
  all_in_ex_bar lib (fun lib => chaltsc lib a).

Lemma cequorsq_mkc_halts {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => chaltsc lib a <=> chaltsc lib b).
Proof.
  unfold equorsq; introv; split; introv h.

  - repndors.

    + allrw @equality_in_uni_mkc_halts; auto.

    + apply in_ext_implies_all_in_ex_bar; introv x.
      pose proof (h _ x) as h; simpl in *; spcast.
      apply cequivc_decomp_halts in h; repnd; auto.
      split; intro q; spcast; apply h0; auto.

  - left.
    apply equality_in_uni_mkc_halts; auto.
Qed.

Lemma isexc_as_raises_exceptionc {o} :
  forall lib (a : @CTerm o),
    capproxc lib bot_excc a <=> raises_exceptionc lib a.
Proof.
  introv.
  split; introv h; spcast.

  - apply approx_stable in h.
    destruct_cterms.
    unfold approxc in h; allsimpl.
    unfold raises_exceptionc; simpl.
    inversion h as [cl].
    unfold close_comput in cl; repnd.
    pose proof (cl3 mk_bot mk_bot) as q.
    autodimp q hyp.
    { apply reduces_to_symm. }
    exrepnd.
    exists a' e'; auto.

  - destruct_cterms.
    unfold raises_exceptionc, raises_exception in h; allsimpl; exrepnd.
    unfold approxc; simpl.
    constructor.
    unfold close_comput; dands; eauto 3 with slow.

    { introv comp.
      apply computes_to_value_exception in comp; sp. }

    { introv comp.
      apply computes_to_exception_exception in comp; repnd; subst.
      applydup @preserve_program_exc2 in h1; eauto 3 with slow; repnd.
      exists a e; dands; auto; left;
      unfold mk_bot; apply bottom_approx_any; eauto 3 with slow. }
Qed.

Definition craises_exceptionc {o} lib (a : @CTerm o) :=
  Cast (raises_exceptionc lib a).

Lemma raises_exceptionc_stable {o} :
  forall lib (a : @CTerm o), craises_exceptionc lib a -> raises_exceptionc lib a.
Proof.
  introv h.
  apply isexc_as_raises_exceptionc; inversion h.
  apply isexc_as_raises_exceptionc; auto.
Qed.

Lemma raises_exceptionc_stable_iff {o} :
  forall lib (a : @CTerm o), craises_exceptionc lib a <=> raises_exceptionc lib a.
Proof.
  introv; split; intro h; unfold craises_exceptionc in *; spcast; auto.
  apply raises_exceptionc_stable; auto.
Qed.

Lemma tequality_mkc_isexc {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_isexc a) (mkc_isexc b)
    <=> all_in_ex_bar lib (fun lib => craises_exceptionc lib a <=> craises_exceptionc lib b).
Proof.
  introv.
  allrw @mkc_isexc_eq.
  rw @tequality_mkc_approx.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; spcast;
      allrw @isexc_as_raises_exceptionc; allrw @raises_exceptionc_stable_iff; auto.
Qed.

Definition raises_exceptionc_bar {o} lib (t : @CTerm o) :=
  all_in_ex_bar lib (fun lib => craises_exceptionc lib t).

Lemma member_isexc_iff {p} :
  forall lib (t : @CTerm p),
    raises_exceptionc_bar lib t
    <=> member lib mkc_axiom (mkc_isexc t).
Proof.
  introv.
  rw @mkc_isexc_eq.
  rw <- @member_approx_iff.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd;
      allrw @isexc_as_raises_exceptionc; allrw @raises_exceptionc_stable_iff; auto.
Qed.

Lemma cequivc_decomp_isexc {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_isexc a) (mkc_isexc b)
    <=> cequivc lib a b.
Proof.
  introv.
  allrw @mkc_isexc_eq.
  rw @cequivc_decomp_approx.
  split; introv h; repnd; dands; auto.
Qed.

Lemma raises_exceptionc_preserves_cequivc {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b
    -> raises_exceptionc lib a
    -> raises_exceptionc lib b.
Proof.
  introv ceq r.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @cequivc; allsimpl.
  allunfold @raises_exception; exrepnd.
  destruct ceq as [c1 c2].
  inversion c1 as [cl].
  unfold close_comput in cl; repnd.
  apply cl3 in r1; exrepnd.
  exists a' e'; auto.
Qed.

Lemma equality_in_uni_mkc_isexc {p} :
  forall lib i (a b : @CTerm p),
    equality lib (mkc_isexc a) (mkc_isexc b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => craises_exceptionc lib a <=> craises_exceptionc lib b).
Proof.
  introv.
  allrw @mkc_isexc_eq.
  allrw @mkc_approx_equality_in_uni.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd;
      allrw @isexc_as_raises_exceptionc; allrw @raises_exceptionc_stable_iff; auto.
Qed.

Lemma cequorsq_mkc_isexc {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_isexc a) (mkc_isexc b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => craises_exceptionc lib a <=> craises_exceptionc lib b).
Proof.
  unfold equorsq; introv; split; introv h.

  - repndors.

    + allapply @equality_in_uni.
      allrw @tequality_mkc_isexc; spcast; auto.

    + apply in_ext_implies_all_in_ex_bar; introv x.
      pose proof (h _ x) as h; simpl in *; spcast.
      rw @cequivc_decomp_isexc in h.
      unfold craises_exceptionc; split; intro q; spcast.

      * apply raises_exceptionc_preserves_cequivc in h; auto.

      * apply cequivc_sym in h; apply raises_exceptionc_preserves_cequivc in h; auto.

  - left.
    apply equality_in_uni_mkc_isexc; auto.
Qed.

Definition bot_exccv {o} (vs : list NVar) : @CVTerm o vs :=
  mk_cv vs bot_excc.

Definition halts_likec {o} lib (t : @CTerm o) (v : NVar) :=
  approxc lib bot_excc (mkc_cbv t v (bot_exccv [v])).

Lemma cbv_raises_exception_val {o} :
  forall lib (a t v u e : @NTerm o) (x : NVar),
    computes_to_value lib t v
    -> computes_to_exception lib a (subst u x v) e
    -> computes_to_exception lib a (mk_cbv t x u) e.
Proof.
  introv comp1 comp2.
  unfold computes_to_value in comp1; repnd.
  eapply reduces_to_trans;
    [apply reduces_to_prinarg; exact comp0
    |]; fold_terms.
  apply isvalue_iff in comp1; repnd.
  apply iscan_implies in comp3; repndors; exrepnd; subst;
  eapply reduces_to_if_split2; try csunf; simpl; try reflexivity;
  unfold apply_bterm; simpl; rw @fold_subst; auto.
Qed.

Lemma hasvalue_likec_iff_or {o} :
  forall lib (t : @CTerm o),
    hasvalue_likec lib t
    <=> (hasvaluec lib t [+] raises_exceptionc lib t).
Proof.
  introv; destruct_cterms.
  unfold hasvalue_likec, hasvaluec, raises_exceptionc; simpl.
  split; introv h.
  - apply hasvalue_like_implies_or; eauto 3 with slow.
  - repndors.
    + apply hasvalue_like_if_hasvalue; auto.
    + apply hasvalue_like_if_raises_exception; auto.
Qed.

Lemma isvalue_like_bot_exc {o} : @isvalue_like o bot_exc.
Proof.
  unfold bot_exc; eauto 3 with slow.
Qed.
Hint Resolve isvalue_like_bot_exc : slow.

Lemma halts_likec_as_hasvalue_likec {o} :
  forall lib (a : @CTerm o) v,
    halts_likec lib a v <=> hasvalue_likec lib a.
Proof.
  introv.
  rw @hasvalue_likec_iff_or.
  split; introv h; spcast.

  - destruct_cterms.
    unfold halts_likec, approxc in h; allsimpl.
    unfold raises_exceptionc, hasvaluec; simpl.
    inversion h as [cl].
    unfold close_comput in cl; repnd.
    pose proof (cl3 mk_bot mk_bot) as q.
    autodimp q hyp.
    { apply reduces_to_symm. }
    exrepnd.
    fold (@bot_exc o) in *.
    repndors; try (complete (allunfold @bot2; sp)).
    apply if_computes_to_exception_cbv0 in q0; eauto 3 with slow.
    repndors; exrepnd.

    + right.
      exists a' e'; auto.

    + left.
      exists x0; auto.

  - destruct_cterms.
    unfold halts_likec, approxc; simpl.
    fold (@bot_exc o).
    unfold raises_exceptionc, raises_exception, hasvaluec, hasvalue in h; allsimpl.

    constructor.
    unfold close_comput; dands; eauto 3 with slow.
    { apply isprogram_cbv_iff2; dands; eauto 3 with slow. }

    + introv comp.
      apply computes_to_value_exception in comp; sp.

    + introv comp.
      apply computes_to_exception_exception in comp; repnd; subst.
      repndors; exrepnd.

      * applydup @preserve_program in h0; eauto 3 with slow.
        exists (@mk_bot o) (@mk_bot o); dands; eauto 3 with slow;
        try (complete (left; unfold mk_bot; apply bottom_approx_any; eauto 3 with slow)).
        eapply cbv_raises_exception_val;[exact h0|].
        rw @subst_trivial; eauto 3 with slow.
        apply computes_to_exception_refl.

      * applydup @preserve_program_exc2 in h1; eauto 3 with slow; repnd.
        exists a e.
        dands; eauto 3 with slow;
        try (complete (left; unfold mk_bot; apply bottom_approx_any; eauto 3 with slow)).
        apply cbv_raises_exception; eauto 3 with slow.
Qed.

Lemma cast_halts_likec_as_hasvalue_likec {o} :
  forall lib (a : @CTerm o) v,
    Cast (halts_likec lib a v) <=> hasvalue_likec lib a.
Proof.
  introv; split; intro h; spcast.
  - apply approx_stable in h.
    apply halts_likec_as_hasvalue_likec in h; auto.
  - apply halts_likec_as_hasvalue_likec; auto.
Qed.

Lemma mkc_halts_like_eq {o} :
  forall (t : @CTerm o),
    mkc_halts_like t
    = mkc_approx bot_excc (mkc_cbv t nvarx (bot_exccv [nvarx])).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Definition computes_to_approx_exception_or_value {o} lib (a b : @NTerm o) :=
  forall n e,
    computes_to_exception lib n a e
    -> ({n' : NTerm
         & {e' : NTerm
         & computes_to_exception lib n' b e'
         # approx lib n n'
         # approx lib e e'}}
        [+] (hasvalue lib b
             # approx lib n mk_bot
             # approx lib e mk_bot)).

Lemma approx_decomp_halts_exc_as_cbv {o} :
  forall lib (a b : @NTerm o) v,
    isprogram a
    -> isprogram b
    -> (approx
          lib
          (mk_cbv a v bot_exc)
          (mk_cbv b v bot_exc)
          <=>
          (computes_to_approx_exception_or_value lib a b
           # (hasvalue lib a -> hasvalue_like lib b))).
Proof.
  introv ispa ispb.
  split; intro h; dands.

  - introv comp.
    inversion h as [c]; clear h.
    unfold close_comput in c; repnd.
    pose proof (c3 n e) as k.
    autodimp k hyp.
    { apply cbv_raises_exception; auto. }
    exrepnd.
    repndors; try (complete (allunfold @bot2; sp)).
    apply if_computes_to_exception_cbv0 in k0; auto; repndors; exrepnd.

    + left; exists a' e'; dands; auto.

    + applydup @preserve_program in k0; auto.
      rw @subst_trivial in k3; eauto 3 with slow.
      apply computes_to_exception_exception in k3; repnd; subst.
      right; dands; auto.
      exists x; auto.

  - introv hv.
    inversion h as [c]; clear h.
    unfold close_comput in c; repnd.
    pose proof (c3 (@mk_bot o) (@mk_bot o)) as k.
    autodimp k hyp.
    { unfold hasvalue in hv; exrepnd.
      eapply cbv_raises_exception_val;[exact hv0|].
      applydup @preserve_program in hv0; auto.
      rw @subst_trivial; eauto 3 with slow.
      apply computes_to_exception_refl. }
    exrepnd.
    repndors; try (complete (allunfold @bot2; sp)).
    apply if_computes_to_exception_cbv0 in k0; eauto 3 with slow.
    repndors; exrepnd.

    + exists (mk_exception a' e'); dands; eauto 2 with slow.

    + unfold computes_to_value in k0; repnd.
      exists x; dands; eauto 3 with slow.

  - constructor.
    unfold close_comput; dands; auto;
    try (complete (apply isprogram_cbv_iff2; dands; eauto 3 with slow)).

    + introv comp.
      apply computes_to_value_hasvalue in comp.
      apply if_hasvalue_cbv in comp; eauto 3 with slow.
      exrepnd.
      applydup @preserve_program in comp1; auto.
      rw @subst_trivial in comp0; eauto 3 with slow.
      unfold hasvalue in comp0; exrepnd.
      apply computes_to_value_exception in comp3; sp.

    + introv comp.
      applydup @if_computes_to_exception_cbv0 in comp; auto.
      repndors; exrepnd.

      * apply h0 in comp0; clear h; repndors; exrepnd.

        { exists n' e'.
          dands; auto.
          apply cbv_raises_exception; auto. }

        { exists (@mk_bot o) (@mk_bot o); dands; auto.
          unfold hasvalue in comp1; exrepnd.
          applydup @preserve_program in comp3; auto.
          eapply cbv_raises_exception_val;[exact comp3|].
          rw @subst_trivial; eauto 3 with slow.
          apply computes_to_exception_refl. }

      * applydup @preserve_program in comp0; auto.
        rw @subst_trivial in comp1; eauto 3 with slow.
        apply computes_to_exception_exception in comp1; repnd; subst.
        autodimp h hyp.
        { exists x; auto. }
        apply hasvalue_like_implies_or in h; auto.
        repndors.

        { unfold hasvalue in h; exrepnd.
          exists (@mk_bot o) (@mk_bot o); dands; auto;
          try (complete (left; unfold mk_bot; apply bottom_approx_any; eauto 3 with slow)).
          eapply cbv_raises_exception_val;[exact h1|].
          applydup @preserve_program in h1; auto.
          rw @subst_trivial; eauto 3 with slow.
          apply computes_to_exception_refl. }

        { unfold raises_exception in h; exrepnd.
          applydup @preserve_program_exc2 in h2; eauto 3 with slow; repnd.
          exists a0 e; dands;
          try (complete (left; unfold mk_bot; apply bottom_approx_any; eauto 3 with slow)).
          apply cbv_raises_exception; auto. }
Qed.

Definition chasvalue_likec {o} lib (a : @CTerm o) :=
  Cast (hasvalue_likec lib a).

Lemma cast_halts_likec_as_chasvalue_likec {o} :
  forall lib (a : @CTerm o) v,
    Cast (halts_likec lib a v) <=> chasvalue_likec lib a.
Proof.
  introv; unfold chasvalue_likec; split; intro h; spcast.
  - apply halts_likec_as_hasvalue_likec in h; auto.
  - apply halts_likec_as_hasvalue_likec; auto.
Qed.

Definition hasvalue_likec_bar {o} lib (a : @CTerm o) :=
  all_in_ex_bar lib (fun lib => chasvalue_likec lib a).

Lemma member_halts_like_iff {p} :
  forall lib (t : @CTerm p),
    member lib mkc_axiom (mkc_halts_like t)
    <=> hasvalue_likec_bar lib t.
Proof.
  introv.
  rw @mkc_halts_like_eq.
  rw <- @member_approx_iff.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; auto;
      allrw @cast_halts_likec_as_chasvalue_likec; auto.
Qed.

(*Lemma lib_extends_preserves_hasvalue_likec {o} :
  forall {lib lib'} (x : lib_extends lib' lib) (a : @CTerm o),
    hasvalue_likec lib a
    -> hasvalue_likec lib' a.
Proof.
  introv x h.
  unfold hasvalue_likec, hasvalue_like in *; exrepnd.
  exists v; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_hasvalue_likec : slow.*)

(*Lemma chasvalue_likec_implies_hasvalue_likec_bar {o} :
  forall lib (a : @CTerm o),
    chasvalue_likec lib a
    -> hasvalue_likec_bar lib a.
Proof.
  introv h.
  apply in_ext_implies_all_in_ex_bar; introv x.
  unfold chasvalue_likec in *; spcast; eauto 3 with slow.
Qed.*)

Lemma hasvalue_likec_stable {o} :
  forall lib (a : @CTerm o), chasvalue_likec lib a -> hasvalue_likec lib a.
Proof.
  introv h.
  unfold chasvalue_likec in h.

  pose proof (cast_halts_likec_as_hasvalue_likec lib a nvarx) as q.
  apply q; spcast.
  apply halts_likec_as_hasvalue_likec.
  auto.
Qed.

Lemma hasvalue_likec_stable_iff {o} :
  forall lib (a : @CTerm o), chasvalue_likec lib a <=> hasvalue_likec lib a.
Proof.
  introv; split; intro h; try apply hasvalue_likec_stable; auto.
  constructor; auto.
Qed.

Lemma tequality_mkc_halts_like {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_halts_like a) (mkc_halts_like b)
    <=> all_in_ex_bar lib (fun lib => chasvalue_likec lib a <=> chasvalue_likec lib b).
Proof.
  introv.
  allrw @mkc_halts_like_eq.
  rw @tequality_mkc_approx.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd;
      allrw @cast_halts_likec_as_hasvalue_likec; allrw @hasvalue_likec_stable_iff; auto.
Qed.

Lemma cequiv_decomp_halts_exc_as_cbv {o} :
  forall lib (a b : @NTerm o) v,
    isprogram a
    -> isprogram b
    -> (cequiv
          lib
          (mk_cbv a v bot_exc)
          (mk_cbv b v bot_exc)
          <=>
          ((hasvalue lib a -> hasvalue_like lib b)
           # (hasvalue lib b -> hasvalue_like lib a)
           # computes_to_approx_exception_or_value lib a b
           # computes_to_approx_exception_or_value lib b a)).
Proof.
  introv ispa ispb.
  unfold cequiv, compute_to_cequiv_exceptions.
  pose proof (approx_decomp_halts_exc_as_cbv lib a b v) as h.
  repeat (autodimp h hyp).
  pose proof (approx_decomp_halts_exc_as_cbv lib b a v) as k.
  repeat (autodimp k hyp).
  rw h.
  rw k.
  clear h k.
  split; intro h; repnd; dands; auto.
Qed.

Definition computes_to_approxc_exception_or_value {o} lib (a b : @CTerm o) :=
  computes_to_approx_exception_or_value lib (get_cterm a) (get_cterm b).

Lemma cequivc_decomp_halts_exc_as_cbv {o} :
  forall lib (a b : @CTerm o) v,
    cequivc
      lib
      (mkc_cbv a v (bot_exccv [v]))
      (mkc_cbv b v (bot_exccv [v]))
    <=>
    ((hasvaluec lib a -> hasvalue_likec lib b)
     # (hasvaluec lib b -> hasvalue_likec lib a)
     # computes_to_approxc_exception_or_value lib a b
     # computes_to_approxc_exception_or_value lib b a).
Proof.
  introv.
  destruct_cterms.
  apply cequiv_decomp_halts_exc_as_cbv; simpl; eauto 3 with slow.
Qed.

Lemma cequivc_decomp_halts_like {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_halts_like a) (mkc_halts_like b)
    <=>
    ((hasvaluec lib a -> hasvalue_likec lib b)
     # (hasvaluec lib b -> hasvalue_likec lib a)
     # computes_to_approxc_exception_or_value lib a b
     # computes_to_approxc_exception_or_value lib b a).
Proof.
  introv.
  allrw @mkc_halts_like_eq.
  rw @cequivc_decomp_approx.
  allrw @cequivc_decomp_halts_exc_as_cbv.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma equality_in_uni_mkc_halts_like {p} :
  forall lib i (a b : @CTerm p),
    equality lib (mkc_halts_like a) (mkc_halts_like b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => chasvalue_likec lib a <=> chasvalue_likec lib b).
Proof.
  introv.
  allrw @mkc_halts_like_eq.
  allrw @mkc_approx_equality_in_uni.
  split; intro e;
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd;
      allrw @cast_halts_likec_as_hasvalue_likec; allrw @hasvalue_likec_stable_iff; auto.
Qed.

Lemma cequivc_halts_like_preserves_hasvalue_likec {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_halts_like a) (mkc_halts_like b)
    -> hasvalue_likec lib a
    -> hasvalue_likec lib b.
Proof.
  introv ceq hv.
  rw @cequivc_decomp_halts_like in ceq; repnd.
  allrw @hasvalue_likec_iff_or; repndors; tcsp.
  destruct_cterms.
  allunfold @computes_to_approxc_exception_or_value; allsimpl.
  allunfold @raises_exceptionc; allsimpl.
  allunfold @hasvaluec; allsimpl.
  allunfold @computes_to_approx_exception_or_value; allsimpl.
  unfold raises_exception in hv; exrepnd.
  apply ceq2 in hv1.
  repndors; exrepnd; tcsp.
  right; exists n' e'; sp.
Qed.

Lemma cequorsq_mkc_halts_like {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_halts_like a) (mkc_halts_like b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => chasvalue_likec lib a <=> chasvalue_likec lib b).
Proof.
  unfold equorsq; introv; split; introv h.

  - repndors.

    + allapply @equality_in_uni.
      allrw @tequality_mkc_halts_like; auto.

    + apply in_ext_implies_all_in_ex_bar; introv x.
      pose proof (h _ x) as h; simpl in *; spcast.
      allrw @hasvalue_likec_stable_iff; auto.
      split; intro q.

      * eapply cequivc_halts_like_preserves_hasvalue_likec; eauto.

      * apply cequivc_sym in h.
        eapply cequivc_halts_like_preserves_hasvalue_likec; eauto.

  - left.
    apply equality_in_uni_mkc_halts_like; auto.
Qed.
