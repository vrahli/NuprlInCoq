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



Require Export Coq.Logic.ConstructiveEpsilon.

Require Export cequiv_bind.
Require Export computation_dec1.
Require Export per.


Lemma hasvalue_likec_eq {o} :
  forall lib (t : @CTerm o),
    hasvalue_likec lib t
    <=> (hasvaluec lib t [+] raises_exceptionc lib t).
Proof.
  introv.
  destruct_cterms.
  unfold hasvalue_likec, hasvaluec, raises_exceptionc; simpl.
  split; intro h; repnd.
  - apply hasvalue_like_implies_or; eauto 3 with slow.
  - repndors.
    + apply hasvalue_like_if_hasvalue; auto.
    + apply hasvalue_like_if_raises_exception; auto.
Qed.

Lemma cast_capprox_value {o} :
  forall lib (a b : @NTerm o) c bs,
    Cast (approx lib a b)
    -> computes_to_value lib a (oterm (Can c) bs)
    -> {k : nat
        , {u : NTerm
        , reduces_in_atmost_k_steps lib b u k
        # isccan u}}.
Proof.
  introv apr comp; spcast.
  inversion apr as [cc].
  unfold close_comput in cc; repnd.
  apply cc2 in comp; exrepnd.
  unfold computes_to_value, reduces_to in comp1; exrepnd.
  exists k.
  exists (oterm (Can c) tr_subterms); dands; auto.
Qed.

Lemma cast_capprox_value2 {o} :
  forall lib (a b : @NTerm o) c bs,
    Cast (approx lib a b)
    -> computes_to_value lib a (oterm (Can c) bs)
    -> {k : nat
        , {bs' : list BTerm
        , reduces_in_atmost_k_steps lib b (oterm (Can c) bs') k}}.
Proof.
  introv apr comp; spcast.
  inversion apr as [cc].
  unfold close_comput in cc; repnd.
  apply cc2 in comp; exrepnd.
  unfold computes_to_value, reduces_to in comp1; exrepnd.
  exists k.
  exists tr_subterms; dands; auto.
Qed.

Lemma cast_capprox_exc {o} :
  forall lib (a b : @NTerm o) n e,
    Cast (approx lib a b)
    -> computes_to_exception lib n a e
    -> {k : nat
        , {n' : NTerm
        , {e' : NTerm
        , reduces_in_atmost_k_steps lib b (mk_exception n' e') k}}}.
Proof.
  introv apr comp; spcast.
  inversion apr as [cc].
  unfold close_comput in cc; repnd.
  apply cc3 in comp; exrepnd.
  unfold computes_to_exception, reduces_to in comp0; exrepnd.
  exists k.
  exists a' e'; dands; auto.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm & reduces_in_atmost_k_steps lib t v k}.
Proof.
  introv.
  remember (compute_at_most_k_steps lib k t) as c; symmetry in Heqc.
  destruct c.
  - left.
    exists n; auto.
  - right; intro r; exrepnd; rw r0 in Heqc; ginv.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_exc {o} :
  forall lib k (t : @NTerm o),
    decidable {n : NTerm & {e : NTerm & reduces_in_atmost_k_steps lib t (mk_exception n e) k}}.
Proof.
  introv.
  remember (compute_at_most_k_steps lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct n as [v|op bs].
    + right.
      intro r; exrepnd.
      rw r1 in Heqc; ginv.
    + dopid op as [can|ncan|exc|abs] Case;
      try (complete (right; intro r; exrepnd; rw r1 in Heqc; ginv)).
      repeat (destruct bs; try (complete (right; intro r; exrepnd; rw r1 in Heqc; ginv))).
      destruct b as [l1 t1].
      destruct b0 as [l2 t2].
      destruct l1; try (complete (right; intro r; exrepnd; rw r1 in Heqc; ginv)).
      destruct l2; try (complete (right; intro r; exrepnd; rw r1 in Heqc; ginv)).
      fold_terms.
      left; exists t1 t2; auto.
  - right; intro r; exrepnd; rw r1 in Heqc; ginv.
Qed.

Lemma reduces_in_atmost_k_steps_eq {o} :
  forall lib (k : nat) (t t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t t1 k
    -> reduces_in_atmost_k_steps lib t t2 k
    -> t1 = t2.
Proof.
  introv r1 r2.
  pose proof (compute_at_most_k_steps_eq lib k t (csuccess t1) (csuccess t2)) as h.
  repeat (autodimp h hyp); ginv; auto.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_iscan {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm & reduces_in_atmost_k_steps lib t v k # iscan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps lib k t) as [d|d].
  - exrepnd.
    destruct (dec_iscan v) as [p|p].
    + left; exists v; sp.
    + right; intro h; exrepnd.
      eapply reduces_in_atmost_k_steps_eq in d0;[|exact h1]; subst; sp.
  - right; introv h; destruct d; exrepnd.
    exists v; auto.
Qed.

Lemma dec_isccan {o} :
  forall (t : @NTerm o), decidable (isccan t).
Proof.
  introv.
  destruct t as [v|op bs]; simpl; tcsp; try (complete (right; sp)).
  dopid op as [can|ncan|exc|abs] Case; tcsp; try (complete (right; sp)).
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_isccan {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm & reduces_in_atmost_k_steps lib t v k # isccan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps lib k t) as [d|d].
  - exrepnd.
    destruct (dec_isccan v) as [p|p].
    + left; exists v; sp.
    + right; intro h; exrepnd.
      eapply reduces_in_atmost_k_steps_eq in d0;[|exact h1]; subst; sp.
  - right; introv h; destruct d; exrepnd.
    exists v; auto.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_iscan_prop {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm , reduces_in_atmost_k_steps lib t v k # iscan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_iscan lib k t) as [d|d].
  - left; exrepnd; exists v; sp.
  - right; intro h; exrepnd; destruct d; exists v; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_iscan_prop2 {o} :
  forall lib k (t : @NTerm o),
    {{v : NTerm , reduces_in_atmost_k_steps lib t v k # iscan v}}
    + {!{v : NTerm , reduces_in_atmost_k_steps lib t v k # iscan v}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_iscan_prop lib k t) as [d|d]; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_isccan_prop {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm , reduces_in_atmost_k_steps lib t v k # isccan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_isccan lib k t) as [d|d].
  - left; exrepnd; exists v; sp.
  - right; intro h; exrepnd; destruct d; exists v; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_isccan_prop2 {o} :
  forall lib k (t : @NTerm o),
    {{v : NTerm , reduces_in_atmost_k_steps lib t v k # isccan v}}
    + {!{v : NTerm , reduces_in_atmost_k_steps lib t v k # isccan v}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_isccan_prop lib k t) as [d|d]; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_exc_prop {o} :
  forall lib k (t : @NTerm o),
    decidable {n : NTerm , {e : NTerm , reduces_in_atmost_k_steps lib t (mk_exception n e) k}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_exc lib k t) as [d|d].
  - left; exrepnd; exists n e; sp.
  - right; intro h; exrepnd; destruct d; exists n e; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_exc_prop2 {o} :
  forall lib k (t : @NTerm o),
    {{n : NTerm , {e : NTerm , reduces_in_atmost_k_steps lib t (mk_exception n e) k}}}
    + {!{n : NTerm , {e : NTerm , reduces_in_atmost_k_steps lib t (mk_exception n e) k}}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_exc_prop lib k t) as [d|d]; sp.
Qed.

Lemma ex_reduces_in_atmost_k_steps_can {o} :
  forall lib (t : @NTerm o) k,
    {u : NTerm , reduces_in_atmost_k_steps lib t u k # iscan u}
    -> {u : NTerm & reduces_in_atmost_k_steps lib t u k # iscan u}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps lib k t) as [d|d].
  - exrepnd.
    destruct (dec_iscan v) as [p|p].
    + exists v; sp.
    + provefalse; exrepnd.
      eapply reduces_in_atmost_k_steps_eq in comp1;[|exact d0]; subst; tcsp.
  - provefalse; exrepnd; destruct d.
    exists u; auto.
Qed.

Lemma ex_reduces_in_atmost_k_steps_ccan {o} :
  forall lib (t : @NTerm o) k,
    {u : NTerm , reduces_in_atmost_k_steps lib t u k # isccan u}
    -> {u : NTerm & reduces_in_atmost_k_steps lib t u k # isccan u}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps lib k t) as [d|d].
  - exrepnd.
    destruct (dec_isccan v) as [p|p].
    + exists v; sp.
    + provefalse; exrepnd.
      eapply reduces_in_atmost_k_steps_eq in comp1;[|exact d0]; subst; tcsp.
  - provefalse; exrepnd; destruct d.
    exists u; auto.
Qed.

Lemma ex_reduces_in_atmost_k_steps_exc {o} :
  forall lib (t : @NTerm o) k,
    {n : NTerm , {e : NTerm , reduces_in_atmost_k_steps lib t (mk_exception n e) k}}
    -> {n : NTerm & {e : NTerm & reduces_in_atmost_k_steps lib t (mk_exception n e) k}}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps_exc lib k t) as [d|d].
  - exrepnd.
    exists n e; auto.
  - provefalse; exrepnd; destruct d.
    exists n e; auto.
Qed.

Lemma cast_capprox_value3 {o} :
  forall lib (a b : @NTerm o) c bs1 bs2,
    Cast (approx lib a b)
    -> computes_to_value lib a (oterm (Can c) bs1)
    -> computes_to_value lib b (oterm (Can c) bs2)
    -> length bs1 = length bs2
       # (forall n : nat,
            n < length bs1
            -> {lv : list NVar
                , {nt1, nt2 : NTerm
                , Cast (olift (approx_aux lib bot2 \2/ bot2) nt1 nt2)
                # Cast (alpha_eq_bterm (bs1 {[n]}) (bterm lv nt1))
                # Cast (alpha_eq_bterm (bs2 {[n]}) (bterm lv nt2))}}).
Proof.
  introv apr comp1 comp2.
  unfold lblift; dands; spcast.

  - inversion apr as [cl].
    unfold close_comput in cl; repnd.
    apply cl2 in comp1; exrepnd.
    eapply computes_to_value_eq in comp1;[|exact comp2]; ginv.
    unfold lblift in comp0; sp.

  - introv ltn.
    inversion apr as [cl].
    unfold close_comput in cl; repnd.
    apply cl2 in comp1; exrepnd.
    eapply computes_to_value_eq in comp1;[|exact comp2]; ginv.
    unfold lblift in comp0; sp.
    apply comp0 in ltn.
    unfold blift in ltn; exrepnd.
    exists lv nt1 nt2; sp.
Qed.

Lemma cast_capprox_value4 {o} :
  forall lib (a b : @NTerm o) c bs1 bs2,
    Cast (approx lib a b)
    -> computes_to_value lib a (oterm (Can c) bs1)
    -> computes_to_value lib b (oterm (Can c) bs2)
    -> length bs1 = length bs2
       # (forall n : nat,
            n < length bs1
            -> Cast (blift (olift (approx_aux lib bot2 \2/ bot2)) (bs1 {[n]}) (bs2 {[n]}))).
Proof.
  introv apr comp1 comp2.
  unfold lblift; dands; spcast.

  - inversion apr as [cl].
    unfold close_comput in cl; repnd.
    apply cl2 in comp1; exrepnd.
    eapply computes_to_value_eq in comp1;[|exact comp2]; ginv.
    unfold lblift in comp0; sp.

  - introv ltn.
    inversion apr as [cl].
    unfold close_comput in cl; repnd.
    apply cl2 in comp1; exrepnd.
    eapply computes_to_value_eq in comp1;[|exact comp2]; ginv.
    unfold lblift in comp0; sp.
Qed.

Lemma isccan_implies {p} :
  forall t : @NTerm p,
    isccan t
    -> {c : CanonicalOp
        & {bterms : list BTerm
        & t = oterm (Can c) bterms}}.
Proof.
  introv isc.
  destruct t as [v|op bs]; try (complete (inversion isc)).
  destruct op; try (complete (inversion isc)).
  exists c bs; sp.
Qed.

Lemma alpha_stable {o} :
  forall (a b : @NTerm o), Cast (alpha_eq a b) -> alpha_eq a b.
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv ca.

  - Case "vterm".
    destruct b as [v2|op2 bs2];
      try (complete (provefalse; spcast; inversion ca; subst; tcsp)).

    destruct (deq_nvar v v2); subst; auto.
    provefalse; spcast; inversion ca; subst; tcsp.

  - Case "oterm".
    destruct b as [v2|op2 bs2];
      try (complete (provefalse; spcast; inversion ca; subst; tcsp)).

    assert (op = op2) as eqop.
    { spcast; inversion ca; subst; auto. }
    subst.

    assert (length bs = length bs2) as eqlbs.
    { spcast; inversion ca; subst; auto. }

    apply alpha_eq_oterm_combine2; dands; auto.
    introv i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].

    applydup in_combine in i; repnd.

    assert (length l1 = length l2) as eql.
    { spcast.
      apply alpha_eq_oterm_combine in ca; repnd.
      apply ca in i.
      inversion i; auto. }

    pose proof (fresh_vars (length l1) (all_vars t1 ++ all_vars t2)) as fvs; exrepnd.
    apply (al_bterm _ _ lvn); auto.
    apply (ind t1 (lsubst t1 (var_ren l1 lvn)) l1); auto.
    { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }

    spcast.
    apply alpha_eq_oterm_combine in ca; repnd.
    apply ca in i.
    apply (alphabt_change_var _ _ _ _ lvn) in i; tcsp.
Qed.

Lemma approx_stable {o} :
  forall lib (a b : @CTerm o), capproxc lib a b -> approxc lib a b.
Proof.
  introv.
  destruct_cterms.
  unfold capproxc, approxc; simpl.

  (* use approx_acc_resp instead? *)
  revert x0 x i0 i.
  cofix CIH.
  intros t1 t2 ispt1 ispt2 h.
  constructor; constructor; dands; try (complete sp); eauto 3 with slow.

  - introv cp.
    dup h as ca.
    eapply cast_capprox_value in ca;[|exact cp].
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in ca; auto;
    [|introv;apply dec_ex_reduces_in_atmost_k_steps_isccan_prop2].

    exrepnd.
    apply ex_reduces_in_atmost_k_steps_ccan in ca0; exrepnd.
    apply isccan_implies in ca1; repndors; exrepnd; subst.

    exists bterms.

    dup h as ca.
    eapply cast_capprox_value2 in ca;[|exact cp].
    assert (c0 = c) as e.
    { exrepnd.
      allapply @reduces_in_atmost_k_steps_implies_reduces_to.
      eapply reduces_to_eq_val_like in ca0;
        [|exact ca2|eauto 2 with slow|eauto 2 with slow].
      ginv; auto. }
    subst.
    clear ca.
    unfold computes_to_value.
    applydup @reduces_atmost_preserves_program in ca0; eauto 3 with slow.
    dands; eauto 3 with slow.

    dup h as ca.
    eapply cast_capprox_value4 in ca;
      [|exact cp
       |unfold computes_to_value;dands;
        [exists x;exact ca0|eauto 3 with slow]
      ].
    repnd.

    unfold lblift; dands; auto.
    introv ltn.

    applydup ca in ltn; exrepnd; clear ca.

    remember (selectbt tl_subterms n) as u1.
    remember (selectbt bterms n) as u2.
    destruct u1 as [l1 u1].
    destruct u2 as [l2 u2].

    assert (length l1 = length l2) as el.
    { spcast.
      unfold blift in ltn0; exrepnd.
      allapply @alpha_eq_bterm_implies_eq_length; lia. }

    pose proof (fresh_vars (length l1) (l1 ++ l2 ++ all_vars u1 ++ all_vars u2)) as fvs; exrepnd.
    exists lvn (lsubst u1 (var_ren l1 lvn)) (lsubst u2 (var_ren l2 lvn)).
    dands;
      [|apply btchange_alpha_aux; auto;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow
       |apply btchange_alpha_aux; auto; try lia;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow];[].

    assert (Cast (blift (olift (approx_aux lib bot2 \2/ bot2))
                        (bterm lvn (lsubst u1 (var_ren l1 lvn)))
                        (bterm lvn (lsubst u2 (var_ren l2 lvn))))) as cb.
    { spcast.
      pose proof (respects_blift_alphabt (olift (approx_aux lib bot2 \2/ bot2))) as resp.
      unfold respects2 in resp; repnd.
      apply (resp _ (bterm l2 u2)).
      { apply btchange_alpha_aux; auto; try lia;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow. }
      apply (resp0 (bterm l1 u1)).
      { apply btchange_alpha_aux; auto; try lia;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow. }
      auto. }
    clear ltn0.

    unfold computes_to_value in cp; repnd.
    allrw @isvalue_iff; repnd.
    allrw @isprogram_ot_iff; repnd.
    pose proof (cp (bterm l1 u1)) as h1.
    autodimp h1 hyp.
    { rw Hequ1; apply selectbt_in; auto. }
    pose proof (ca1 (bterm l2 u2)) as h2.
    autodimp h2 hyp.
    { rw Hequ2; apply selectbt_in; auto; try lia. }
    allrw <- @isprog_vars_iff_isprogram_bt.
    dup h1 as q1; rw @isprog_vars_eq in q1; repnd.
    dup h2 as q2; rw @isprog_vars_eq in q2; repnd.

    unfold olift.
    dands.
    {apply @lsubst_wf_iff_vars; auto. }
    {apply @lsubst_wf_iff_vars; auto. }
    introv ws isp1 isp2.
    left.
    apply CIH; eauto 3 with slow;[].
    exrepnd; spcast.

    pose proof (respects_alpha_olift_l (approx_aux lib bot2 \2/ bot2)) as rl.
    autodimp rl hyp.
    { apply respects_alpha_l_approx_aux_bot2_or_bot2. }

    pose proof (respects_alpha_olift_r (approx_aux lib bot2 \2/ bot2)) as rr.
    autodimp rr hyp.
    { apply respects_alpha_r_approx_aux_bot2_or_bot2. }

    apply blift_selen_triv in cb;
      [|split;
         [apply respects_alpha_l_approx_aux_bot2_or_bot2
         |apply respects_alpha_r_approx_aux_bot2_or_bot2
         ]
      ].

    unfold olift in cb; repnd.
    pose proof (cb sub) as q.
    repeat (autodimp q hyp).
    repndors; tcsp; try (complete (unfold bot2 in q; sp)).

  - introv cp.
    dup h as ca.
    eapply cast_capprox_exc in ca;[|exact cp].
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in ca; auto;
    [|introv;apply dec_ex_reduces_in_atmost_k_steps_exc_prop2].

    exrepnd.
    apply ex_reduces_in_atmost_k_steps_exc in ca0; exrepnd.
    exists n e0.
    applydup @reduces_to_preserves_program in cp; eauto 3 with slow.
    applydup @reduces_atmost_preserves_program in ca0; eauto 3 with slow.
    allrw @isprogram_exception_iff; repnd.
    dands; auto.

    { exists x; auto. }

    { left.
      apply CIH; eauto 3 with slow.
      spcast.
      inversion h as [cl].
      unfold close_comput in cl; repnd.
      apply cl3 in cp; exrepnd.
      allapply @reduces_in_atmost_k_steps_implies_reduces_to.
      eapply reduces_to_eq_val_like in ca0;
        [|exact cp2|eauto 2 with slow|eauto 2 with slow].
      ginv.
      clear cp3; repndors; try (complete (unfold bot2 in cp4; sp)). }

    { left.
      apply CIH; eauto 3 with slow.
      spcast.
      inversion h as [cl].
      unfold close_comput in cl; repnd.
      apply cl3 in cp; exrepnd.
      allapply @reduces_in_atmost_k_steps_implies_reduces_to.
      eapply reduces_to_eq_val_like in ca0;
        [|exact cp2|eauto 2 with slow|eauto 2 with slow].
      ginv.
      clear cp4; repndors; try (complete (unfold bot2 in cp3; sp)). }
Qed.

Lemma cequiv_stable {o} :
  forall lib (a b : @CTerm o), ccequivc lib a b -> cequivc lib a b.
Proof.
  introv h.
  apply cequivc_iff_approxc.
  dands; apply approx_stable; spcast;
  rw @cequivc_iff_approxc in h; sp.
Qed.

Lemma cast_hasvalue {o} :
  forall lib (a : @NTerm o),
    Cast (hasvalue lib a)
    -> {k : nat
        , {u : NTerm
        , reduces_in_atmost_k_steps lib a u k
        # isprog u
        # iscan u}}.
Proof.
  introv comp; spcast.
  unfold hasvalue, computes_to_value, reduces_to in comp; exrepnd.
  exists k t'; dands; eauto 2 with slow.
  apply compute_max_steps_eauto2 in comp0; eauto 3 with slow.
Qed.

Lemma cast_hasvalue2 {o} :
  forall lib (a : @NTerm o),
    Cast (hasvalue lib a)
    -> {k : nat
        , {u : NTerm
        , reduces_in_atmost_k_steps lib a u k
        # iscan u}}.
Proof.
  introv comp; spcast.
  unfold hasvalue, computes_to_value, reduces_to in comp; exrepnd.
  exists k t'; dands; eauto 2 with slow.
Qed.

(*
Lemma dec_ex_reduces_in_atmost_k_steps_isprog_iscan {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm & reduces_in_atmost_k_steps lib t v k # isprog v # iscan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps lib k t) as [d|d].
  - exrepnd.
    destruct (dec_iscan v) as [p|p].
    + destruct (decidable_isprog v) as [q|q].
      * left; exists v; sp.
      * right; intro h; exrepnd.
        eapply reduces_in_atmost_k_steps_eq in d0;[|exact h1]; subst; sp.
    + right; intro h; exrepnd.
      eapply reduces_in_atmost_k_steps_eq in d0;[|exact h1]; subst; sp.
  - right; introv h; destruct d; exrepnd.
    exists v; auto.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_isprog_iscan_prop {o} :
  forall lib k (t : @NTerm o),
    decidable {v : NTerm , reduces_in_atmost_k_steps lib t v k # isprog v # iscan v}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_isprog_iscan lib k t) as [d|d].
  - left; exrepnd; exists v; sp.
  - right; intro h; exrepnd; destruct d; exists v; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_isprog_iscan_prop2 {o} :
  forall lib k (t : @NTerm o),
    {{v : NTerm , reduces_in_atmost_k_steps lib t v k # isprog v # iscan v}}
    + {!{v : NTerm , reduces_in_atmost_k_steps lib t v k # isprog v # iscan v}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_isprog_iscan_prop lib k t) as [d|d]; sp.
Qed.

Lemma ex_reduces_in_atmost_k_steps_isprog_iscan {o} :
  forall lib (t : @NTerm o) k,
    {u : NTerm , reduces_in_atmost_k_steps lib t u k # isprog u # iscan u}
    -> {u : NTerm & reduces_in_atmost_k_steps lib t u k # isprog u # iscan u}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps_isprog_iscan lib k t) as [d|d].
  - exrepnd.
    exists v; auto.
  - provefalse; exrepnd; destruct d.
    exists u; auto.
Qed.
 *)

Lemma ex_reduces_in_atmost_k_steps_iscan {o} :
  forall lib (t : @NTerm o) k,
    {u : NTerm , reduces_in_atmost_k_steps lib t u k # iscan u}
    -> {u : NTerm & reduces_in_atmost_k_steps lib t u k # iscan u}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps_iscan lib k t) as [d|d].
  - exrepnd.
    exists v; auto.
  - provefalse; exrepnd; destruct d.
    exists u; auto.
Qed.

Lemma hasvaluec_stable {o} :
  forall lib (a : @CTerm o), chaltsc lib a -> hasvaluec lib a.
Proof.
  introv.
  destruct_cterms.
  unfold chaltsc, hasvaluec; simpl.
  intro h.
  apply cast_hasvalue2 in h.
  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in h; auto;
  [|introv; apply dec_ex_reduces_in_atmost_k_steps_iscan_prop2].
  exrepnd.
  apply ex_reduces_in_atmost_k_steps_iscan in h0; exrepnd.
  exists u.
  unfold computes_to_value; dands; auto.
  { exists x0; auto. }
  { apply isvalue_iff; dands; eauto 3 with slow. }
Qed.
