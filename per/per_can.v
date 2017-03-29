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


Require Export Coq.Logic.ConstructiveEpsilon.

Require Export cequiv_bind.
Require Export computation_dec1.
(*Require Export computation_dec.*)
Require Export sequents_tacs.
Require Export per_props_cequiv.
Require Export per_props_uni.


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

Lemma cast_capprox_seq {o} :
  forall lib (a b : @NTerm o) f,
    Cast (approx lib a b)
    -> computes_to_seq lib a f
    -> {k : nat
        , {f' : ntseq
        , reduces_in_atmost_k_steps lib b (sterm f') k }}.
Proof.
  introv apr comp; spcast.
  inversion apr as [cc].
  unfold close_comput in cc; repnd.
  apply cc4 in comp; exrepnd.
  unfold computes_to_seq, reduces_to in comp1; exrepnd.
  exists k f'; dands; auto.
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
  - destruct n as [v|f|op bs].
    + right.
      intro r; exrepnd.
      rw r1 in Heqc; ginv.
    + right; introv r; exrepnd.
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
  destruct t as [v|f|op bs]; simpl; tcsp; try (complete (right; sp)).
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

Lemma dec_ex_reduces_in_atmost_k_steps_seq {o} :
  forall lib k (t : @NTerm o),
    decidable {f : ntseq & reduces_in_atmost_k_steps lib t (sterm f) k}.
Proof.
  introv.
  remember (compute_at_most_k_steps lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct n as [v|f|op bs].
    + right.
      intro r; exrepnd.
      rw r0 in Heqc; ginv.
    + left.
      exists f; auto.
    + right.
      intro r; exrepnd.
      rw r0 in Heqc; ginv.
  - right; intro r; exrepnd; rw r0 in Heqc; ginv.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_seq_prop {o} :
  forall lib k (t : @NTerm o),
    decidable {f : ntseq , reduces_in_atmost_k_steps lib t (sterm f) k}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_seq lib k t) as [d|d].
  - left; exrepnd; exists f; sp.
  - right; intro h; exrepnd; destruct d; exists f; sp.
Qed.

Lemma dec_ex_reduces_in_atmost_k_steps_seq_prop2 {o} :
  forall lib k (t : @NTerm o),
    {{f : ntseq , reduces_in_atmost_k_steps lib t (sterm f) k}}
    + {!{f : ntseq , reduces_in_atmost_k_steps lib t (sterm f) k}}.
Proof.
  introv.
  destruct (dec_ex_reduces_in_atmost_k_steps_seq_prop lib k t) as [d|d]; sp.
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

Lemma ex_reduces_in_atmost_k_steps_seq {o} :
  forall lib (t : @NTerm o) k,
    {f : ntseq , reduces_in_atmost_k_steps lib t (sterm f) k}
    -> {f : ntseq & reduces_in_atmost_k_steps lib t (sterm f) k}.
Proof.
  introv comp.
  destruct (dec_ex_reduces_in_atmost_k_steps_seq lib k t) as [d|d].
  - exrepnd.
    exists f; auto.
  - provefalse; exrepnd; destruct d.
    exists f; auto.
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
  destruct t as [v|f|op bs]; try (complete (inversion isc)).
  destruct op; try (complete (inversion isc)).
  exists c bs; sp.
Qed.

Lemma alpha_stable {o} :
  forall (a b : @NTerm o), Cast (alpha_eq a b) -> alpha_eq a b.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv ca.

  - Case "vterm".
    destruct b as [v2|f2|op2 bs2];
      try (complete (provefalse; spcast; inversion ca; subst; tcsp)).

    destruct (deq_nvar v v2); subst; auto.
    provefalse; spcast; inversion ca; subst; tcsp.

  - Case "sterm".
    destruct b as [v2|f2|op2 bs2];
      try (complete (provefalse; spcast; inversion ca; subst; tcsp)).
    constructor; introv.
    apply ind; spcast.
    inversion ca; auto.

  - Case "oterm".
    destruct b as [v2|f2|op2 bs2];
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
      allapply @alpha_eq_bterm_implies_eq_length; omega. }

    pose proof (fresh_vars (length l1) (l1 ++ l2 ++ all_vars u1 ++ all_vars u2)) as fvs; exrepnd.
    exists lvn (lsubst u1 (var_ren l1 lvn)) (lsubst u2 (var_ren l2 lvn)).
    dands;
      [|apply btchange_alpha_aux; auto;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow
       |apply btchange_alpha_aux; auto; try omega;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow];[].

    assert (Cast (blift (olift (approx_aux lib bot2 \2/ bot2))
                        (bterm lvn (lsubst u1 (var_ren l1 lvn)))
                        (bterm lvn (lsubst u2 (var_ren l2 lvn))))) as cb.
    { spcast.
      pose proof (respects_blift_alphabt (olift (approx_aux lib bot2 \2/ bot2))) as resp.
      unfold respects2 in resp; repnd.
      apply (resp _ (bterm l2 u2)).
      { apply btchange_alpha_aux; auto; try omega;
        allrw disjoint_app_r; allrw disjoint_app_l;
        repnd; dands; eauto 3 with slow. }
      apply (resp0 (bterm l1 u1)).
      { apply btchange_alpha_aux; auto; try omega;
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
    { rw Hequ2; apply selectbt_in; auto; try omega. }
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

  - introv comp.
    dup h as ca.
    eapply cast_capprox_seq in ca;[|exact comp].
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in ca; auto;
    [|introv;apply dec_ex_reduces_in_atmost_k_steps_seq_prop2].

    exrepnd.
    apply ex_reduces_in_atmost_k_steps_seq in ca0; exrepnd.
    exists f0.
    applydup @reduces_to_preserves_program in comp; eauto 3 with slow.
    applydup @reduces_atmost_preserves_program in ca1; eauto 3 with slow.
    dands; auto.

    { exists x; auto. }

    { introv.
      left.
      apply CIH; eauto 3 with slow.
      spcast.
      inversion h as [cl].
      unfold close_comput in cl; repnd.
      apply cl4 in comp; exrepnd.
      allapply @reduces_in_atmost_k_steps_implies_reduces_to.
      eapply reduces_to_eq_val_like in ca1;
        [|exact comp2|eauto 2 with slow|eauto 2 with slow].
      allunfold @mk_ntseq; ginv; auto.
      pose proof (comp1 n) as q; repndors; tcsp.
      inversion q. }
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

Lemma cequorsq_mkc_halts {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    (hasvaluec lib a <=> hasvaluec lib b).
Proof.
  unfold equorsq; introv; split; introv h.
  - split; introv q; apply hasvaluec_stable; repndors;
     allrw @equality_in_uni_mkc_halts.
     + apply h; spcast; auto.
     + spcast.
       apply cequivc_decomp_halts in h; repnd.
       apply h0; auto.
     + apply h; spcast; auto.
     + spcast.
       apply cequivc_decomp_halts in h; repnd.
       apply h0; auto.
  - left.
    apply equality_in_uni_mkc_halts.
    split; intro q; spcast; apply h; auto.
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

    { introv comp.
      apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv. }
Qed.

Lemma tequality_mkc_isexc {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_isexc a) (mkc_isexc b)
    <=> (raises_exceptionc lib a <=> raises_exceptionc lib b).
Proof.
  introv.
  allrw @mkc_isexc_eq.
  rw @tequality_mkc_approx.
  allrw @isexc_as_raises_exceptionc; sp.
Qed.

Lemma member_isexc_iff {p} :
  forall lib (t : @CTerm p),
    raises_exceptionc lib t
    <=> member lib mkc_axiom (mkc_isexc t).
Proof.
  introv.
  rw @mkc_isexc_eq.
  rw <- @member_approx_iff.
  rw @isexc_as_raises_exceptionc; sp.
Qed.

Lemma raises_exceptionc_stable {o} :
  forall lib (a : @CTerm o), Cast (raises_exceptionc lib a) -> raises_exceptionc lib a.
Proof.
  introv h.
  apply isexc_as_raises_exceptionc; inversion h.
  apply isexc_as_raises_exceptionc; auto.
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
    (raises_exceptionc lib a <=> raises_exceptionc lib b).
Proof.
  introv.
  allrw @mkc_isexc_eq.
  allrw @mkc_approx_equality_in_uni.
  allrw @isexc_as_raises_exceptionc; sp.
Qed.

Lemma cequorsq_mkc_isexc {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_isexc a) (mkc_isexc b) (mkc_uni i)
    <=>
    (raises_exceptionc lib a <=> raises_exceptionc lib b).
Proof.
  unfold equorsq; introv; split; introv h.
  - split; introv q; apply raises_exceptionc_stable; repndors;
    allapply @equality_in_uni;
    allrw @tequality_mkc_isexc; spcast;
    try (complete (apply h; auto)).
    + rw @cequivc_decomp_isexc in h.
      apply raises_exceptionc_preserves_cequivc in h; auto.
    + rw @cequivc_decomp_isexc in h.
      apply cequivc_sym in h.
      apply raises_exceptionc_preserves_cequivc in h; auto.
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

    + introv comp.
      apply reduces_to_if_isvalue_like in comp; ginv; eauto 3 with slow.
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

Lemma tequality_mkc_halts_like {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_halts_like a) (mkc_halts_like b)
    <=> (hasvalue_likec lib a <=> hasvalue_likec lib b).
Proof.
  introv.
  allrw @mkc_halts_like_eq.
  rw @tequality_mkc_approx.
  allrw @cast_halts_likec_as_hasvalue_likec; sp.
Qed.

Lemma member_halts_like_iff {p} :
  forall lib (t : @CTerm p),
    member lib mkc_axiom (mkc_halts_like t)
    <=> hasvalue_likec lib t.
Proof.
  introv.
  rw @mkc_halts_like_eq.
  rw <- @member_approx_iff.
  rw @cast_halts_likec_as_hasvalue_likec; sp.
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

    + introv comp; repnd.
      apply computes_to_seq_implies_computes_to_value in comp;
        [|apply isprogram_cbv_iff2;dands; eauto 3 with slow].
      apply computes_to_value_hasvalue in comp.
      apply if_hasvalue_cbv in comp; eauto 3 with slow.
      exrepnd.
      applydup @preserve_program in comp1; auto.
      rw @subst_trivial in comp0; eauto 3 with slow.
      unfold hasvalue in comp0; exrepnd.
      apply computes_to_value_exception in comp3; sp.
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
    (hasvalue_likec lib a <=> hasvalue_likec lib b).
Proof.
  introv.
  allrw @mkc_halts_like_eq.
  allrw @mkc_approx_equality_in_uni.
  allrw @cast_halts_likec_as_hasvalue_likec.
  allrw @isexc_as_raises_exceptionc; sp.
Qed.

Lemma hasvalue_likec_stable {o} :
  forall lib (a : @CTerm o), Cast (hasvalue_likec lib a) -> hasvalue_likec lib a.
Proof.
  introv h.
  rw <- @member_halts_like_iff.
  spcast.
  apply member_halts_like_iff; auto.
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
    (hasvalue_likec lib a <=> hasvalue_likec lib b).
Proof.
  unfold equorsq; introv; split; introv h.
  - split; introv q; apply hasvalue_likec_stable; repndors;
    allapply @equality_in_uni;
    allrw @tequality_mkc_halts_like; spcast;
    try (complete (apply h; auto)).
    + eapply cequivc_halts_like_preserves_hasvalue_likec; eauto.
    + apply cequivc_sym in h.
      eapply cequivc_halts_like_preserves_hasvalue_likec; eauto.
  - left.
    apply equality_in_uni_mkc_halts_like; auto.
Qed.
