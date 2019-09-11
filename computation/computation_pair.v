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

Require Export computation4.

Lemma isprog_pair_iff {p} :
  forall a b : @NTerm p, isprog (mk_pair a b) <=> (isprog a # isprog b).
Proof.
  introv; split; intro k.

  - allrw @isprog_eq.
    destruct k as [c w].
    inversion w as [| | o lnt j e ]; subst.
    generalize (j (nobnd a)) (j (nobnd b)); intros i1 i2; allsimpl.
    repeat (autodimp i1 hyp).
    repeat (autodimp i2 hyp).
    unfold isprogram.
    inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
    inversion i1; inversion i2; subst.
    rw app_eq_nil_iff in pp; sp; subst; sp.

  - apply isprog_pair; sp.
Qed.

Lemma isvalue_pair {p} :
  forall (a b : @NTerm p), isprogram a -> isprogram b -> isvalue (mk_pair a b).
Proof.
 introv ispa ispb.
 constructor; simpl; auto.
 apply isprogram_pair; auto.
Qed.
Hint Resolve isvalue_pair : slow.

Lemma compute_step_spread_ncan {o} :
  forall lib n l x y b,
    @compute_step o lib (mk_spread (oterm (NCan n) l) x y b)
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_spread p x y b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma hasvaluec_mkc_spread {q} :
  forall lib p x y t,
    hasvaluec lib (mkc_spread p x y t)
    -> {a, b : @CTerm q $ computes_to_valc lib p (mkc_pair a b)}.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x0 into p.
  rename x1 into t.
  unfold computes_to_valc; simpl.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  revert dependent p.
  induction k; introv isp comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion iv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct p as [v|f|op bs].

    + inversion comp1.

    + csunf comp1; allsimpl; ginv.

    + destruct op.

      * remember (compute_step_spread
                    c
                    (oterm (NCan NSpread) [nobnd (oterm (@Can q c) bs), bterm [x, y] t])
                    bs
                  [bterm [x, y] t]).
        destruct c0.

        { symmetry in Heqc0.
          apply compute_step_spread_success in Heqc0; exrepnd; subst; cpx.
          rw @isprog_pair_iff in isp; repnd.
          exists (mk_ct a isp0) (mk_ct b isp); simpl.
          apply computes_to_value_isvalue_refl; sp.
          apply isvalue_pair; rw @isprogram_eq; sp. }

        { csunf comp1; simpl in comp1.
          apply compute_step_spread_success in comp1; exrepnd; subst; cpx.
          simpl in Heqc0; inversion Heqc0. }

      * rw @compute_step_spread_ncan in comp1.
        remember (compute_step lib (oterm (NCan n) bs)).
        destruct c.

        symmetry in Heqc.
        allrw @isprog_eq.
        applydup @preserve_compute_step in Heqc; auto.
        inversion comp1; subst; GC.
        apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
        exists a b.
        apply computes_to_value_step with (t2 := n0); auto.
        inversion comp1.

      * simpl in comp1.
        unfold compute_step_catch in comp1; inversion comp1; subst; GC.
        apply reduces_atmost_exc in comp0; subst.
        inversion iv; allsimpl; tcsp.

      * csunf comp1; simpl in comp1; unfold on_success in comp1; csunf comp1; allsimpl.
        remember (compute_step_lib lib o bs) as csl.
        destruct csl; inversion comp1; subst; GC.
        symmetry in Heqcsl.
        rw @isprog_eq in isp.
        applydup @isprogram_compute_step_lib in Heqcsl; auto.
        rw <- @isprog_eq in Heqcsl0.
        apply IHk in comp0; auto; exrepnd.
        exists a b.
        apply computes_to_value_step with (t2 := n); auto.
Qed.

(* !!MOVE *)
Lemma if_computes_to_exception_spread0 {o} :
  forall lib n (t : @NTerm o) x y u e,
    isprogram t
    -> computes_to_exception lib n (mk_spread t x y u) e
    -> computes_to_exception lib n t e
       [+] {a : NTerm
            & {b : NTerm
            & computes_to_value lib t (mk_pair a b)
            # computes_to_exception lib n (lsubst u [(x,a),(y,b)]) e}}.
Proof.
  unfold computes_to_exception, reduces_to.
  introv ispt re; exrepnd.
  revert dependent t.
  revert x y u.
  induction k; introv ispt r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; allsimpl.
    destruct t as [v|f|op bs]; try (complete (inversion r1)).
    dopid op as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".
      apply compute_step_spread_success in r1; exrepnd; subst; ginv.
      right.
      exists a b; dands; eauto 3 with slow.
      allrw <- @isprogram_pair_iff; repnd.
      apply computes_to_value_isvalue_refl; eauto 3 with slow.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right.
        exists a b; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }

    + Case "Exc".
      ginv.
      left.
      exists k; auto.

    + Case "Abs".
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs bs) as c;
        destruct c; allsimpl; symmetry in Heqc; ginv.

      applydup @isprogram_compute_step_lib in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right.
        exists a b; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }
Qed.

(* !!MOVE *)
Lemma if_raises_exception_spread0 {o} :
  forall lib (t : @NTerm o) x y u,
    isprogram t
    -> raises_exception lib (mk_spread t x y u)
    -> raises_exception lib t
       [+] {a : NTerm
            & {b : NTerm
            & computes_to_value lib t (mk_pair a b)
            # raises_exception lib (lsubst u [(x,a),(y,b)]) }}.
Proof.
  introv isp re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exception_spread0 lib a t x y u e isp re1) as h.
  repndors; exrepnd.
  - left; exists a e; auto.
  - right.
    exists a0 b; dands; auto.
    exists a e; auto.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_spread0 {o} :
  forall lib (t : @CTerm o) x y u,
    raises_exceptionc lib (mkc_spread t x y u)
    -> raises_exceptionc lib t
       [+] {a : CTerm
            & {b : CTerm
            & computes_to_valc lib t (mkc_pair a b)
            # raises_exceptionc lib (lsubstc2 x a y b u) }}.
Proof.
  introv re.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_spread0 lib x0 x y x1) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  repndors; exrepnd; tcsp.
  right.
  applydup @preserve_program in h0; eauto 3 with slow.
  allrw <- @isprogram_pair_iff; repnd.
  exists (mk_cterm a h3) (mk_cterm b h2); simpl.
  dands; auto.
Qed.
