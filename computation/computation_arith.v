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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export computation8.


Ltac fold_mk_arithop :=
  unfold mk_add, mk_sub, mk_mul, mk_div, mk_rem in *;
  repeat
  match goal with
  | [ |- context[oterm (NCan (NArithOp ?op)) [nobnd ?m, nobnd ?n] ] ]
         => fold (mk_arithop op m n)
  | [ H: context[oterm (NCan (NArithOp ?op)) [nobnd ?m, nobnd ?n] ] |- _ ] 
        => fold (mk_arithop op m n) in H
  end.


Lemma isprog_arith_iff {p} :
  forall (a b : @NTerm p) (op: ArithOp), isprog (mk_arithop op a b) <=> (isprog a) # (isprog b).
Proof.
  introv; split; intro k;
  allrw @isprog_eq; allrw (@isprogram_arithop_iff p); simpl.
  -
  destruct k as [c w].
  destruct w as [d w]; sp;
  inversion w0; auto.
  - exists a b; auto.  
Qed.


Lemma compute_step_arithop_ncan {o} :
  forall lib n l op b,
    @compute_step o lib (mk_arithop op (oterm (NCan n) l) b )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_arithop op p b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_arithop_abs {o} :
  forall lib n l op b,
    @compute_step o lib (mk_arithop op (oterm (Abs n) l) b )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_arithop op p b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_arithop_exc {o} :
  forall lib l op b,
    @compute_step o lib (mk_arithop op (oterm Exc l) b )
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_minus_ncan {o} :
  forall lib n l,
    @compute_step o lib (mk_minus (oterm (NCan n) l) )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_minus p )
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_minus_abs {o} :
  forall lib n l,
    @compute_step o lib (mk_minus (oterm (Abs n) l) )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_minus p )
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_minus_exc {o} :
  forall lib l,
    @compute_step o lib (mk_minus (oterm Exc l))
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_minus_can {o} :
  forall lib c l, 
     @compute_step o lib (mk_minus (oterm (Can c) l) ) =
      compute_step_minus c (oterm (NCan NMinus) [nobnd (oterm (Can c) l)]) l [].
Proof. introv; unfold mk_minus; csunf; simpl; sp. 
Qed.

Lemma compute_step_minus_can_success {o} :
  forall lib c l u, 
     @compute_step o lib (mk_minus (oterm (Can c) l) ) = csuccess u ->
      { z:Z $  u = mk_integer (0-z) 
             # l = []  
             # c = Nint z}. 
Proof. introv cs. csunf cs; allsimpl.
       destruct l; destruct c; 
       unfold compute_step_minus in cs; allsimpl; inversion cs; subst. exists z; auto.
Qed.


Lemma compute_step_arithop_can_can {o} :
  forall lib c1 c2 l1 l2 op , ca_wf c1 l1 = true ->
     @compute_step o lib (mk_arithop op (oterm (Can c1) l1) (oterm (Can c2) l2) ) =
     compute_step_arith op c1 c2 l1 l2 []
         (oterm (NCan (NArithOp op))
            [nobnd (oterm (Can c1) l1), nobnd (oterm (Can c2) l2)]).
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
      unfold ca. unfold ca_aux. remember (ca_wf c1 l1); destruct b; [inversion H | sp].
      sp.
Qed.

Lemma compute_step_arithop_can_can_success {o} :
  forall lib c c2 l1 l2 op u,
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm (Can c2) l2) )
    = csuccess u ->
 { z:Z $ { z0: Z $ u =  oterm (Can (Nint (get_arith_op op z z0))) []
             # l1 = []  # l2 = [] 
             # c = Nint z # c2 = Nint z0
 }}.
Proof. introv cs. csunf cs; allsimpl. dcwf H; allsimpl.
       apply compute_step_arithop_success_can_can in cs. exrepnd; subst.
       allapply @get_param_from_cop_pki; subst.
       eexists. eexists. dands; eauto; auto.
Qed.



Lemma compute_step_arithop_can_ncan {o} :
  forall lib c n l1 l2 op , ca_wf c l1 = true ->
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm (NCan n) l2) )
    = match compute_step lib (oterm (NCan n) l2) with
        | csuccess p => csuccess (mk_arithop op (oterm (Can c)  l1) p)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
      unfold ca. unfold ca_aux. remember (ca_wf c l1); destruct b; [inversion H | sp].
      sp.
Qed.

Lemma compute_step_arithop_can_ncan_success {o} :
  forall lib c n l1 l2 op u,
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm (NCan n) l2) )
    = csuccess u ->
    { p: NTerm $ u = mk_arithop op (oterm (Can c) l1) p
                # compute_step lib (oterm (NCan n) l2) = csuccess p
    }.
Proof. introv; remember (ca_wf c l1); destruct b.
      - rw (@compute_step_arithop_can_ncan o); auto.
        remember (compute_step lib (oterm (NCan n) l2)) as xxx; destruct xxx; intro; inversion H.
        inversion H. exists n0. auto.
      - unfold mk_arithop. csunf. simpl. unfold ca. remember (ca_wf c l1) as xxx; destruct xxx.
        + inversion Heqb.
        + intro. inversion H.
Qed.


Lemma compute_step_arithop_can_abs {o} :
  forall lib c n l1 l2 op , ca_wf c l1 = true ->
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm (Abs n) l2) )
    = match compute_step lib (oterm (Abs n) l2) with
        | csuccess p => csuccess (mk_arithop op (oterm (Can c)  l1) p)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
      unfold ca. unfold ca_aux. remember (ca_wf c l1); destruct b; [inversion H | sp].
      sp.
Qed.

Lemma compute_step_arithop_can_abs_success {o} :
  forall lib c n l1 l2 op u,
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm (Abs n) l2) )
    = csuccess u ->
    { p: NTerm $ u = mk_arithop op (oterm (Can c) l1) p
                # compute_step lib (oterm (Abs n) l2) = csuccess p
    }.
Proof. introv; remember (ca_wf c l1); destruct b.
      - rw (@compute_step_arithop_can_abs o); auto.
        remember (compute_step lib (oterm (Abs n) l2)) as xxx; destruct xxx; intro; inversion H.
        inversion H. exists n0. auto.
      - unfold mk_arithop. csunf. simpl. unfold ca. remember (ca_wf c l1) as xxx; destruct xxx.
        + inversion Heqb.
        + intro. inversion H.
Qed.

Lemma compute_step_arithop_can_vterm {o} :
  forall lib c v l1 op , ca_wf c l1 = true ->
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (vterm v) )
    =  cfailure compute_step_error_not_closed
         (oterm (NCan (NArithOp op))
            [nobnd (oterm (Can c) l1), nobnd (vterm v)]).
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
      unfold ca. unfold ca_aux. remember (ca_wf c l1); destruct b; [inversion H | sp].
      sp.
Qed.


Lemma compute_step_arithop_can_vterm_success {o} :
  forall lib c v l1 op u , 
    !@compute_step o lib (mk_arithop op (oterm (Can c) l1) (vterm v) )
    = csuccess u .
Proof. introv. remember (ca_wf c l1); destruct b.
      - rw (@compute_step_arithop_can_vterm o); auto. intro.
        inversion H.
      - unfold mk_arithop. csunf. simpl. unfold ca. remember (ca_wf c l1) as xxx; destruct xxx.
        + inversion Heqb.
        + intro. inversion H.
Qed. 


Lemma compute_step_arithop_can_exc {o} :
  forall lib c v l1 op , ca_wf c l1 = true ->
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm Exc v) )
    = csuccess (oterm Exc v).
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
      unfold ca. unfold ca_aux. remember (ca_wf c l1); destruct b; [inversion H | sp].
      sp.
Qed.


Lemma compute_step_arithop_can_exc_success {o} :
  forall lib c v l1 op u , 
    @compute_step o lib (mk_arithop op (oterm (Can c) l1) (oterm Exc v) )
    = csuccess u -> {z: Z $  u = (oterm Exc v) # l1 = [] #  c = Nint z} .
Proof. introv cs; csunf cs; allsimpl; dcwf H; allsimpl; ginv; subst.
       unfold ca_wf_def in HeqH; exrepnd; subst; eexists; dands; eauto.
Qed.


Lemma hasvaluec_mkc_arithop {q} :
  forall lib op t1 t2,
    hasvaluec lib (mkc_arithop op t1 t2)
    -> {n1: Z $
       { n2 : Z $
          computes_to_valc lib t1 (mkc_integer n1)
           #
          computes_to_valc lib t2 (@mkc_integer q n2)
       }}.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x0 into a.
  rename x into b.
  unfold computes_to_valc; simpl.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  revert dependent a.
  revert dependent b.
  revert dependent op.
  induction k; introv isp isq comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion iv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct a as [v|op1 bs].

    + inversion comp1.

    + dopid op1 as [can | ncan | ex | abs] Case.

      * Case "Can".
        destruct b as [v|op1 bs1].

        { apply (@compute_step_arithop_can_vterm_success q) in comp1. inversion comp1. }

        { dopid op1 as [bcan | bncan | bex | babs] BCase.

          - (* BCase = "Can" *)
            apply compute_step_arithop_can_can_success in comp1; sp; subst.
            exists z z0. split; apply computes_to_value_isvalue_refl; eauto 3 with slow.

          - (* BCase = "NCan" *)
            apply (@compute_step_arithop_can_ncan_success q) in comp1. sp. subst.
            apply IHk in comp0; auto. sp.
            + exists n1 n2; split; auto.
              apply (@computes_to_value_step q lib (oterm (NCan bncan) bs1) p (mk_integer n2));auto.
            + apply (@isprogram_eq q). apply (@preserve_compute_step q lib (oterm (NCan bncan) bs1) p);
              auto; apply (@isprogram_eq q); auto.

          - (* BCase = "Exc" *)
            apply (@compute_step_arithop_can_exc_success q) in comp1; exrepnd; subst.
            apply reduces_in_atmost_k_steps_exception in comp0. subst.
            inversion iv; allsimpl; tcsp.

          - (* BCase = "Abs" *)
            apply (@compute_step_arithop_can_abs_success q) in comp1. sp. subst.
            apply IHk in comp0; auto. sp.
            + exists n1 n2; split; auto.
              apply (@computes_to_value_step q lib (oterm (Abs babs) bs1) p (mk_integer n2));auto.
            + apply (isprogram_eq). eapply preserve_compute_step; eauto 3 with slow.
        }

      * Case "NCan".

        rw @compute_step_arithop_ncan in comp1.
        remember (compute_step lib (oterm (NCan ncan) bs)).
        destruct c; ginv.

        symmetry in Heqc.
        allrw @isprog_eq.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
        exists n1 n2; split; auto.
        eapply computes_to_value_step; eauto.

      * Case "Exc".
        simpl in comp1. csunf comp1; allsimpl; ginv.
        apply reduces_atmost_exc in comp0; subst.
        inversion iv; allsimpl; tcsp.

      * Case "Abs".
        csunf comp1; simpl in comp1; unfold on_success in comp1; csunf comp1; allsimpl.
        remember (compute_step_lib lib abs bs) as csl.
        destruct csl; inversion comp1; subst.  GC.
        symmetry in Heqcsl.
        rw @isprog_eq in isq.
        applydup @isprogram_compute_step_lib in Heqcsl; auto.
        rw <- @isprog_eq in Heqcsl0.
        apply IHk in comp0; auto; exrepnd.
        exists n1 n2; split; auto. eapply computes_to_value_step; eauto.
Qed.


Lemma if_computes_to_exc_arithop {q} :
  forall lib n op (t1 : @NTerm q) t2 e,
    isprogram t1
   -> isprogram t2
    -> computes_to_exception lib n (mk_arithop op t1 t2) e
    -> computes_to_exception lib n t1 e
       [+] {z : Z
            & computes_to_value lib t1 (mk_integer z)
            # computes_to_exception lib n t2 e}.
Proof.
 unfold computes_to_exception, reduces_to.
  introv ispt1 ispt2 re; exrepnd.
  revert dependent t2.
  revert dependent t1.
  induction k; introv ispt1 ispt2 r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    destruct t1 as [z|op1 bs]; try (complete (inversion r1));[].

    dopid op1 as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".

      destruct t2 as [v|op1 bs1].

      { apply (@compute_step_arithop_can_vterm_success q) in r1. inversion r1. }

      { dopid op1 as [bcan | bncan | bex | babs] SCase.

        - SCase "Can".
          apply (@compute_step_arithop_can_can_success q) in r1; sp; subst.
          apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow. ginv.

        - SCase "NCan".
          apply (@compute_step_arithop_can_ncan_success q) in r1. sp. subst.
          apply IHk in r0; auto. sp.
          + left. exists ( k0); auto.
          + right. exists z. split; auto. exists (S k0).
            rw @reduces_in_atmost_k_steps_S. exists p. auto.
          + apply (@preserve_compute_step q lib (oterm (NCan bncan) bs1) p);
            auto; apply (@isprogram_eq q); auto.

        - SCase "Exc".
          apply (@compute_step_arithop_can_exc_success q) in r1; exrepnd; subst.
          right. exists z; dands; eauto 3 with slow.

        - SCase "Abs".
          apply (@compute_step_arithop_can_abs_success q) in r1. sp. subst.
          apply IHk in r0; auto. sp.
          + left. exists ( k0); auto.
          + right. exists z. split; auto. exists (S k0).
            rw @reduces_in_atmost_k_steps_S. exists p. auto.
          + apply (@preserve_compute_step q lib (oterm (Abs babs) bs1) p);
            auto; apply (@isprogram_eq q); auto.
      }

    + Case "NCan".
      csunf r1; allsimpl.
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right.
        exists z; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }

    + Case "Exc".
      csunf r1; allsimpl.
      ginv.
      left.
      exists k; auto.

    + Case "Abs".
      csunf r1; allsimpl.
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
        exists z; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }
Qed.

(* !!MOVE *)
Lemma if_raises_exception_arithop {o} :
  forall lib op (t1 t2: @NTerm o),
    isprogram t1
    -> isprogram t2
    -> raises_exception lib (mk_arithop op t1 t2)
    -> raises_exception lib t1
       [+] {z : Z
            & computes_to_value lib t1 (mk_integer z)
            # raises_exception lib t2 }.
Proof.
  introv isp1 isp2 re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exc_arithop lib a op t1 t2 e isp1 isp2  re1) as h.
  repndors; exrepnd.
  - left; exists a e; auto.
  - right.
    exists z; dands; auto.
    exists a e; auto.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_arithop {o} :
  forall lib op (t1 t2 : @CTerm o),
    raises_exceptionc lib (mkc_arithop op t1 t2)
    -> raises_exceptionc lib t1
       [+] {z : Z
            & computes_to_valc lib t1 (mkc_integer z)
            # raises_exceptionc lib t2 }.
Proof.
  introv re.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_arithop lib op x0 x ) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed.

Lemma arithop_int_exc_not_int {o} :
  forall lib op i j l k,
    !reduces_in_atmost_k_steps lib
           (mk_arithop op (mk_integer i) (oterm Exc l))
           (@mk_integer o j) k.
Proof.
  intros. destruct k; introv red.
  - rw @reduces_in_atmost_k_steps_0 in red;  inversion red.
  - rw @reduces_in_atmost_k_steps_S in red; exrepnd.
       unfold mk_integer in red1. rw @compute_step_arithop_can_exc in red1; inversion red1; subst.       
       clear red1. revert red0. induction k; introv red.
       + rw @reduces_in_atmost_k_steps_0 in red;  inversion red.
       + rw @reduces_in_atmost_k_steps_S in red; exrepnd.
         inversion red1; subst; auto.
       + constructor.
Qed.

Lemma arithop_exc_not_int {o} :
  forall lib op b j l k,
    !reduces_in_atmost_k_steps lib
           (mk_arithop op (oterm Exc l) b)
           (@mk_integer o j) k.
Proof.
  intros. destruct k; introv red.
  - rw @reduces_in_atmost_k_steps_0 in red;  inversion red.
  - rw @reduces_in_atmost_k_steps_S in red; exrepnd.
       unfold mk_integer in red1. rw @compute_step_arithop_exc in red1; inversion red1; subst.       
       clear red1. revert red0. induction k; introv red.
       + rw @reduces_in_atmost_k_steps_0 in red;  inversion red.
       + rw @reduces_in_atmost_k_steps_S in red; exrepnd.
         inversion red1; subst; auto.
Qed.

Lemma canonical_reduces_to {o} :
   forall lib c l t,
   reduces_to lib (oterm (@Can o c) l) t -> (oterm (Can c) l) = t.
Proof.
  introv r.
  apply reduces_to_if_isvalue_like in r; eauto 3 with slow.
Qed.

Lemma integer_reduces_to {o} :
   forall lib i k,
   reduces_to lib (mk_integer i) (@mk_integer o k) -> i = k.
Proof.
  introv red. unfold mk_integer in red.
  apply canonical_reduces_to in red. ginv. auto.
Qed.

Lemma reduces_to_arithop {o} :
  forall lib op (a b : (@NTerm o)) i j,
   (reduces_to lib a (mk_integer i))->
   (reduces_to lib b (mk_integer j))->
   (reduces_to lib (mk_arithop op a b) (mk_integer (get_arith_op op i j))).
Proof.
  introv ai bj.
  allunfold @reduces_to; exrepnd.

  revert dependent b. revert dependent a. revert k. induction k0; introv red.

  - apply @reduces_in_atmost_k_steps_0 in red; subst.
    induction k. introv red.

    + apply @reduces_in_atmost_k_steps_0 in red; subst.
      exists 1. apply @reduces_in_atmost_k_steps_S.
      exists  (@mk_integer o (get_arith_op op i j)); sp.

    + introv red. apply @reduces_in_atmost_k_steps_S in red; exrepnd.
      apply IHk in red0. exrepnd.

      destruct b as [v|op1 bs].

      { inversion red1. }

      dopid op1 as [can | ncan |ex |abs] Case; simpl.

      * Case "Can". inversion red1; subst. clear red1.
        destruct k0.

        { apply @reduces_in_atmost_k_steps_0 in red2; ginv. }

        { apply @reduces_in_atmost_k_steps_S in red2; exrepnd.
          csunf red1; allsimpl; dcwf h; allsimpl.
          destruct bs; allsimpl; ginv.
          destruct can; allsimpl; ginv; fold_terms.
          apply reduces_in_atmost_k_steps_if_isvalue_like in red0; eauto 3 with slow.
          rw red0.
          exists 1.
          rw @reduces_in_atmost_k_steps_S; auto.
          csunf; simpl; dcwf h; simpl; fold_terms.
          eexists; dands; eauto.
          apply reduces_in_atmost_k_steps_0; auto.
        }

      * Case "NCan".
        exists (S k0); apply @reduces_in_atmost_k_steps_S.
        exists (mk_arithop op (mk_integer i) u); sp; auto.
        unfold mk_integer.
        rw @compute_step_arithop_can_ncan; auto.
        remember ( compute_step lib (oterm (NCan ncan) bs)) as s.
        destruct s; inversion red1; subst; auto.

      * Case "Exc".
        inversion red1; subst.
        apply arithop_int_exc_not_int in red2; inversion red2.

      * Case "Abs".
        exists (S k0); apply @reduces_in_atmost_k_steps_S.
        exists (mk_arithop op (mk_integer i) u); sp; auto.
        unfold mk_integer. rw @compute_step_arithop_can_abs; auto.
        remember ( compute_step lib (oterm (Abs abs) bs)) as s.
        destruct s; inversion red1; subst; auto.

  - (* induction step *)
    apply @reduces_in_atmost_k_steps_S in red; exrepnd.
    introv redb.
    pose proof (IHk0 k u red0 b redb) as hyp; clear IHk0; exrepnd.

    destruct a as [v|op1 bs].

    { inversion red1. }

    dopid op1 as [can | ncan |ex |abs] Case; simpl.

    + Case "Can".
      inversion red1; subst; clear red1. apply reduces_atmost_can in red0.
      remember (oterm (Can can) bs); clear Heqn; subst. exists k1; auto.

    + Case "NCan". exists (S k1); apply @reduces_in_atmost_k_steps_S.
      exists (mk_arithop op u b); sp; auto.
      rw @compute_step_arithop_ncan; auto.
      remember ( compute_step lib (oterm (NCan ncan) bs)) as s.
      destruct s; inversion red1; subst; auto.

    + Case "Exc". inversion red1; subst.
      apply arithop_exc_not_int in hyp0; inversion hyp0.

    + Case "Abs". exists (S k1); apply @reduces_in_atmost_k_steps_S.
      exists (mk_arithop op u b); sp; auto.
      rw @compute_step_arithop_abs; auto.
      remember ( compute_step lib (oterm (Abs abs) bs)) as s.
      destruct s; inversion red1; subst; auto.
Qed.
