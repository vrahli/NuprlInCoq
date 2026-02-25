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


Require Export rules_partial1.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(** printing <=2=> $\Leftarrow\!\!{\scriptstyle{2}}\!\!\Rightarrow$ *)
(** printing $  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing |- $\vdash$ *)

(** *** Typing the Fixpoint Combinator

%\noindent% The fix operator of the Nuprl language is a key
  way to build interesting members of partial types.
  Crary proved several rules (called fixpoint induction rules) that
  allow one to prove equality of terms containing the fix operator
  in a partial type.
  Here is a simple one. Note that the second
  subgoal in the rule cannot be removed. In other words,
  in a powerful dependent type theory like Nuprl, there are
  fairly intuitive dependent types [T] for which we have
  some [f] in [mk_partial T-> mk_partial T], but
  [mk_fix f] is not a member of [mk_partial T].
  See %\cite[Theorem 5.1]{Crary:1998}%.
  Monohood and Admissibility are two predicates on types
  which ensure that this principle holds.
  Monohood implies Admissibility. However, monohood
  is easier to understand.
*)

(**
  Fixpoint principle for Mono types:
<<
   H |- fix(f1) = fix(f2) in partial(T)

     By fixpointPrinciple

     H |- f1 = f2 in partial(T)->partial(T)
     H |- Mono(T)
>>
 *)

Definition rule_fixpoint_principle_mono {o}
           (f1 f2 T : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
        (mk_equality (mk_fix f1) (mk_fix f2) (mk_partial T))))
    [ mk_baresequent H 
        (mk_conclax (mk_equality f1 f2 
            (mk_fun (mk_partial T) (mk_partial T)))),
      mk_baresequent H (mk_conclax (mk_mono T))
    ]
    [].

(** In order to prove the above rule, we first prove some lemmas. 
*)

Lemma fix_approx_hasvalue {o} : forall lib f n,
  @isprogram o f
  -> hasvalue lib (fix_approx n f)
  -> hasvalue lib (mk_fix  f).
Proof.
  introv Hpr.
  apply (fix_approx_ub lib) in Hpr.
  specialize (Hpr n). allsimpl.
  apply hasvalue_approx.
  auto.
Qed.

Lemma fix_approx_hasvalue_context {o} : forall lib f G n,
  @isprogram o f
  -> isprogram G
  -> hasvalue lib (mk_apply G (fix_approx n f))
  -> hasvalue lib (mk_apply G (mk_fix  f)).
Proof.
  introv Hpf HpG Hv.
  apply (fix_approx_ub lib) in Hpf.
  specialize (Hpf n). allsimpl.
  apply (implies_approx_apply lib G G) in Hpf; auto;
  [ |eauto 2 with slow].
  eapply hasvalue_approx; eauto.
Qed.

Lemma fapprox_hasvalue_higher {o} : forall lib f n,
  @isprogram o f
  -> hasvalue lib (fix_approx n f)
  -> forall m, hasvalue lib (fix_approx (m+n) f).
Proof.
  introv Hpr. introv Hv.
  apply (is_approx_chain_fix_aprox lib) in Hpr.
  induction m; auto.
  assert (S m + n = S(m + n)) as Xr by lia.
  rw Xr.
  specialize (Hpr (m+n)). allsimpl.
  eapply hasvalue_approx;
  eauto.
Qed.
(* begin hide *)

(* end hide *)

Lemma equal_chains_equal_fun_gen {o} : forall lib (fa fb T : @CTerm o),
  equality lib fa fb (mkc_fun T T)
  -> member lib mkc_bot T
  -> forall n, equality lib (fix_approxc n fa) (fix_approxc n fb) T.
Proof.
  introv Hfeq Hmem.
  apply equality_in_fun in Hfeq; repnd.
  unfold member in Hmem. 
  induction n;simpl;auto.
Qed.

Corollary equal_chains_equal_fun {o} : forall lib (fa fb T : @CTerm o),
  equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  -> forall n, equality lib (fix_approxc n fa) (fix_approxc n fb) (mkc_partial T).
Proof.
  introv Hfeq. apply equal_chains_equal_fun_gen; auto;[].
  apply bot_in_partial_type.
  apply equality_in_fun in Hfeq; repnd. auto.
Qed.

Lemma fix_approxc_removec {o} : forall f (fp : @isprog o f) n, 
 (get_cterm (fix_approxc n (exist _ f  fp))) = (fix_approx n f).
Proof.
  induction n; auto.
  simpl.
  destruct (fix_approxc n (exist _  f fp)) as [fn fnp].
  allsimpl.
  f_equal; auto.
Qed.


  
(** To recap the compactness theorem [fix_compactness]
    from %\ref{sec:comp:domain}%, here is a trivial restatement of it
    which that lifts it to the [CTerm] type.
 *)

Lemma fixc_compactness {o} : forall lib (f G : @CTerm o),
  hasvaluec lib (mkc_apply G (mkc_fix f))
  -> {n : nat $ hasvaluec lib (mkc_apply G (fix_approxc n f))}.
Proof.
  introv Hc.
  allunfold @hasvaluec.
  destruct f as [f fp]. destruct G as [G Gp]. allsimpl.
  assert ({n : nat $ hasvalue lib (mk_apply G (fix_approx n f))}).
  Focus 2. exrepnd; exists n. simpl.
    remember  (fix_approxc n (exist (fun t : NTerm => isprog t) f fp)) as fac.
    destruct fac as [fa fap].
    apply (f_equal get_cterm) in Heqfac.
    allsimpl.
    rw @fix_approxc_removec in Heqfac. subst fa.
    auto; fail.
  allsimpl.
  allrw @isprog_eq.
  apply fix_compactness_apply; auto.
Qed.

Lemma fixc_compactness_no_context {o} : forall lib (f : @CTerm o),
  hasvaluec lib (mkc_fix f)
  -> {n : nat $ hasvaluec lib (fix_approxc n f)}.
Proof.
  introv Hc.
  allunfold @hasvaluec.
  destruct f as [f fp].
  assert ({n : nat $ hasvalue lib (fix_approx n f)});
  [|exrepnd; exists n; rw @fix_approxc_removec; auto; fail].
  allsimpl.
  allrw @isprog_eq.
  apply fix_compactness_no_context; auto.
Qed.

(* begin hide *)
  
Lemma fixc_compactness_no_context_ccc {o} : forall lib f,
  @chaltsc o lib (mkc_fix f)
  -> {n : nat , chaltsc lib (fix_approxc n f)}.
Proof.
  introv Hc.
  spcast.
  apply fixc_compactness_no_context in Hc.
  exrepnd.
  exists n.
  spcast.
  auto.
Qed.

Lemma fixc_compactness_ccc {o} : forall lib (f G : @CTerm o),
  chaltsc lib (mkc_apply G (mkc_fix f))
  -> {n : nat , chaltsc lib (mkc_apply G (fix_approxc n f))}.
Proof.
  introv Hc.
  spcast.
  apply fixc_compactness in Hc.
  exrepnd.
  exists n.
  spcast.
  auto.
Qed.


(*
Theorem fix_compactness_anyvar : forall f e v,
  let tf := (apply_bterm (bterm [v] e) [mk_fix f]) in
  isprogram f
  -> isprogram tf
  -> hasvalue tf
  -> {n : nat $ let tfa := 
        (apply_bterm (bterm [v] e) [fix_approx n f]) in
          hasvalue tfa}.
Proof.
  simpl. introv Hpf Hptf Hv.
  apply ispro
  pose proof (alpha_eq_bterm_single_change e v).

  pose proof (apply_bterm_alpha_congr2)
*)

Lemma fixc_approx_hasvalue {o} : forall lib f n,
  @hasvaluec o lib (fix_approxc n f)
  -> hasvaluec lib (mkc_fix  f).
Proof.
  introv Hvc.
  allunfold @hasvaluec.
  destruct f as [f fp].
  rw @fix_approxc_removec in Hvc.
  simpl. allrw @isprog_eq.
  eapply fix_approx_hasvalue; eauto.
Qed.

Lemma fixc_approx_hasvalue_context {o}  : forall lib (f G : @CTerm o) (n: nat),
  hasvaluec lib (mkc_apply G (fix_approxc n f))
  -> hasvaluec lib (mkc_apply G (mkc_fix  f)).
Proof.
  introv Hvc.
  allunfold @hasvaluec.
  destruct f as [f fp].
  destruct G as [G Gp]. allsimpl.
  match type of Hvc with
  context [ fix_approxc n ?ff ] => remember (fix_approxc n ff) as fac
  end.
  apply (f_equal get_cterm) in Heqfac.
  destruct fac as [fa fap].
  allsimpl.
  rw @fix_approxc_removec in Heqfac.
  subst fa.
  simpl. allrw @isprog_eq.
  eapply fix_approx_hasvalue_context; eauto.
Qed.


Lemma fix_converges_equal_fun {o} : forall lib (fa fb T : @CTerm o),
  equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  ->  (chaltsc lib (mkc_fix fa) -> chaltsc lib (mkc_fix fb)).
Proof.
  introv Heq Hsv.
  apply' (equal_chains_equal_fun lib) Heq.
  apply fixc_compactness_no_context_ccc in Hsv.
  exrepnd.
  specialize (Heq n).
  apply equality_in_mkc_partial in Heq.
  exrepnd. applydup Heq1 in Hsv0.
  clear Heq Heq1 Heq0 Hsv0 fa T.
  spcast.
  eapply fixc_approx_hasvalue; eauto.
Qed.

Lemma fix_converges_equal_fun_context {o} : forall lib (fa fb Ua Ub T S : @CTerm o),
  member lib mkc_bot T
  -> equality lib fa fb (mkc_fun T T)
  -> equality lib Ua Ub (mkc_fun T (mkc_partial S))
  -> chaltsc lib (mkc_apply Ua (mkc_fix fa))
  -> chaltsc lib (mkc_apply Ub (mkc_fix fb)).
Proof.
  introv Hbot Hfeq Hceq Hsv.
  pose proof (equal_chains_equal_fun_gen _ _ _ _ Hfeq Hbot) as Hnfeq.
  apply fixc_compactness_ccc in Hsv.
  exrepnd.
  specialize (Hnfeq n).
  apply equality_in_fun in Hceq.
  exrepnd.
  apply Hceq in Hnfeq.  
  apply equality_in_mkc_partial in Hnfeq.
  exrepnd. applydup Hnfeq1 in Hsv0.
  clear Hnfeq Hnfeq1 Hnfeq0 Hsv0.
  spcast.
  eapply fixc_approx_hasvalue_context; eauto.
Qed.


(* end hide *)
Lemma fix_converges_equal_fun_iff_context {o} : forall lib (fa fb Ua Ub T S : @CTerm o),
  member lib mkc_bot T
  -> equality lib fa fb (mkc_fun T T)
  -> equality lib Ua Ub (mkc_fun T (mkc_partial S))
  -> (chaltsc lib (mkc_apply Ua (mkc_fix fa))
     <=> chaltsc lib (mkc_apply Ub (mkc_fix fb))).
Proof.
  introv Heq.
  split; eapply fix_converges_equal_fun_context; eauto with nequality.
Qed.

Lemma fix_converges_equal_fun_iff {o} : forall lib (fa fb T : @CTerm o),
  equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  ->  (chaltsc lib (mkc_fix fa) <=> chaltsc lib (mkc_fix fb)).
Proof.
  introv Heq.
  split; eapply fix_converges_equal_fun; eauto with nequality.
Qed.

Lemma fapproxc_hasvalue_higher {o} : forall lib f n,
  @hasvaluec o lib (fix_approxc n f)
  -> forall m, hasvaluec lib (fix_approxc (m+n) f).
Proof.
  introv Hvc.
  allunfold @hasvaluec.
  destruct f as [f fp].
  rw @fix_approxc_removec in Hvc.
  simpl. intro m.
  rw @fix_approxc_removec. allrw @isprog_eq.
  simpl. eapply fapprox_hasvalue_higher; eauto.
Qed.
(* begin hide *)


Lemma cvterm_nvarx {o} : @CVTerm o [nvarx].
  exists (@vterm o nvarx).
  apply isprog_vars_mk_var; simpl; tcsp.
Defined.

Hint Immediate bool_dec : slow.
Lemma substc_cvterm_nvarx {o} : forall (t : @CTerm o),
  (substc t nvarx cvterm_nvarx) = t.
Proof.
  intros.
  simpl. destruct t. simpl.
  apply cterm_eq; simpl.
  unfold subst. allsimpl.
  change_to_lsubst_aux4. allsimpl; auto.
Qed.

Lemma cvterm_nvarx_pi1 {o} : @CVTerm o [nvarx].
  exists (mk_pi1 (@vterm o nvarx)).
  apply isprog_vars_eq; simpl; dands; eauto 3 with slow.
  constructor; simpl; unfold num_bvars; simpl; tcsp.
  introv i; repndors; subst; tcsp.
  apply bt_wf_iff; eauto 3 with slow.
Defined.

Lemma cvterm_nvarx_pi2 {o} : @CVTerm o [nvarx].
  exists (mk_pi2 (@vterm o nvarx)).
  apply isprog_vars_eq; simpl; dands; eauto 3 with slow.
  constructor; simpl; unfold num_bvars; simpl; tcsp.
  introv i; repndors; subst; tcsp.
  apply bt_wf_iff; eauto 3 with slow.
Defined.

Lemma fvnil_program_erw {o} : forall t : @NTerm o,
  isprogram t
  -> free_vars t = [].
Proof.
  introv Hp.
  repnud Hp.
  auto.
Qed.

Hint Rewrite @fvnil_program_erw : slow.

Lemma mkc_pi1 {o} : forall (t: @CTerm o) , @CTerm o.
Proof.
  intro t.
  destruct t as [t tp].
  exists (mk_pi1 t).
  allrw @isprog_eq.
  unfold mk_pi1, mk_spread.
  repeat(decomp_progc); auto.
  unfolds_base.
  dands; auto.
  unfolds_base.
  dands; auto.
Defined.

Lemma mkc_pi2 {o} : forall (t: @CTerm o) , @CTerm o.
Proof.
  intro t.
  destruct t as [t tp].
  exists (mk_pi2 t).
  allrw @isprog_eq.
  unfold mk_pi2, mk_spread.
  repeat(decomp_progc); auto.
  unfolds_base.
  dands; auto.
  unfolds_base.
  dands; auto.
Defined.





(*
Lemma substc_cvterm_nvarx_pi1 : forall (t : CTerm),
  (substc t nvarx cvterm_nvarx_pi1) = mkc_pi1 t.
Proof.
  intros.
  simpl. destruct t. simpl.
  unfold subst. allsimpl. 
  change_to_lsubst_aux4. allsimpl.
  f_equal.
  apply UIP_dec; auto with slow.
Qed.
*)

Lemma fapproxc_hasvalue_higher_cc {o} : forall lib f n,
  @chaltsc o lib (fix_approxc n f)
  -> forall m, chaltsc lib (fix_approxc (m+n) f).
Proof.
  intros. spcast.
  eapply fapproxc_hasvalue_higher; eauto.
Qed.

Lemma fapproxc_hasvalue_higher_cc2 {o} : forall lib f n,
  @chaltsc o lib (fix_approxc n f)
  -> forall m, m>n -> chaltsc lib (fix_approxc (m) f).
Proof.
  introv HH Hgt.
  apply' @fapproxc_hasvalue_higher_cc HH.
  specialize (HH (m-n)).
  assert (m - n + n = m) as Xr by lia.
  rw Xr in HH.
  auto.
Qed.

Definition admissible_equality_no_context {o} (eq : per) :=
  forall  (f : @CTerm o),
    {j: nat, forall k : nat, k > j -> eq (fix_approxc k f) (fix_approxc k f) }
    -> eq (mkc_fix f) (mkc_fix f).

Lemma admissible_equality_no_context_if {o} :
  forall eq : per(o), admissible_equality eq 
      -> admissible_equality_no_context eq.
Proof.
  introv Had.
  unfolds_base.
  repnud Had.
  introv Heq.
  exrepnd.
  specialize(Had nvarx cvterm_nvarx cvterm_nvarx f).
  unfold subst_fix_eqc, cofinite_subst_fapprox_eqc in Had.
  unfold subst_fapproxc in Had.
  unfold subst_fixc in Had.
  rw @substc_cvterm_nvarx in Had.
  apply Had. exists j.
  introv Hgt.
  rw @substc_cvterm_nvarx. eauto.
Qed.

Definition cofinite_subst_fapprox_eqc_new {o}
           (eq : per)
           {v: NVar}
           (e e' : CVTerm [v])
           (f f' : @CTerm o) :=
    {j : nat
     , forall (k :nat),
         k>j -> eq (subst_fapproxc e f k) (subst_fapproxc e' f' k)}.

Definition subst_fix_eqc_new {o}
           (eq : per)
           {v: NVar}
           (e e' : CVTerm [v])
           (f f' : @CTerm o) :=
  eq (subst_fixc e f)  (subst_fixc e' f').

Definition admissible_equality_new {o} (eq : per(o)) :=
  forall v (e e' : CVTerm [v]) (f f' : CTerm),
    cofinite_subst_fapprox_eqc_new eq e e' f f'
    -> subst_fix_eqc_new eq e e' f f'.



Lemma mk_pair_apply_nvarx_ccc {o} : forall (f f' : @CTerm o), @CVTerm o [nvarx].
Proof.
  intros. destruct f as [f fp].
  destruct f' as [f' fp'].
  exists (mk_pair (mk_apply f (mk_pi1 (vterm nvarx)))
                  (mk_apply f' (mk_pi1 (vterm nvarx)))).
  apply isprog_vars_eq; simpl; autorewrite with slow; simpl;
  allrw @isprogram_eq; dands; eauto 3 with slow.
  apply nt_wf_eq.
  apply wf_pair; dands; apply wf_apply_iff; dands; eauto 3 with slow.
  - apply wf_pi1; eauto 3 with slow.
  - apply wf_pi2; eauto 3 with slow.
Qed.

(* end hide *)
Definition is_nice_per {o} lib (eq : per(o)) :=
  term_equality_symmetric eq
  # term_equality_transitive eq
  # term_equality_respecting lib eq.

Lemma nuprl_pers_are_nice {o}:
  forall lib (T T': CTerm) (eq: per(o)),
  nuprl lib T T' eq
  -> is_nice_per lib eq.
Proof.
  introv Hn.
  pose proof (@nuprl_type_system o lib) as Hns.
  repnud Hns.
  unfolds_base; dands; eauto.
Qed.
  
(* begin hide *)
Lemma nice_per_prop1 {o} : forall lib eq t t',
  @is_nice_per o lib eq
  -> eq t t' -> eq t t.
Proof.
  introv Hn Heq.
  repnud Hn.
  applydup Hn0 in Heq.
  eauto.
Qed.

Lemma nice_per_respects_cequivc {o} : forall lib eq,
  @is_nice_per o lib eq
  -> respects2 (cequivc lib) eq.
Proof.
  introv Hn. repnud Hn.
  split; introv Hc Heq;
  apply cast in Hc;
  apply Hn in Hc;
  eauto.
Qed.

(* end hide *)
(** We will show that if the PER of a type satisfies the following
  [fixpoint_induction_suff] condition, then
  the fixpoint induction principle holds for it.
  The next lemma shows that PERs of Mono types satisfy this condition.

 *)

Definition fixpoint_induction_suff {o} (eq : per(o)) :=
  forall  (f f' : CTerm),
    {j: nat, forall k : nat, k > j -> eq (fix_approxc k f) (fix_approxc k f') }
    -> eq (mkc_fix f) (mkc_fix f').

Lemma fixpoint_induction_suff_if_mono {o} : forall lib (eq : per(o)),
  is_nice_per lib eq
  -> mono_equality lib eq
  -> fixpoint_induction_suff eq.
Proof.
  introv Hnc Had.
  repnud Had. unfolds_base.
  introv Hcfs.
  exrepnd.
  dimp (Hcfs0 (S j)). duplicate hyp as Heqb.
  apply (nice_per_prop1 _ _ _ _ Hnc) in hyp; eauto.
  apply Had with (t':=mkc_fix f) in hyp;
  [ | unfold approxc; destruct_cterms; rw @fix_approxc_removec;
     apply fix_approx_ub; auto; allrw <- @isprog_eq; auto; fail].
  duplicate Hnc as Hncb. repnud Hnc.
  duplicate Heqb as Heqbb. apply Hnc0 in Heqb.
  apply (nice_per_prop1 _ _ _ _ Hncb) in Heqb; auto.
  apply Had with (t':=mkc_fix f') in Heqb;
  [ | unfold approxc; destruct_cterms; rw @fix_approxc_removec;
     apply fix_approx_ub; auto; allrw <- @isprog_eq; auto; fail].
  eauto.
Qed.

(* begin hide *)

Lemma fixpoint_induction_suff_if {o} :
  forall eq : per(o), admissible_equality_new eq 
      -> fixpoint_induction_suff eq.
Proof.
  introv Had.
  unfolds_base.
  repnud Had.
  introv Heq.
  exrepnd.
  specialize(Had nvarx cvterm_nvarx cvterm_nvarx f f').
  unfold subst_fix_eqc_new, cofinite_subst_fapprox_eqc_new in Had.
  unfold subst_fapproxc in Had.
  unfold subst_fixc in Had.
  allrw @substc_cvterm_nvarx.
  apply Had. exists j.
  introv Hgt.
  allrw @substc_cvterm_nvarx. eauto.
Qed.


(* end hide *)

(** %\noindent% The following lemma distills out the key idea in the
    proofs of the rules [rule_fixpoint_principle_mono] (above) and 
    [rule_fixpoint_principle_admiss] (below).
    Due to functionality requirements of sequents,
    it is actually used three times in the proofs of these rules.
    The proof uses the compactness  property [fixc_compactness_no_context].


    We apply the lemma [equality_in_mkc_partial]. So we have to prove
    3 things. Firstly, we have to prove that [mkc_partial T] is a type.
    This is true because our second hypothesis implies that
    [(mk_fun (mk_partial T) (mk_partial T))] is a type.
    Secondly, we have to prove 
    [(chaltsc (mkc_fix fa) <=> chaltsc (mkc_fix fb))].
    This is a trivial consequence of the lemma [fix_converges_equal_fun_iff]
    above. Finally, we have to assume that [(mkc_fix fa)] converges
    and prove that [(mkc_fix fa)] and [(mkc_fix fb)] are equal in the type
    [T].
  
    By compactness and because [(mkc_fix fa)] converges, one of its partial
    approximations(say [(fix_approxc n fa)]) converges, and is hence
    a member of the type [T].
    By the lemma [fapprox_hasvalue_higher], we have that
    [(fix_approxc m fa)] converges for all [m>=n].

    By lemma [equal_chains_equal_fun], we have that for all [m>=n],
    [(fix_approxc m fb)] is equal to [(fix_approxc m fa)] in [mkc_partial T].
    So, by the lemma [equality_mkc_partial],
    [fix_approxc m fb] converges too and is equal to [(fix_approxc m fa)]
    in the type [T]. 
    
    The rest of the proof is a straightforward
    consequence of thet hypothesis that
    the  PER of the type [T] satisfies the 
    [fixpoint_induction_suff] condition,
 *)

Lemma fixpoint_induction_general {o} :  forall lib fa fb T eqT,
  @nuprl o lib T T eqT
  -> fixpoint_induction_suff eqT
  -> equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  -> equality lib (mkc_fix fa) (mkc_fix fb) (mkc_partial T).
Proof.
  introv Hn Hm Hfeq.
  applydup @inhabited_implies_tequality in Hfeq.
  apply @tequality_mkc_fun_l in Hfeq0.
  duplicate Hfeq.
  apply' (equal_chains_equal_fun lib) Hfeq1.
  applydup @fix_converges_equal_fun_iff in Hfeq.
  apply equality_in_mkc_partial; dands; auto;[].
  introv Hcv.
  apply fixc_compactness_no_context_ccc in Hcv.
  exrepnd.
  apply' @fapproxc_hasvalue_higher_cc2 Hcv0.
  exrepnd.
  unfold equality.
  exists eqT.
  dands; auto;[].

  assert ( forall k : nat, k > n -> eqT (fix_approxc k fa) (fix_approxc k fb)) as Hapx.
  - introv Hgt. specialize (Hfeq1 k). apply Hcv0 in Hgt.
    apply equality_in_mkc_partial in Hfeq1. repnd.
    apply Hfeq1 in Hgt. repnud Hgt. exrepnd. repnud Hgt1. equality_unique.
    apply Huniq. auto.
  - clear Hcv0 Hfeq2 Hfeq1 Hfeq0 Hfeq.
    repnud Hm.
    apply Hm; exists n; auto.
Qed.

Corollary fixpoint_induction_helper_mono {o} : forall lib (fa fb T : @CTerm o),
   member lib mkc_axiom (mkc_mono T)
  -> equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  -> equality lib (mkc_fix fa) (mkc_fix fb) (mkc_partial T).
Proof.
  introv Hm Hfeq.
  apply equality_in_mkc_mono in Hm.
  exrepnd.
  apply fixpoint_induction_general with (eqT:=eqa); auto.
  apply (fixpoint_induction_suff_if_mono lib); auto.
  eapply nuprl_pers_are_nice; eauto.
Qed.


Corollary rule_fixpoint_principle_mono_true {o} :
  forall lib (f1 f2 T : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_fixpoint_principle_mono
                 f1 f2 T
                 H).
Proof.
  unfold rule_fixpoint_principle_mono, rule_true, closed_type_baresequent, closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  (* We prove the well-formedness of things *)
  destruct Hyp as [ wsa Hypa ].
  destruct Hyp0 as [ wsb Hypb ].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in Hypa.
  generalize (Hypa s1 s2 eqh sim). clear Hypa. intro Hypa. exrepnd.

  vr_seq_true in Hypb.
  generalize (Hypb s1 s2 eqh sim); clear Hypb; intro Hypb; exrepnd.
  lsubst_tac.
  rw @tequality_mono in Hypb0.
  allrw @member_eq.
  apply member_equality_iff in Hypa1.
  let Xrr := fresh Xrr in
  match goal with
  [ H: context [lsubstc (mk_fun ?A ?A) ?wfA ?s ?wcA ] , Aw: wf_term ?A, Ac : cover_vars ?A ?s |- _]
      =>pose proof (lsubstc_mk_fun A A s Aw Aw wfA Ac Ac wcA)  as Xrr;
        rwhg Xrr H; clear Xrr 
  end.
  repeat match goal with
  [ H: context [mkc_equality ?a ?b (lsubstc (mk_fun ?A ?A) ?wfA ?s ?wcA) ] , Aw: wf_term ?A, Ac : cover_vars ?A ?s |- _]
      =>pose proof (lsubstc_mk_fun A A s Aw Aw wfA Ac Ac wcA)  as Xrr;
        apply (mkc_equality_alpha_congr a b) in Xrr; rwhg Xrr H; clear Xrr
  end.
  lsubst_tac.


  repeat match goal with
  [H: context [lsubstc ?f ?w ?s ?c] |- context [lsubstc (mk_fix ?f) _ ?s _ ] ]
    => rewrite (lsubstc_mk_fix _ _ w _ c _);
       let fs := fresh f s in 
        remember (lsubstc f w s c) as fs
  end.

  repeat match goal with
  [H : wf_term _ |- _ ] => clear H
  |[H : cover_vars _ _ |- _ ] => clear H
  end.

  duplicate Hypa0 as Hpart.
  applydup @tequality_mkc_equality_implies in Hpart. repnd.
  clear Hpart0 Hpart2 Hpart.
  apply @tequality_mkc_fun_l in Hpart1.
  remember (lsubstc T w0 s1 c0) as Ts1.
  apply @tequality_mkc_equality in Hypa0.
  repnd.
  assert (forall fa fb,
        equality lib fa fb (mkc_fun (mkc_partial Ts1) (mkc_partial Ts1))
        -> equality lib (mkc_fix fa) (mkc_fix fb) (mkc_partial Ts1)) as Hxx by
    (introv; apply fixpoint_induction_helper_mono; auto).
  dands; auto.
  apply @tequality_mkc_equality_if_equal; sp; apply Hxx.
  - apply Hypa4. apply equality_refl in Hypa1; auto.
  - apply Hypa0.  apply equality_sym in Hypa1; apply equality_refl in Hypa1; auto.
  
Qed.


Ltac decomp_ntwfc := unfold_all_mk;
match goal with 
| [ |- nt_wf _] 
    => try trivial;constructor;
     [| spc;fail]; introv Hin; 
    repeat(in_reasoning); cpx
| [ |- bt_wf (bterm _ ?lbt)] 
    => constructor
| [ |- bt_wf ?b] 
    => subst b
 end.

(* begin hide *)

Definition crary_f'' {o} (f f' : @NTerm o) :=
  mk_lam nvarx (mk_pair (mk_apply f (mk_pi1 (vterm nvarx))) 
                        (mk_apply f' (mk_pi2 (vterm nvarx)))).

Lemma crary_f''_isp {o} : forall f f' : @NTerm o,
  isprogram f
  -> isprogram f'
  -> isprogram (crary_f'' f f').
Proof.
  introv H1p H2p.
  unfold crary_f''.
  unfold_all_mk.
  repeat(decomp_progc).
  split.
  - unfolds_base. simpl. simpl_vlist.
    autorewrite with slow;auto.
  - repnud H1p. repnud H2p.
    repeat(decomp_ntwfc); auto.
Qed.

Hint Resolve crary_f''_isp : program.

Ltac dest_ctermsn :=
repeat match goal with
[c: CTerm |- _ ] => let cp := fresh c "pr" in 
  destruct c as [c cp]
end.

Lemma mkc_crary_f'' {o} : @CTerm o -> @CTerm o -> @CTerm o.
Proof.
  introv f f'.
  dest_ctermsn.
  exists (crary_f'' f f').
  allrw @isprog_eq.
  eauto with program.
Defined.

Lemma substc_cvterm_pi1 {o} : forall (t : @CTerm o),
  (substc t nvarx cvterm_nvarx_pi1) = mkc_pi1 t.
Proof.
  intros.
  apply cterm_eq.
  dest_ctermsn.
  simpl.
  unfold subst. allsimpl. 
  change_to_lsubst_aux4;[refl|].
  simpl.
  autorewrite with slow; auto.
  eauto 3 with slow.
Qed.

Lemma substc_cvterm_pi2 {o} : forall (t : @CTerm o),
  (substc t nvarx cvterm_nvarx_pi2) = mkc_pi2 t.
Proof.
  intros.
  apply cterm_eq.
  dest_ctermsn.
  simpl.
  unfold subst. allsimpl. 
  change_to_lsubst_aux4;[refl|].
  simpl.
  allrw @isprog_eq.
  autorewrite with slow; auto.
Qed.


Hint Resolve fix_approx_program: program.


Ltac decomp_progc3 := unfold_all_mk;
match goal with 
| [ |- isprogram (oterm _ ?lbt)] => repeat(decomp_progc)
| [ |- isprogram_bt (bterm [] ?lbt)] => apply implies_isprogram_bt0
| [ |- isprogram_bt (bterm _ _)] 
    => split;[unfold closed_bt| repeat(decomp_ntwfc)]
 end.


Lemma remove_nvars {o} : forall lv v,
  LIn v lv
  -> isprogram_bt (bterm lv (@vterm o v)).
Proof.
  introv Hin.
  split.
  unfolds_base.
  simpl. unfold remove_nvars.
  simpl.
Abort.

Lemma isprogram_if_eauto {o}
     : forall t : @NTerm o, isprog t -> isprogram t.
Proof.
  introv.
  allrw @isprog_eq.
  trivial.
Qed.

(*
Lemma compute_decompose_val {o} :
  forall lib (op : NonCanonicalOp)
         (lbt : list BTerm)
         (a: NTerm),
    isprogram (oterm (NCan op) lbt)
    -> computes_to_value lib (oterm (NCan op) lbt) a
    -> {la : NTerm
        $ {v : @NTerm o
        $ {lbtt: (list BTerm)
        $ lbt = (bterm [] la)::lbtt
        # computes_to_value lib la v
          [+] {a : NTerm & computes_to_exception lib a la v}}}}
       [+]
       {v : NVar
        $ {t, u, x, w : NTerm
        # op = NFresh
        # lbt = [bterm [v] t]
        # (let ut := get_fresh_atom t in
           computes_to_value lib (subst t v (mk_utoken ut)) x
           computes_to_value lib (subst t v (mk_utoken ut)) x
           # alpha_eq x (subst u v (mk_utoken ut))
           # subset (get_utokens u) (get_utokens t)
           # reduces_in_atmost_k_steps lib (oterm (NCan op) lbt) (mk_fresh v w) m
           # alpha_eq u w # isvalue_like u)}}}.
Proof.
  introv Hpr Hcv.
  unfold computes_to_value, reduces_to in Hcv; exrepnd.
  pose proof (compute_decompose lib op k lbt a Hpr) as h.
  autodimp h hh.

  - unfold computes_to_value_in_max_k_steps; auto; sp.
    apply no_change_after_value_ra with (k1 := k); auto.

  - repndors; exrepnd; subst.

    + applydup @isprogram_ot_iff in Hpr; repnd.
      pose proof (Hpr0 (nobnd la)) as g; autodimp g gg; simpl; auto.
      apply isprogram_bt_nobnd in g.
      applydup @reduces_atmost_preserves_program in h3; auto.

      dorn h1.

      * eexists; eexists; eexists; dands; eauto.
        left; eauto.
        unfold computes_to_value, reduces_to; dands.
        exists m; eauto.
        rw @isvalue_iff; dands; auto.

      * apply isexc_implies in h1; auto.
        exrepnd; subst.
        eexists; eexists; eexists; dands; eauto.
        right.
        unfold computes_to_exception, reduces_to; eauto.

    + remember (get_fresh_atom t) as ut; allsimpl; repnd; fold_terms.
      exists 
Qed.
 *)

Lemma reduces_in_atmost_k_steps_primarg {o} :
  forall lib j k op (t : @NTerm o) bs u v,
    reduces_in_atmost_k_steps lib (oterm (NCan op) (bterm [] t :: bs)) v k
    -> reduces_in_atmost_k_steps lib t u j
    -> isvalue_like v
    -> {l : nat & reduces_in_atmost_k_steps lib (oterm (NCan op) (bterm [] u :: bs)) v l}.
Proof.
  induction j; introv r1 r2 isv.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists k; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct k.
    + allrw @reduces_in_atmost_k_steps_0; subst; simpl.
      provefalse; unfold isvalue_like in isv; repndors; inversion isv.
    + rw @reduces_in_atmost_k_steps_S in r1; exrepnd.
      destruct t as [v1|f1|op1 bs1]; try (complete (allsimpl; ginv)).
      { csunf r2; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
        exists (S k).
        apply reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
      dopid op1 as [can1|ncan1|exc1|abs1] Case; try (complete (allsimpl; ginv)).
      * csunf r2; simpl in r2; ginv.
        apply reduces_atmost_can in r0; subst.
        exists (S k).
        rw @reduces_in_atmost_k_steps_S; eexists; eauto.
      * rw @compute_step_ncan_ncan in r1.
        rw r2 in r1; ginv.
        apply (IHj _ _ _ _ u) in r3; auto.
      * csunf r2; simpl in r2; ginv.
        apply reduces_atmost_exc in r0; subst.
        exists (S k).
        rw @reduces_in_atmost_k_steps_S; eexists; eauto.
      * rw @compute_step_ncan_abs in r1.
        csunf r2; allsimpl.
        rw r2 in r1; ginv.
        apply (IHj _ _ _ _ u) in r3; auto.
Qed.

(*
Lemma compute_decompose_exc {o} :
  forall lib en (op : NonCanonicalOp)
         (lbt : list BTerm)
         (a: NTerm),
    isprogram (oterm (NCan op) lbt)
    -> computes_to_exception lib en (oterm (NCan op) lbt) a
    -> {la : NTerm
       $ {v : @NTerm o
       $ {lbtt: (list BTerm)
         $ lbt = (bterm [] la)::lbtt
         # computes_to_value lib la v
           [+] {en : exc_name & computes_to_exception lib en la v}}}}.
Proof.
  introv Hpr Hcv.
  unfold computes_to_exception, reduces_to in Hcv; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv0; auto.
  generalize (compute_decompose_aux lib op k lbt (mk_nexception en a) Hpr); intro h.
  autodimp h hh.

  - unfold computes_to_val_like_in_max_k_steps; auto; sp; try (right; left; sp).
    apply no_change_after_val_or_exc with (k1 := k); auto; try (right; sp).

  - exrepnd; subst.

    applydup @isprogram_ot_iff in Hpr; repnd.
    generalize (Hpr0 (nobnd la)); intro g; autodimp g gg; simpl; auto.
    apply isprogram_bt_nobnd in g.
    applydup @reduces_atmost_preserves_program in h3; auto.

    dorn h1.

    + eexists; eexists; eexists; dands; eauto.
      left; eauto.
      unfold computes_to_value, reduces_to; dands.
      exists m; eauto.
      rw @isvalue_iff; dands; auto.

    + apply isexc_implies in h1; auto.
      exrepnd; subst.
      eexists; eexists; eexists; dands; eauto.
      right.
      unfold computes_to_exception, reduces_to; eauto.
Qed.
 *)

Lemma computes_to_value_implies_computes_to_val_like_in_max_k_steps {o} :
  forall lib (t u : @NTerm o),
    computes_to_value lib t u
    -> {k : nat & computes_to_val_like_in_max_k_steps lib t u k}.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  unfold reduces_to in comp0; exrepnd.
  exists k.
  unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow.
Qed.

Lemma computes_to_exception_implies_computes_to_val_like_in_max_k_steps {o} :
  forall lib a (t u : @NTerm o),
    computes_to_exception lib a t u
    -> {k : nat & computes_to_val_like_in_max_k_steps lib t (mk_exception a u) k}.
Proof.
  introv comp.
  unfold computes_to_exception in comp; repnd.
  unfold reduces_to in comp; exrepnd.
  exists k.
  unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow.
Qed.

Lemma isvalue_like_implies_not_isnoncan_like {o} :
  forall (t : @NTerm o), isvalue_like t -> !isnoncan_like t.
Proof.
  introv isv.
  unfold isvalue_like in isv; unfold isnoncan_like.
  repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; allsimpl; tcsp.
  - apply isexc_implies2 in isv; exrepnd; subst; allsimpl; tcsp.
Qed.

Lemma isnoncn_like_implies_not_isvalue_like {o} :
  forall (t : @NTerm o), isnoncan_like t -> !isvalue_like t.
Proof.
  introv isv.
  unfold isnoncan_like in isv; unfold isvalue_like.
  repndors.
  - apply isnoncan_implies in isv; exrepnd; subst; allsimpl; tcsp.
  - apply isabs_implies in isv; exrepnd; subst; allsimpl; tcsp.
Qed.

Lemma computes_to_val_like_in_max_k_steps_if_isnoncan_like {o} :
  forall lib k (t u : @NTerm o),
    isnoncan_like t
    -> computes_to_val_like_in_max_k_steps lib t u k
    -> {n : nat & k = S n}.
Proof.
  introv isn comp.
  destruct k.
  - allrw @computes_to_val_like_in_max_k_steps_0; repnd; subst.
    apply isvalue_like_implies_not_isnoncan_like in comp; tcsp.
  - eexists; eauto.
Qed.

Lemma if_hasvalue_spread {o} : forall lib t vx vy td,
  @isprogram o (mk_spread t vx vy td)
  -> hasvalue lib (mk_spread t vx vy td)
  -> hasvalue lib t [+] raises_exception lib t.
Proof.
  introv Hpr Hsv.
  repnud Hsv.
  exrepnd.
  apply computes_to_value_implies_computes_to_val_like_in_max_k_steps in Hsv0; exrepnd.
  unfold mk_spread, nobnd in Hsv1.
  applydup @computes_to_val_like_in_max_k_steps_if_isnoncan_like in Hsv1; tcsp; exrepnd; subst.
  apply compute_decompose_aux in Hsv1; auto.
  repndors; exrepnd; ginv.
  unfold is_can_or_exc in Hsv1; repndors.
  - left.
    eapply reduces_in_atmost_k_steps_implies_hasvalue; eauto.
    eapply reduces_atmost_preserves_program; eauto.
    allrw @isprogram_spread_iff2; sp.
  - right.
    eapply reduces_in_atmost_k_steps_implies_raises_exception; eauto.
    eapply reduces_atmost_preserves_program; eauto.
    allrw @isprogram_spread_iff2; sp.
Qed.

Lemma if_raises_exception_spread {o} :
  forall lib t vx vy td,
    @isprogram o (mk_spread t vx vy td)
    -> raises_exception lib (mk_spread t vx vy td)
    -> hasvalue lib t [+] raises_exception lib t.
Proof.
  introv Hpr Hsv.
  repnud Hsv.
  exrepnd.
  apply computes_to_exception_implies_computes_to_val_like_in_max_k_steps in Hsv1; exrepnd.
  unfold mk_spread, nobnd in Hsv0.
  applydup @computes_to_val_like_in_max_k_steps_if_isnoncan_like in Hsv0; tcsp; exrepnd; subst.
  apply compute_decompose_aux in Hsv0; auto.
  repndors; exrepnd; ginv.
  unfold is_can_or_exc in Hsv0; repndors.
  - left.
    eapply reduces_in_atmost_k_steps_implies_hasvalue; eauto.
    eapply reduces_atmost_preserves_program; eauto.
    allrw @isprogram_spread_iff2; sp.
  - right.
    eapply reduces_in_atmost_k_steps_implies_raises_exception; eauto.
    eapply reduces_atmost_preserves_program; eauto.
    allrw @isprogram_spread_iff2; sp.
Qed.

(*
Lemma compute_decompose_mrk {o} :
  forall lib (op : NonCanonicalOp)
         (lbt : list BTerm)
         (m : marker),
    isprogram (oterm (NCan op) lbt)
    -> computes_to_marker lib (oterm (NCan op) lbt) m
    -> {la : NTerm
       $ {v : @NTerm o
       $ {lbtt: (list BTerm)
         $ lbt = (bterm [] la)::lbtt
         # computes_to_value lib la v
           [+] {en : exc_name & computes_to_exception lib en la v}}}}.
Proof.
  introv Hpr Hcv.
  unfold computes_to_marker, reduces_to in Hcv; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv0; auto.
  generalize (compute_decompose_aux lib op k lbt (mk_marker m) Hpr); intro h.
  autodimp h hh.

  - unfold computes_to_val_like_in_max_k_steps; auto; sp; try (right; right; sp).
    apply no_change_after_val_like with (k1 := k); auto; try (right; right; sp).

  - exrepnd; subst.
    applydup @isprogram_ot_iff in Hpr; repnd.
    generalize (Hpr0 (nobnd la)); intro g; autodimp g gg; simpl; auto.
    apply isprogram_bt_nobnd in g.
    applydup @reduces_atmost_preserves_program in h3; auto.

    dorn h1.

    + exists la t lbtt; dands; auto.
      left; auto.
      unfold computes_to_value, reduces_to; dands.
      * exists m0; auto.
      * rw @isvalue_iff; dands; auto.

    + apply isexc_implies in h1; auto; exrepnd; subst.
      exists la e lbtt; dands; auto.
      right; auto.
      unfold computes_to_exception, reduces_to; dands.
      exists a m0; auto.
Qed.

Lemma primarg_if_computes_to_marker_non_catch {o} :
  forall lib (t : @NTerm o) op bs m,
    isprogram t
    -> (forall a, op <> NTryCatch a)
    -> computes_to_marker lib (oterm (NCan op) (nobnd t :: bs)) m
    -> hasvalue lib t.
Proof.
  introv isp ne comp.
  unfold computes_to_marker, reduces_to in comp; exrepnd.
  revert t isp comp0.
  induction k; introv isp comp.
  - rw @reduces_in_atmost_k_steps_0 in comp; allsimpl; ginv.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t as [v|op1 bs1].
    + simpl in comp1; ginv.
    + dopid op1 as [c1 | nc1 | exc1 | mrk1 | abs1] Case.
      * Case "Can".
        unfold hasvalue.
        exists (oterm (Can c1) bs1).
        unfold computes_to_value; dands; auto.
        apply reduces_to_symm.
      * Case "NCan".
        unfold nobnd in comp1.
        rw @compute_step_ncan_ncan in comp1.
        remember (compute_step lib (oterm (NCan nc1) bs1)) as cs; destruct cs; ginv.
        symmetry in Heqcs.
        applydup @preserve_compute_step in Heqcs; auto.
        apply IHk in comp0; auto.
        eapply reduces_to_hasvalue; eauto.
        apply reduces_to_if_step; auto.
      * Case "Exc".
        simpl in comp1.
        unfold nobnd in comp1.
        rw @compute_step_catch_non_trycatch in comp1; auto; ginv.
        apply reduces_in_atmost_k_steps_exception in comp0; ginv.
      * Case "Mrk".
        allsimpl; ginv.
        apply reduces_in_atmost_k_steps_primarg_marker in comp0; ginv.
      * Case "Abs".
        simpl in comp1.
        unfold on_success in comp1.
        remember (compute_step_lib lib abs1 bs1) as csl.
        destruct csl; ginv.
        symmetry in Heqcsl.
        applydup @isprogram_compute_step_lib in Heqcsl; auto.
        apply IHk in comp0; auto.
        eapply reduces_to_hasvalue; eauto.
        apply reduces_to_if_step; auto.
Qed.

Lemma if_marks_spread {o} :
  forall lib t vx vy td,
    @isprogram o (mk_spread t vx vy td)
    -> marks lib (mk_spread t vx vy td)
    -> hasvalue lib t.
Proof.
  introv Hpr Hsv.
  repnud Hsv.
  exrepnd.
  allunfold @mk_spread.
  unfold_all_mk2.
  apply primarg_if_computes_to_marker_non_catch in Hsv0; eauto with slow.
  introv k; inversion k.
Qed.
 *)

Lemma if_hasvalue_mk_pi2 {o} : forall lib t,
  @isprogram o t
  -> hasvalue lib (mk_pi2 t)
  -> hasvalue lib t [+] raises_exception lib t.
Proof.
  introv Hpr Hsv.
  repnud Hsv.
  exrepnd.
  unfold mk_pi2, mk_spread, nobnd in Hsv0.
  apply computes_to_value_implies_computes_to_val_like_in_max_k_steps in Hsv0; exrepnd.
  applydup @computes_to_val_like_in_max_k_steps_if_isnoncan_like in Hsv1; tcsp; exrepnd; subst.
  apply compute_decompose_aux in Hsv1; auto;[|repeat (decomp_progc3); eauto with program].
  repndors; exrepnd; ginv.
  unfold is_can_or_exc in Hsv1; repndors.
  - left.
    eapply reduces_in_atmost_k_steps_implies_hasvalue; eauto.
    eapply reduces_atmost_preserves_program; eauto.
  - right.
    eapply reduces_in_atmost_k_steps_implies_raises_exception; eauto.
    eapply reduces_atmost_preserves_program; eauto.
Qed.


Hint Resolve isprog_ntwf_eauto
  isprog_pi2 isprog_pi1 isprogram_bot
  isprogram_implies isprogram_if_eauto : program.

Hint Resolve not_hasvalue_bot: slow.

(* !! MOVE to computation4 *)
Lemma not_raises_exception_bot {o} : forall lib, @raises_exception o lib mk_bot -> False.
Proof.
  introv re.
  unfold raises_exception in re; exrepnd.
  apply bottom_doesnt_raise_an_exception in re1; sp.
Qed.

Ltac cequivl_cstepc :=
  let hyp1 := fresh "Hyp" in
  let hyp2 := fresh "Hyp'" in
  let v := fresh "v" in
  match goal with
      [ |- cequiv ?lib ?tl _] =>
      assert {v : NTerm & compute_step lib tl = csuccess v} as hyp1;
        [csunf; simpl; eexists; complete auto
        |destruct hyp1 as [v hyp1]; dup hyp1 as hyp2;
         csunf hyp2; simpl in hyp2; rw <- hyp2 in hyp1;
         clear hyp2;
         apply reduces_to_if_step in hyp1
        ]
  end.

Lemma crary_f''_fapprox_pi2 {o} :
  forall lib (f f' : @NTerm o),
    let f'' := crary_f'' f f' in
    isprogram f
    -> isprogram f'
    -> forall j,
         cequiv lib (mk_pi2 (fix_approx j f''))
                (fix_approx j f').
Proof.
  introv Hpf Hpf'. simpl.
  induction j.
  - remember @mkc_pi2 as xx.
    simpl.
    subst xx. split.
    + apply approx_assume_hasvalue;
      eauto with program.
      introv Hv. provefalse.
      apply hasvalue_like_implies_or in Hv; auto; eauto with program.
      dorn Hv.
      * apply if_hasvalue_spread in Hv; auto;
        [| repeat (decomp_progc3); eauto with program].
        dorn Hv; eauto using not_hasvalue_bot, not_raises_exception_bot.
      * apply if_raises_exception_spread in Hv; auto;
        [| repeat (decomp_progc3); eauto with program].
        dorn Hv; eauto using not_hasvalue_bot, not_raises_exception_bot.
    + apply bottom_approx_any.
      allrw <- @isprog_eq.
      eauto with program.
  - simpl.
    unfold cequivc.
    allunfold @mk_pi2.
    allunfold @mk_apply.
    simpl.
    unfold_all_mk2.
    allunfold @mk_spread.
    cequivl_cstepc.
    apply reduces_to_implies_cequiv in Hyp;
    [|repeat(decomp_progc3); eauto with program].
    rwg Hyp. clear Hyp.
    unfold apply_bterm. simpl.
    rw @lsubst_lsubst_aux_prog_sub;
      [|prove_sub_range_sat; eauto with program].
    simpl.
    cequivl_cstepc.
    apply reduces_to_implies_cequiv in Hyp;
    [| repeat(decomp_progc3);
       eauto with program;
       rw @lsubst_aux_trivial2;auto;
        prove_sub_range_sat; eauto with program].
    rwg Hyp. clear Hyp.
    unfold apply_bterm. simpl.
    unfold lsubst. simpl.
    rw @lsubst_aux_trivial2;auto;
       [| prove_sub_range_sat; eauto with program].
    repeat(prove_cequiv); eauto with program.
    repeat(decomp_progc3); auto.
Qed.

Lemma mkc_pi2_get_cterm {o}:
  forall t : @CTerm o,
  get_cterm (mkc_pi2 t)
  = mk_pi2 (get_cterm t).
Proof.
  intro t.
  destruct_cterms.
  simpl.
  refl.
Qed.

Lemma mkc_pi1_get_cterm {o} :
  forall t : @CTerm o,
  get_cterm (mkc_pi1 t)
  = mk_pi1 (get_cterm t).
Proof.
  intro t.
  destruct_cterms.
  simpl.
  refl.
Qed.

Lemma crary_f''_fapprox_pi1 {o} : forall lib (f f' : @NTerm o),
  let f'' := crary_f'' f f' in
  isprogram f
  -> isprogram f'
  -> forall j,
       cequiv lib (mk_pi1 (fix_approx j f''))
              (fix_approx j f).
Proof.
  introv Hpf Hpf'. simpl.
  induction j.
  - remember @mkc_pi2 as xx.
    simpl.
    subst xx. split.
    + apply approx_assume_hasvalue;
      eauto with program;[].
      introv Hv. provefalse.
      apply hasvalue_like_implies_or in Hv; auto; eauto with program.
      dorn Hv.
      * apply if_hasvalue_spread in Hv; auto;
        [| repeat (decomp_progc3); eauto with program].
        dorn Hv; eauto using not_hasvalue_bot, not_raises_exception_bot.
      * apply if_raises_exception_spread in Hv; auto;
        [| repeat (decomp_progc3); eauto with program].
        dorn Hv; eauto using not_hasvalue_bot, not_raises_exception_bot.
    + apply bottom_approx_any.
      allrw <- @isprog_eq.
      eauto with program.
  - simpl.
    unfold cequivc.
    allunfold @mk_pi1.
    allunfold @mk_apply.
    simpl.
    unfold_all_mk2.
    allunfold @mk_spread.
    cequivl_cstepc.
    apply reduces_to_implies_cequiv in Hyp;
    [|repeat(decomp_progc3); eauto with program].
    rwg Hyp. clear Hyp.
    unfold apply_bterm. simpl.
    rw @lsubst_lsubst_aux_prog_sub;
      [|prove_sub_range_sat; eauto with program].
    simpl.
    cequivl_cstepc.
    apply reduces_to_implies_cequiv in Hyp;
    [| repeat(decomp_progc3);
       eauto with program; 
       rw @lsubst_aux_trivial2;auto; 
        prove_sub_range_sat; eauto with program].
    rwg Hyp. clear Hyp.
    unfold apply_bterm. simpl.
    unfold lsubst. simpl. 
    rw @lsubst_aux_trivial2;auto;
       [| prove_sub_range_sat; eauto with program].
    repeat(prove_cequiv); eauto with program.
    repeat(decomp_progc3); auto.
Qed.


Lemma crary_f''_fapprox_pi2c {o} : forall lib (f f' : @CTerm o),
  let f'' := mkc_crary_f'' f f' in
  forall j, cequivc lib (mkc_pi2 (fix_approxc j f''))
          (fix_approxc j f').
Proof.
  simpl. intros. dest_ctermsn.
  unfold cequivc.
  rw @fix_approxc_removec.
  rw @mkc_pi2_get_cterm.
  unfold mkc_crary_f''.
  rw @fix_approxc_removec.
  apply crary_f''_fapprox_pi2;
  eauto with program.
Qed.

Lemma crary_f''_fapprox_pi1c {o} : forall lib (f f' : @CTerm o),
  let f'' := mkc_crary_f'' f f' in
  forall j, cequivc lib (mkc_pi1 (fix_approxc j f''))
          (fix_approxc j f).
Proof.
  simpl. intros. dest_ctermsn.
  unfold cequivc.
  rw @fix_approxc_removec.
  rw @mkc_pi1_get_cterm.
  unfold mkc_crary_f''.
  rw @fix_approxc_removec.
  apply crary_f''_fapprox_pi1;
  eauto with program.
Qed.
(* !! MOVE *)
Lemma resp_cequiv_approx {o} : forall lib, respects2 (cequiv lib) (@approx o lib).
Proof.
   split; introv; introv Hc Ha; repnud Hc;eauto with slow.
Qed.
Hint Resolve resp_cequiv_approx : respects.

Lemma approx_open_bterm_refl {o} :
  forall lib bt,
  @bt_wf o bt
  -> approx_open_bterm lib bt bt.
Proof.
   intros. apply alphabt_blift; simpl; dands; (introns XX); 
    allsimpl; exrepnd;
    eauto 2 with slow.
Qed.



Lemma cequiv_crary_approximations1 {o} : forall lib (f f' : @CTerm o),
  let f'' := mkc_crary_f'' f f' in
  (cequivc lib (mkc_pi1 (mkc_fix f'')) ((mkc_fix f))).
Proof.
  simpl.
  introv.
  unfold cequivc.
  pose proof (substc_cvterm_pi1 (mkc_fix (mkc_crary_f'' f f'))) as Hs.
  dest_ctermsn.
  simpl.
  apply_eq (@get_cterm o) H Hn. allsimpl.
  clear Hs.
  allrw @isprog_eq.
  split.
  - rw <- Hn. unfold subst. apply crary5_9; auto;
    eauto with program.
    unfold apply_bterm.
    intro n. simpl.
    rw @lsubst_lsubst_aux_prog_sub;
    [| prove_sub_range_sat ; eauto with program].
    simpl.
    allrw @fold_nobnd.
    rw @fold_spread.
    rw @fold_pi1.
    pose proof (crary_f''_fapprox_pi1 lib f f' fpr f'pr n) as XX.
    rwg XX.
    apply fix_approx_ub; auto.
  - apply crary5_9_no_context; auto.
    intro n. simpl.
    pose proof (crary_f''_fapprox_pi1 lib f f' fpr f'pr n) as XX.
    symmt XX.
    rwg XX.
    unfold mk_pi1, mk_spread, nobnd.
    repeat(prove_approx);
    repeat(decomp_progc3);eauto with program.
    + apply fix_approx_ub; eauto with program.
    + apply approx_open_bterm_refl. auto.
Qed.

Lemma cequiv_crary_approximations2 {o} : forall lib (f f' : @CTerm o),
  let f'' := mkc_crary_f'' f f' in
  (cequivc lib (mkc_pi2 (mkc_fix f'')) ((mkc_fix f'))).
Proof.
  simpl.
  introv.
  unfold cequivc.
  pose proof (substc_cvterm_pi2 (mkc_fix (mkc_crary_f'' f f'))) as Hs.
  dest_ctermsn.
  simpl.
  apply_eq (@get_cterm o) H Hn. allsimpl.
  clear Hs.
  allrw @isprog_eq.
  split.
  - rw <- Hn. unfold subst. apply crary5_9; auto;
    eauto with program.
    unfold apply_bterm.
    intro n. simpl.
    rw @lsubst_lsubst_aux_prog_sub;
    [| prove_sub_range_sat ; eauto with program].
    simpl.
    allrw @fold_nobnd.
    rw @fold_spread.
    rw @fold_pi2.
    pose proof (crary_f''_fapprox_pi2 lib f f' fpr f'pr n) as XX.
    rwg XX.
    apply fix_approx_ub; auto.
  - apply crary5_9_no_context; auto.
    intro n. simpl.
    pose proof (crary_f''_fapprox_pi2 lib f f' fpr f'pr n) as XX.
    symmt XX.
    rwg XX.
    unfold mk_pi2, mk_spread, nobnd.
    repeat(prove_approx);
    repeat(decomp_progc3);eauto with program.
    + apply fix_approx_ub; eauto with program.
    + apply approx_open_bterm_refl. auto.
Qed.

(* Based on Carl Krary's ideas *)

(* end hide *)

(** %\noindent% The above rule is not very useful.
    For notational brevity, we will often denote [mk_partial T] by
    $\overline{T}$.
    Intuitively,
    to prove typehood of partial functions from numbers to
    numbers using the above rule, we would have to show that
    the type $\mathbb{N} \rightarrow \overline{\mathbb{N}}$
    is as mono type.
    However, this is not true as we will see below.
    

    As a concrete example, suppose 
    we wish to prove that the 3x+1 function
    is in the type $\mathbb{N} \rightarrow \overline{\mathbb{N}}$.
    The function can be represented in Nuprl as
    $fix (f3x)$, where $f3x$ is 
    $\lambda f. \lambda n. if\; n\; =\; 0\; then\; 1\; else \;
        if \; n\; mod\; 2=0 \; then\; f\;\frac{n}{2}\; else\; f\;(3 \times n+1)$
    Since $fix (f3x)$ reduces to a lambda expression (value) after one
    step of computation, by the termination rule it suffices to show that
    it is in the type
    %\ensuremath{\overline{\mathbb{N} \rightarrow \overline{\mathbb{N}}}}%.
    However, the type %\ensuremath{\mathbb{N} \rightarrow \overline{\mathbb{N}}}%
     is not Mono.
    Monohood (see  [mono_inhabited_implies] above)
     is not closed under the partial type constructor.
    $\lambda n. \bot$ is clearly a member of the type 
    %\ensuremath{\mathbb{N} \rightarrow \overline{\mathbb{N}}}%,
    and we have [approx] $(\lambda n. \bot)$ $(\lambda n. Ax)$,
    but  $\lambda n. Ax$ is not even a member of the type
    %\ensuremath{\mathbb{N} \rightarrow \overline{\mathbb{N}}}%
    because $Ax$ is a value that is not a number. Next, we will discuss
    two approaches to get around this issue.

    We were able to prove a stronger version of the fixpoint induction
    principle ([rule_fixpoint_principle_context] below) 
    which can be stated just in terms of the Mono property.
    This rule is enough to prove the typehood of many partial functions
    like the one above. So far, this stronger version sufficed for
    all our uses.
    Monohood is much easier to understand than admissibility.

    Crary introduced a weaker predicate on types, called admissibility
    to deal with these cases. Unlike Monohood, for any type [T],
    [mkc_admiss T] implies [mkc_admiss (mk_partial T)]. Below,
    We will prove another flavour of the fixpoint induction rule
    where [mkc_mono T] is replaced by [mkc_admiss T].
    
*)

(* begin hide *)

Lemma respects_member_alpha {o} :
  forall lib, respects2 alphaeqc (@member o lib).
Proof.
  split; introv Ha Hm;
  eauto with nequality.
Qed.

Hint Resolve respects_member_alpha : respects.

Ltac lsubst_tac_fun := 
  let Xrr := fresh "Xrr" in
  repeat match goal with
  [ H: context [lsubstc (mk_fun ?A ?A) ?wfA ?s ?wcA ] , Aw: wf_term ?A, Ac : cover_vars ?A ?s |- _]
      =>pose proof (lsubstc_mk_fun A A s Aw Aw wfA Ac Ac wcA)  as Xrr;
        rwhg Xrr H; clear Xrr 
  end;
  repeat match goal with
  [ H: context [lsubstc (mk_fun ?A ?B) ?wab ?s ?cab ] 
    , Aw: wf_term ?A, Bw: wf_term ?B, Ac : cover_vars ?A ?s,
       Bc : cover_vars ?B ?s |- _]
      => pose proof (lsubstc_mk_fun A B s Aw Bw wab Ac Bc cab)  as Xrr;
        rwhg Xrr H; clear Xrr 
  end.

Ltac hide_cov_wf :=
repeat match goal with
[H : wf_term _ |- _ ] => hide_hyp H
|[H : cover_vars _ _ |- _ ] => hide_hyp H
end.

Lemma fix_approxc_approxc {o} : forall lib f G n,
  @approxc o lib (mkc_apply G (fix_approxc n f))
   (mkc_apply G (mkc_fix  f)).
Proof.
  intros. unfold approxc.
  destruct f as [f fp].
  destruct G as [G Gp]. allsimpl.
  match goal with
  [|- context [ fix_approxc n ?ff ] ] => remember (fix_approxc n ff) as fac
  end.
  apply (f_equal get_cterm) in Heqfac.
  destruct fac as [fa fap].
  allsimpl.
  rw @fix_approxc_removec in Heqfac.
  subst fa.
  allrw @isprog_eq.
  apply (fix_approx_ub lib) in fp. simpl in fp.
  specialize (fp n). allsimpl.
  apply (implies_approx_apply lib G G) in fp; auto.
  eauto 2 with slow.
Qed.

(* end hide *)


(** %\noindent% Here is a version of fixpoint induction rule that makes it
    easy to prove typehood of partial functions.
    Unlike the previous rule, [mk_fix f] now occurs in a context.
    [U] denotes this context. This
    rule is stated in terms of the more intuitive monohood property. *)

(**
 Fixpoint principle w/ context:
<<
   H |- U fix(f) = U fix(g) in partial S

     By fixpointPrinciple_context

     H |- f = g in T -> T
     H |- Mono S
     H |- mk_bot = mk_bot in T
     H |- U = U in T -> partial S
>>

*)

Definition rule_fixpoint_principle_context {o}
           (f g U T S: @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
        (mk_equality 
            (mk_apply U (mk_fix f)) 
            (mk_apply U (mk_fix g)) 
            (mk_partial S))))
    [ 
      mk_baresequent H (mk_conclax (mk_equality f g (mk_fun T T))),
      mk_baresequent H (mk_conclax (mk_mono S)),
      mk_baresequent H (mk_conclax (mk_equality mk_bot mk_bot T)),
      mk_baresequent H (mk_conclax 
                          (mk_equality U U (mk_fun T (mk_partial S))))
    ]
    [].



Lemma fixpoint_induction_context_helper {o} :  forall lib Ua Ub fa fb T S,
  @member o lib mkc_axiom (mkc_mono S)
  -> member lib mkc_bot T
  -> equality lib fa fb (mkc_fun T T)
  -> equality lib Ua Ub (mkc_fun T (mkc_partial S))
  -> equality lib (mkc_apply Ua (mkc_fix fa)) 
              (mkc_apply Ub (mkc_fix fb)) 
              (mkc_partial S).
Proof.
  introv Hmon Hbot Hfeq Heqc.
  (* applydup inhabited_implies_tequality in Hfeq.
  apply @tequality_mkc_fun_l in Hfeq0.*)
  applydup @inhabited_implies_tequality in Heqc.
  apply @tequality_mkc_fun in Heqc0.
  repnd. unfold inhabited_type in Heqc0.
  dimp (Heqc0);[eexists; eauto; fail|]. clear Heqc0.
  duplicate Hfeq.
  pose proof (equal_chains_equal_fun_gen _ _ _ _ Hfeq Hbot) as Hfneq.
  clear Hfeq.
  applydup (fix_converges_equal_fun_iff_context lib fa fb Ua Ub T S) in Hfeq0; auto.
  apply equality_in_mkc_partial; dands; auto;[].
  clear Hfeq1. introv Hcv.
  apply fixc_compactness_ccc in Hcv.
  exrepnd.
  specialize (Hfneq n).
  apply equality_in_fun in Heqc.
  repnd.
  apply Heqc in Hfneq.
  apply equality_in_mkc_partial in Hfneq.
  repnd.
  clear Hfneq1.
  apply_clear Hfneq in Hcv0.
  apply equality_in_mkc_mono in Hmon.
  exrepnd.
  repnud Hmon0.
  allunfold @equality.
  exrepnd.
  equality_unique.
  exists eq.
  dands; auto;[].
  apply nuprl_pers_are_nice in Hmon3.
  clear Heqc Hcv0 Hfneq0 Hfeq1 Hfeq0 hyp Heqc1 Heqc 
    Heqc2 Heqc0 Hbot Hmon1 Hmon2 .
  eauto with nequality.
  pose proof (fix_approxc_approxc lib fa Ua n) as Ha.
  pose proof (fix_approxc_approxc lib fb Ub n) as Hb.
  apply Huniq in Hcv1.
  apply Huniq.
  duplicate Hcv1.
  duplicate Hcv1 as Heqb.
  apply (nice_per_prop1 _ _ _ _ Hmon3) in Hcv1.
  apply Hmon0 in Ha; auto.
  apply (nice_per_prop1 _ _ _ _ Hmon3) in Hcv1.
  duplicate Hmon3 as Hn.
  repnud Hn.
  apply Hn0 in Hcv0.
  apply (nice_per_prop1 _ _ _ _ Hmon3) in Hcv0.
  apply Hmon0 in Hb; auto.
  repnud Hn1. repnud Hn0.
  clear Hn Hcv1 Hcv0 Huniq Hmon0 Hmon3.
  eauto 4.
Qed.

Hint Resolve equality_respects_cequivc : nequality.

Theorem rule_fixpoint_principle_context_true {o} :
  forall lib (f g U T S: NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_fixpoint_principle_context
                 f g U T S
                 H).
Proof.
  unfold rule_fixpoint_principle_context, rule_true, closed_type_baresequent, closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  (* We prove the well-formedness of things *)
  destruct Hyp as [ wsa Hypa ].
  destruct Hyp0 as [ wsb Hypb ].
  destruct Hyp1 as [ wsc Hypc ].
  destruct Hyp2 as [ wsd Hypd ].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).


  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  repeat match goal with
             [ Hypa : sequent_true _ _ |- _ ] =>
             vr_seq_true_ltac Hypa;
               generalize (Hypa s1 s2 eqh sim); clear Hypa; intro Hypa; exrepnd
         end.
  lsubst_tac.
  allrw @tequality_mono.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  apply tequality_mkc_equality_sp_eq in Hypd0; repnd; auto;[].
  apply tequality_mkc_equality_sp_eq in Hypa0; repnd; auto;[].
  apply tequality_mkc_equality_sp_eq in Hypc0; repnd; auto;[].
  lsubst_tac.

  allrw @member_eq.

  hide_cov_wf.
  match goal with
  [H: context [lsubstc T ?w s1 ?c] |- _ ] =>
    remember (lsubstc T w s1 c) as Ts1
  end.
  match goal with
  [H: context [lsubstc T ?w s2 ?c] |- _ ] =>
    remember (lsubstc T w s2 c) as Ts2
  end.

  match goal with
  [H: context [lsubstc S ?w s1 ?c] |- _ ] =>
    remember (lsubstc S w s1 c) as Ss1
  end.
  match goal with
  [H: context [lsubstc S ?w s2 ?c] |- _ ] =>
    remember (lsubstc S w s2 c) as Ss2
  end.

  match goal with
  [H: context [lsubstc U ?w s1 ?c] |- _ ] =>
    remember (lsubstc U w s1 c) as Us1
  end.
  match goal with
  [H: context [lsubstc U ?w s2 ?c] |- _ ] =>
    remember (lsubstc U w s2 c) as Us2
  end.


  assert (forall Ua Ub fa fb,
            equality lib fa fb (mkc_fun Ts1 Ts1)
            -> equality lib Ua Ub (mkc_fun Ts1 (mkc_partial Ss1))
            -> equality lib (mkc_apply Ua (mkc_fix fa))
                        (mkc_apply Ub (mkc_fix fb))
                        (mkc_partial Ss1)) as Hxx.
  { intros. apply @tequality_refl in Hypb0. repnud Hypb0. exrepnd.
    eapply fixpoint_induction_context_helper; eauto.
  }

  dands; auto;[].

  rename Hypd2 into Hdfunc.
  apply @tequality_mkc_fun in Hdfunc.
  repnd.
  autodimp Hdfunc hyp;[eexists; eauto|];[].
  apply tequality_mkc_equality_if_equal; dands; auto.
Qed.

(** Now, we discuss the second solution which was given by Crary.
    The type [(mkc_admiss A)] is inhabited (by [mkc_axiom]) if the PER
    of the type [A] satisfies the [admissible_equality]
    condition. The definition of [admissible_equality]
    can be found in Sec. %\ref{sec:type:ind:per}% if you
    are reading the technical report.
 *)


(**

  Fixpoint principle for Admissible types:
<<
   H |- fix(f1) = fix(f2) in partial(T)

     By fixpointPrinciple

     H |- f1 = f2 in partial(T)->partial(T)
     H |- Admiss(T)
>>
*)

Definition rule_fixpoint_principle_admiss {o}
           (f1 f2 T : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
        (mk_equality (mk_fix f1) (mk_fix f2) (mk_partial T))))
    [ mk_baresequent H 
        (mk_conclax (mk_equality f1 f2 
            (mk_fun (mk_partial T) (mk_partial T)))),
      mk_baresequent H (mk_conclax (mk_admiss T))
    ]
    [].

(** In order to use the lemma [fixpoint_induction_general]
    to prove the above rule, we need to prove the following
    lemma. The proof is tricky and uses the
    least upper bound principle ([crary5_9_no_context]).
    Intuitively, the difficulty is that
    [fixpoint_induction_suff] is about partial
    approximations of two functions, while
    [admissible_equality] is about partial
    approximations of a single function in
    two contexts. The idea behind this proof
    is due to Crary.

*)
Theorem fixpoint_induction_suff_if2 {o} :
  forall lib (eq : per(o)),
  respects2 (cequivc lib) eq
  -> admissible_equality eq
  -> fixpoint_induction_suff eq.
Proof.
  introv Hres Had.
  repnud Had. unfolds_base.
  introv Hcfs.
  remember (mkc_crary_f'' f f') as f''.
  specialize (Had nvarx cvterm_nvarx_pi1 cvterm_nvarx_pi2 f'').
  unfold subst_fix_eqc in Had.
  unfold cofinite_subst_fapprox_eqc in Had.
  unfold subst_fixc in Had.
  unfold subst_fapproxc in Had.
  allrw @substc_cvterm_pi1.
  allrw @substc_cvterm_pi2.
  assert (cequivc lib (mkc_pi1 (mkc_fix f'')) ((mkc_fix f))) as H1xx by
  (subst f''; apply cequiv_crary_approximations1).
  assert (cequivc lib (mkc_pi2 (mkc_fix f'')) ((mkc_fix f'))) as H2xx by
  (subst f''; apply cequiv_crary_approximations2).
  symmt H1xx.
  symmt H2xx.
  rwg H1xx. rwg H2xx. apply Had.
  exrepnd. exists j.
  introv Hgt.
  allrw @substc_cvterm_pi1.
  allrw @substc_cvterm_pi2.
  apply Hcfs0 in Hgt.
  clear H2xx H1xx Hcfs0 j Had.
  subst f''.
  pose proof (crary_f''_fapprox_pi1c lib f f' k) as Xf.
  pose proof (crary_f''_fapprox_pi2c lib f f' k) as Xf'.
  allsimpl.
  rwg Xf.
  rwg Xf'.
  auto.
Qed.

(* begin show *)
(** The following Corrollary corresponds to Crary's Theorem 5.14 %\cite{Crary:1998}% *)

Corollary fixpoint_induction_helper_admiss {o} :  forall lib (fa fb T : @CTerm o),
   member lib mkc_axiom (mkc_admiss T)
  -> equality lib fa fb (mkc_fun (mkc_partial T) (mkc_partial T))
  -> equality lib (mkc_fix fa) (mkc_fix fb) (mkc_partial T).
Proof.
  introv Hm Hfeq.
  apply equality_in_mkc_admiss in Hm.
  exrepnd.
  apply fixpoint_induction_general with (eqT:=eqa); auto.
  apply (fixpoint_induction_suff_if2 lib); auto.
  apply nice_per_respects_cequivc.
  eapply nuprl_pers_are_nice;eauto.
Qed.
(* end show *)

Corollary rule_fixpoint_principle_admiss_true {o} :
  forall lib (f1 f2 T : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_fixpoint_principle_admiss
                 f1 f2 T
                 H).
Proof.
  unfold rule_fixpoint_principle_admiss, rule_true, closed_type_baresequent, closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  (* We prove the well-formedness of things *)
  destruct Hyp as [ wsa Hypa ].
  destruct Hyp0 as [ wsb Hypb ].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in Hypa.
  generalize (Hypa s1 s2 eqh sim). clear Hypa. intro Hypa. exrepnd.

  vr_seq_true in Hypb.
  generalize (Hypb s1 s2 eqh sim); clear Hypb; intro Hypb; exrepnd.
  lsubst_tac.
  rw @tequality_admiss in Hypb0.
  allrw @member_eq.
  apply member_equality_iff in Hypa1.
  apply tequality_mkc_equality_sp_eq in Hypa0;auto;[];repnd.
  lsubst_tac.

  apply @tequality_mkc_fun_l in Hypa2.
  remember (lsubstc T w0 s1 c0) as Ts1.

  assert (forall fa fb,
            equality lib fa fb (mkc_fun (mkc_partial Ts1) (mkc_partial Ts1))
            -> equality lib (mkc_fix fa) (mkc_fix fb) (mkc_partial Ts1)) as Hxx by
    (introv; apply fixpoint_induction_helper_admiss; auto).

  dands; auto;[].
  apply @tequality_mkc_equality_if_equal; dands; auto.
Qed.



(** Crary proved the admissibility and monohood of many types
    (see %\cite[Sec. 5.3]{Crary:1998}%). The collection of admissible types
  includes [mkc_base], [mkc_int].
  Admissibility is also closed under many type constructors:
  e.g. dependent functions, independent pairs, partial types.
  Unlike above, the type [mkc_base] is not a Mono type.
  Also, Monohood is not closed under the partial type
  constructor, but is closed under dependent pairs.
  The next two subsubsections deal with the characterization of
  Mono and Admissible types, respectively.
*)
