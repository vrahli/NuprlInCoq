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


Require Export cequiv.
Require Export sqle.
Require Export subst_props.
Require Export library_alpha.
Require Export computation8.
Require Export terms5.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(** [approx] is a preorder on closed terms 
(see lemmas [approx_refl] and [approx_trans] above in this section).
In this subsection we will formalize some domain theoretic properties
of this preorder. We will prove that it has a least element (upto [cequiv]).
We will define finite approximations of a term of the form
[mk_fix f] and formalize Crary's %\cite{Crary:1998}% proof
that [mk_fix f] is the least upperbound of its approximations.
We will also formalize his Compactness property which says that
if a term of the form [mk_fix f] converges, then one of it's finite
approximations also converges. We had to slightly adapt Crary's proofs
because our operations semantics for [mk_fix f] is 
slightly different. These properties will be used in 
Sec.%\ref{sec:rules:partial}% to
prove rules that talk about membership of terms of the form
[mk_fix f] in partial types.
*)

(** First we recap some earlier definitions that
    will be used a lot in this section.
[[
Definition mk_fix (f : NTerm) :=
  oterm (NCan NFix) [ bterm [] f ].

Definition mk_id := mk_lam nvarx (vterm nvarx).

Definition mk_lam (v : NVar) (b : NTerm) :=
  oterm (Can NLambda) [bterm [v] b].

Definition mk_bottom := mk_fix mk_id.

Definition mk_bot := mk_bottom.

]] 

%\noindent% As the name suggests, the following function 
  constructs the $n^{th}$  approximation to [mk_fix f]. *)
 
Fixpoint fix_approx {o} (n : nat) (f : NTerm) : @NTerm o :=
match n with
| 0 => mk_bottom
| S n => mk_apply f (fix_approx n f)
end.

Lemma fix_approx_program {o} : forall  f,
  @isprogram o f
  -> forall n, isprogram (fix_approx n f).
Proof.
  introv Hpr.
  induction n;simpl;repeat(decomp_progc);sp; split; sp.
Qed.





Hint Resolve fix_approx_program : slow.
Hint Resolve fix_approx_program : isprogram.


Definition is_chain {T : Type} (R : @bin_rel T) (tf : nat -> T) : [univ] :=
  forall n, R (tf n) (tf (S n)).


Definition is_upper_bound {T : Type} (R : @bin_rel T) (tf : nat -> T) (t: T) : [univ] :=
  forall n, R (tf n) t.

Definition is_approx_ub {o} (lib : @library o) :=is_upper_bound (approx lib).
Definition is_approx_chain {o} (lib : @library o) := is_chain (approx lib).

(** %\noindent% The following lemma is an easy consequence of 
    the congruence of [approx] *)
  
Lemma is_approx_chain_fix_aprox {o} : forall lib (f : @NTerm o),
  isprogram f
  -> is_approx_chain lib (fun n => fix_approx n f).
Proof.
  introv Hpr. unfolds_base.
  introv.
  induction n as [| n Hind].
  - simpl. apply bottom_approx_any. repeat(decomp_progc); sp. split; sp.
  - remember (S n) as sn. simpl. remember (mk_apply f (fix_approx sn f)) as XX.
    rewrite Heqsn. simpl. subst XX. clear Heqsn.
    unfold_all_mk. unfold mk_apply, nobnd.
    repeat(prove_approx);sp; eauto 2 with slow.
Qed.


(** %\noindent% The following lemma says that [mk_fix f] is
    an upper bound of its approximations. 
*)
  
Lemma fix_approx_ub {o} : forall lib f,
  @isprogram o f
  -> is_approx_ub lib (fun n => fix_approx n f) (mk_fix f).
Proof.
  introv Hpr. unfolds_base.
  introv.
  induction n as [| n Hind].
  - simpl. apply bottom_approx_any. repeat(decomp_progc); sp.
  - simpl. apply approx_trans with (b:= (mk_apply f (mk_fix f))).
    + repeat(prove_approx); eauto 2 with slow.
    + apply fix_unfold_approx_fix;sp.
Qed.

(** One of the main goals of this section is to prove
    that it is infact the least upper bound (upto [cequiv]).
    We will hereby call it the LUB principle(theorem 5.9 in %\cite{Crary:1998}%).
    The proof is similar in spirit to the one in %\cite{Crary:1998}%.
    However, our definition of the operational semantics([compute_step])
    of [mk_fix] is different from his. As mentioned before in the section
    %\ref{sec:comp:step:NFix}%, in our computation system,
    [mk_fix f] computes to [mk_apply f (mk_fix f)] only
    if [f] is canonical. In other words, unlike in his system,
    the first argument if a [NFix] is always principal,
    It evaluates [f] further otherwise.

    When we made this innocuous looking change (months before), we did not think
    that these proofs will require some non-trivial changes.
    Intead of reverting to the old semantics by fixing our previous
    Coq proofs that were simplified because the first argument
    is now uniformly principal for all [NonCanonicalOp]s, we decided
    hunt for a proof of the LUB principle that holds in this new
    operational semantics. We were successful in this endeavour.

    To prove the LUB principle, Crary first proves 2 lemmas (5.7 and 5.8)
    Although both the proof and statement of his lemma 5.7 holds
    for our system, lemma 5.8 probably does not hold for our system
    (TODO : prove a counterexample). However, a weaker version
    of it holds. To prove the LUB principle for our system we proved
    a strengthened version of his lemma 5.7, and a weak version of his lemma
    5.8. Along with some other new lemmas about our computation system,
    we could then prove Crary's LUB principle (and the compactness principle below).
 *)
    
(** %\noindent% To begin, here is a sneak peek at the 
   statements of the LUB principle and Compactness principle
   which we wish to prove along the lines of Crary.
*)

(* begin show *)
Theorem crary5_9_LUB {o} : forall lib f t e,
  @isprogram o f
  -> is_approx_ub lib (fun n => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t
  -> approx lib (apply_bterm (bterm [nvarx] e) [mk_fix f]) t.
Abort.

(** %\noindent%  Compactness says that if a term with a subterm of the form
   [mk_fix f] then there (constructively) exists a number [n] such that
   replacing that subterm by its $n^{th}$ finite approximation also conveges.
*)

Theorem fix_compactness {o} : forall lib f e,
  let tf := (apply_bterm (bterm [nvarx] e) [@mk_fix o f]) in
  isprogram f
  -> isprogram tf
  -> hasvalue lib tf
  -> {n : nat $ let tfa := (apply_bterm (bterm [nvarx] e) [fix_approx n f]) in
          hasvalue lib tfa}.
Abort.
(* end show *)

(**
   A key use of Compactness will be in proving
   for certain types [T] (called admissible types), that if a [f] is in the
    function type
   [mk_partial T -> mk_partial T], then [mk_fix f]
   is in the type [mk_partial T].
   Intuitively, [t] $\in$ [mk_partial T] iff
   ([hasvaue t -> t] $\in$ [T]). We defer the proof of this rule till
    section %\ref{sec:rules:partial}% where we will we have a formal definition
    of our type system. The goal of the rest
    of this section to formalize the proofs of Compactness
    and the LUB property.
*)

(* begin hide *)

Definition single {T} (x:T) := [x].

Ltac disjoint_app :=
match goal with
| [  |- disjoint _ (_ ++ _) ] => apply disjoint_app_r;split
| [  |- disjoint (_ ++ _) _ ] => apply disjoint_app_l;split
| [  |- disjoint _ (_ :: _) ] => apply disjoint_cons_r;split
| [  |- disjoint (_ :: _) _ ] => apply disjoint_cons_l;split
| [  |- disjoint _ _ ] => (sp;fail  || apply disjoint_sym; sp;fail)
(** important to leave it the way it was .. so that repeat progress won't loop*)
| [ H: (disjoint  _ []) |- _ ] => clear H
| [ H: (disjoint  [] _) |- _ ] => clear H
| [ H: disjoint _ (_ ++ _) |- _ ] => apply disjoint_app_r in H;repnd
| [ H: disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H;repnd
| [ H: disjoint _ (?v :: []) |- _ ] => fold (single v) in H
| [ H: disjoint (?v :: []) _ |- _ ] => fold (single v) in H
| [ H: disjoint _ (_ :: _) |- _ ] => rewrite cons_as_app in H
| [ H: disjoint (_ :: _) _ |- _ ] => rewrite cons_as_app in H
| [ H: !(disjoint  _ []) |- _ ] => provefalse; apply H; apply disjoint_nil_r
| [ H: !(disjoint  [] _) |- _ ] => provefalse; apply H; apply disjoint_nil_l
end.
(*
Ltac disjoint_cons :=
match goal with
end. *)

Ltac allunfoldsingle :=
match goal with
[ H: context[single ?v] |- _ ] => unfold single in H
end.

Ltac disjoint_consl :=
match goal with
| [  |- disjoint _ (_ ++ _) ] => apply disjoint_app_r;split
| [  |- disjoint (_ ++ _) _ ] => apply disjoint_app_l;split
| [  |- disjoint (_ :: _) _ ] => apply disjoint_cons_l;split
| [  |- disjoint _ _ ] => (sp;fail  || apply disjoint_sym; sp;fail)
(** important to leave it the way it was .. so that repeat progress won't loop*)
| [ H: disjoint _ (_ ++ _) |- _ ] => apply disjoint_app_r in H;sp
| [ H: disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H;sp
| [ H: disjoint (_ :: _) _ |- _ ] => apply disjoint_cons_l in H;sp
| [ H: !(disjoint  _ []) |- _ ] => provefalse; apply H; apply disjoint_nil_r
| [ H: !(disjoint  [] _) |- _ ] => provefalse; apply H; apply disjoint_nil_l
| [ H: (disjoint  _ []) |- _ ] => clear H
| [ H: (disjoint  [] _) |- _ ] => clear H
end.


Lemma memvar_single : forall v, (memvar v [v]) =true.
Proof.
  unfold memvar. simpl. introv. cases_if; cpx.
Qed.

Lemma memvar_single_false : forall vx vy, 
   vx  <> vy -> (memvar vx [vy]) =false.
Proof.
  unfold memvar. simpl. introv. cases_if; cpx.
Qed.

Hint Rewrite <- beq_var_refl : slow.
Hint Rewrite memvar_single : slow.

Ltac prove_sub_range_sat2 :=
  let Hin := fresh "Hin" in
  introv Hin; simpl in Hin;
   repeat(in_reasoning); subst;auto.

Definition compute_1_step_eq {o} :
  forall lib (t : @NTerm o),
    compute_1_step lib t
    = match t with
        | sterm _ => cfailure "term is already a value" t
        | oterm (Can _) _ => cfailure "term is already a value" t
        | oterm Exc _ => cfailure "term is already a exception" t
        | _ => compute_step lib t
      end.
Proof. sp. Qed.

Lemma compute_1_step_is_computes_in_1step {p} :
  forall lib (a b : @NTerm p),
    (compute_1_step lib a = csuccess b) <=> computes_in_1step lib a b.
Proof.
  introv.
  rw @compute_1_step_eq; destruct a; try (destruct o); split; intro k;
  try (complete (inversion k));
  try (complete (constructor; auto));
  try (complete (inversion k; auto)).
Qed.

Lemma lsubst_bterm_aux_trivial_cl_term {o} :
  forall (b : @BTerm o) sub,
    disjoint (free_vars_bterm b) (dom_sub sub)
    -> lsubst_bterm_aux b sub = b.
Proof.
  introv disj; destruct b as [l t]; allsimpl.
  f_equal.
  rw @lsubst_aux_trivial_cl_term; auto.
  rw <- @dom_sub_sub_filter.
  apply disjoint_remove_nvars_l; auto.
Qed.

Lemma cl_isprog_vars_lsubst_aux_implies {o} :
  forall (t : @NTerm o) vs sub,
    cl_sub sub
    -> isprog_vars vs (lsubst_aux t sub)
    -> isprog_vars (vs ++ dom_sub sub) t.
Proof.
  introv cl isp.
  allrw @isprog_vars_eq; repnd.
  allrw @nt_wf_lsubst_aux_iff; repnd; dands; auto.
  allrw subvars_prop; introv i; allrw in_app_iff.
  destruct (in_deq _ deq_nvar x (dom_sub sub)) as [d|d]; tcsp.
  pose proof (isp0 x) as k; autodimp k hyp; tcsp.
  rw @free_vars_lsubst_aux_cl; auto.
  rw in_remove_nvars; tcsp.
Qed.

Lemma isprogram_lsubst_aux_if_isprog_vars {o} :
  forall (t : @NTerm o) (sub : Substitution),
    isprog_vars (dom_sub sub) t
    -> prog_sub sub
    -> isprogram (lsubst_aux t sub).
Proof.
  introv isp ps.
  allrw @isprog_vars_eq; repnd.
  split.
  - unfold closed.
    apply null_iff_nil; unfold null; introv i.
    rw @free_vars_lsubst_aux_cl in i; eauto 3 with slow.
    rw in_remove_nvars in i; repnd.
    rw subvars_eq in isp0; apply isp0 in i0; sp.
  - apply implies_wf_lsubst_aux; eauto 3 with slow.
Qed.

Lemma isprog_vars_lsubst_aux_if_isprog_vars {o} :
  forall (t : @NTerm o) (sub : Substitution) vs,
    isprog_vars (vs ++ dom_sub sub) t
    -> prog_sub sub
    -> isprog_vars vs (lsubst_aux t sub).
Proof.
  introv isp ps.
  allrw @isprog_vars_eq; repnd.
  split.
  - allrw subvars_eq; introv i.
    rw @free_vars_lsubst_aux_cl in i; eauto 3 with slow.
    rw in_remove_nvars in i; repnd.
    apply isp0 in i0; allrw in_app_iff; repndors; tcsp.
  - apply implies_wf_lsubst_aux; eauto 3 with slow.
Qed.

Lemma subst_utokens_aux_trivial1 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> disjoint (get_utokens t) (utok_sub_dom sub)
    -> subst_utokens_aux t sub = t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv wf disj; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      allrw disjoint_cons_l; repnd.
      allrw @wf_term_utok; subst; allsimpl.
      rw @subst_utok_if_not_in; auto.

    + allrw @wf_oterm_iff; repnd.
      f_equal.
      apply eq_map_l; introv i.
      applydup wf in i.
      destruct x as [l t]; allsimpl; f_equal.
      allrw @wf_bterm_iff.
      allrw disjoint_app_l; repnd.
      disj_flat_map; allsimpl.
      eapply ind; eauto.
Qed.

Lemma subst_utokens_trivial1 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> disjoint (get_utokens t) (utok_sub_dom sub)
    -> alpha_eq (subst_utokens t sub) t.
Proof.
  introv wf disj.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0.
  rw @subst_utokens_aux_trivial1; eauto 3 with slow.
  allapply @alphaeq_preserves_utokens.
  rw <- h1; auto.
Qed.

(* !!MOVE *)
Hint Resolve computes_in_1step_to_alpha : slow.
Hint Constructors computes_in_1step : slow.

Lemma computes_in_1step_if_isnoncan_like {o} :
  forall lib (t u : @NTerm o),
    isnoncan_like t
    -> compute_step lib t = csuccess u
    -> computes_in_1step lib t u.
Proof.
  introv isn comp.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst; tcsp.
  - apply isabs_implies in isn; exrepnd; subst; tcsp.
Qed.

Lemma computes_in_1step_alpha_fresh {o} :
  forall lib (t u : @NTerm o) v a,
    nt_wf t
    -> !LIn a (get_utokens t)
    -> computes_in_1step lib (lsubst_aux t [(v, mk_utoken a)]) u
    -> computes_in_1step_alpha lib (mk_fresh v t) (mk_fresh v (subst_utokens u [(a,mk_var v)])).
Proof.
  introv wf ni comp.
  destruct t as [x|f|op bs]; auto; try (complete (allsimpl; boolvar; inversion comp)).

  - dopid op as [can|ncan|exc|abs] Case; allsimpl;
    allrw @fold_lsubst_bterms_aux; try (complete (inversion comp)).

    + inversion comp as [? ? ? ? c|]; subst; clear comp.
      remember (get_fresh_atom (oterm (NCan ncan) bs)) as a'.
      pose proof (compute_step_subst_utoken
                    lib (oterm (NCan ncan) bs) u
                    [(v,mk_utoken a)]) as c'.
      unflsubst in c'; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp c' hyp).
      exrepnd.

      pose proof (c'0 [(v,mk_utoken a')]) as q; clear c'0; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      pose proof (get_fresh_atom_prop (oterm (NCan ncan) bs)) as gfa; rw <- Heqa' in gfa.
      repeat (autodimp q hyp); eauto 3 with slow.
      exrepnd.

      allrw @fold_subst.
      pose proof (computation2.compute_step_fresh_if_isnoncan_like
                    lib v (oterm (NCan ncan) bs)) as c''.
      autodimp c'' hyp.
      rw <- Heqa' in c''; allsimpl.
      rw q1 in c''; simpl in c''.

      pose proof (alpha_eq_subst_utokens u (subst w v (mk_utoken a)) [(a,mk_var v)] [(a,mk_var v)]) as aeq1.
      repeat (autodimp aeq1 hyp); eauto 3 with slow.

      pose proof (alpha_eq_subst_utokens s (subst w v (mk_utoken a')) [(a',mk_var v)] [(a',mk_var v)]) as aeq2.
      repeat (autodimp aeq2 hyp); eauto 3 with slow.

      pose proof (simple_alphaeq_subst_utokens_subst w v a) as aeq3.
      autodimp aeq3 hyp.
      eapply alpha_eq_trans in aeq3;[|exact aeq1]; clear aeq1.

      pose proof (simple_alphaeq_subst_utokens_subst w v a') as aeq4.
      autodimp aeq4 hyp.
      { intro i; apply c'4 in i; tcsp. }
      eapply alpha_eq_trans in aeq4;[|exact aeq2]; clear aeq2.

      exists (mk_fresh v (subst_utokens s [(a', mk_var v)])); dands.

      { constructor; auto. }

      { apply implies_alpha_eq_mk_fresh; eauto with slow. }

    + inversion comp as [|? ? ? ? c]; subst; clear comp.
      remember (get_fresh_atom (oterm (Abs abs) bs)) as a'.
      pose proof (compute_step_subst_utoken
                    lib (oterm (Abs abs) bs) u
                    [(v,mk_utoken a)]) as c'.
      unflsubst in c'; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp c' hyp).
      exrepnd.

      pose proof (c'0 [(v,mk_utoken a')]) as q; clear c'0; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      pose proof (get_fresh_atom_prop (oterm (Abs abs) bs)) as gfa; rw <- Heqa' in gfa.
      repeat (autodimp q hyp); eauto 3 with slow.
      exrepnd.

      allrw @fold_subst.
      pose proof (computation2.compute_step_fresh_if_isnoncan_like
                    lib v (oterm (Abs abs) bs)) as c''.
      autodimp c'' hyp.
      rw <- Heqa' in c''; allsimpl.
      rw q1 in c''; simpl in c''.

      pose proof (alpha_eq_subst_utokens u (subst w v (mk_utoken a)) [(a,mk_var v)] [(a,mk_var v)]) as aeq1.
      repeat (autodimp aeq1 hyp); eauto 3 with slow.

      pose proof (alpha_eq_subst_utokens s (subst w v (mk_utoken a')) [(a',mk_var v)] [(a',mk_var v)]) as aeq2.
      repeat (autodimp aeq2 hyp); eauto 3 with slow.

      pose proof (simple_alphaeq_subst_utokens_subst w v a) as aeq3.
      autodimp aeq3 hyp.
      eapply alpha_eq_trans in aeq3;[|exact aeq1]; clear aeq1.

      pose proof (simple_alphaeq_subst_utokens_subst w v a') as aeq4.
      autodimp aeq4 hyp.
      { intro i; apply c'4 in i; tcsp. }
      eapply alpha_eq_trans in aeq4;[|exact aeq2]; clear aeq2.

      exists (mk_fresh v (subst_utokens s [(a', mk_var v)])); dands.

      { constructor; auto. }

      { apply implies_alpha_eq_mk_fresh; eauto with slow. }
Qed.

Lemma computes_in_1step_ren_utokens {o} :
  forall lib (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_in_1step lib t u
    -> computes_in_1step lib (ren_utokens ren t) (ren_utokens ren u).
Proof.
  introv wf norep disj comp.
  inversion comp as [? ? ? ? x|]; subst; clear comp.
  - pose proof (compute_step_ren_utokens lib (oterm (NCan no) lbt) u ren) as h.
    repeat (autodimp h hyp).
    allsimpl; constructor; auto.
  - pose proof (compute_step_ren_utokens lib (oterm (Abs x) lbt) u ren) as h.
    repeat (autodimp h hyp).
    allsimpl; constructor; auto.
Qed.

Lemma computes_in_1step_alpha_ren_utokens {o} :
  forall lib (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_in_1step_alpha lib t u
    -> computes_in_1step_alpha lib (ren_utokens ren t) (ren_utokens ren u).
Proof.
  introv wf norep disj comp.
  allunfold @computes_in_1step_alpha; exrepnd.
  pose proof (computes_in_1step_ren_utokens lib t t2a ren) as h.
  repeat (autodimp h hyp).
  exists (ren_utokens ren t2a); dands; auto.
  apply alpha_eq_ren_utokens; auto.
Qed.

Lemma subst_utokens_aux_lsubst_aux_trivial1 {o} :
  forall (t : @NTerm o) v a,
    !LIn a (get_utokens t)
    -> subst_utokens_aux (lsubst_aux t [(v, mk_utoken a)]) [(a, mk_var v)] = t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv nia; tcsp.

  - Case "vterm".
    allsimpl; boolvar; allsimpl; tcsp.
    unfold subst_utok; allsimpl; boolvar; tcsp.

  - Case "oterm".
    rw @lsubst_aux_oterm.
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl; allrw not_over_or; repnd.
      unfold lsubst_bterms_aux.
      allrw map_map; unfold compose.
      unfold subst_utok; simpl; boolvar; tcsp.
      f_equal.
      apply eq_map_l; introv i.
      destruct x as [l t]; simpl.
      allrw in_app_iff; allrw not_over_or; repnd.
      boolvar; f_equal; simpl.

      * allrw @lsubst_aux_nil.
        apply trivial_subst_utokens_aux; simpl; apply disjoint_singleton_r.
        introv j; destruct nia; rw lin_flat_map; eexists; dands; eauto.

      * eapply ind; eauto.
        introv j; destruct nia; rw lin_flat_map; eexists; dands; eauto.

    + f_equal.
      unfold lsubst_bterms_aux.
      allrw map_map; unfold compose.
      apply eq_map_l; introv i.
      destruct x as [l t]; simpl.
      allrw in_app_iff; allrw not_over_or; repnd.
      boolvar; f_equal; simpl.

      * allrw @lsubst_aux_nil.
        apply trivial_subst_utokens_aux; simpl; apply disjoint_singleton_r.
        introv j; destruct nia; rw lin_flat_map; eexists; dands; eauto.

      * eapply ind; eauto.
        introv j; destruct nia; rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma subst_utokens_lsubst_aux_trivial1 {o} :
  forall (t : @NTerm o) v a,
    !LIn a (get_utokens t)
    -> alpha_eq (subst_utokens (lsubst_aux t [(v, mk_utoken a)]) [(a, mk_var v)]) t.
Proof.
  introv nia.

  pose proof (change_bvars_alpha_wspec [v] t) as ch; exrepnd.
  rename ntcv into u.

  pose proof (computation2.lsubst_aux_alpha_congr_same_cl_sub t u [(v, mk_utoken a)]) as aeq1.
  repeat (autodimp aeq1 hyp); eauto 3 with slow.

  pose proof (alpha_eq_subst_utokens
                (lsubst_aux t [(v, mk_utoken a)])
                (lsubst_aux u [(v, mk_utoken a)])
                [(a, mk_var v)] [(a, mk_var v)]) as aeq2.
  repeat (autodimp aeq2 hyp); eauto 3 with slow.

  eapply alpha_eq_trans;[exact aeq2|].

  unfold subst_utokens; simpl.
  rw (bound_vars_lsubst_aux_nrut_sub u [(v,mk_utoken a)] []);
    [|apply nrut_sub_cons; simpl; eexists; dands; eauto with slow; tcsp].
  boolvar; allrw disjoint_singleton_l; allrw disjoint_singleton_r; tcsp.
  rw @subst_utokens_aux_lsubst_aux_trivial1; eauto with slow.
  apply alphaeq_preserves_utokens in ch0; rw <- ch0; auto.
Qed.

Lemma subst_utokens_subst_utokens_aux {o} :
  forall (t : @NTerm o) sub,
    disjoint (bound_vars t) (free_vars_utok_sub sub)
    -> subst_utokens t sub = subst_utokens_aux t sub.
Proof.
  introv disj.
  unfold subst_utokens; boolvar; tcsp.
Qed.

Lemma bound_vars_utok_sub_eq_flat_map {o} :
  forall (sub : @utok_sub o),
    bound_vars_utok_sub sub = flat_map bound_vars (utok_sub_range sub).
Proof.
  induction sub; simpl; auto.
  destruct a; simpl; f_equal; tcsp.
Qed.

Lemma bound_vars_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) sub,
    subset (bound_vars (subst_utokens_aux t sub))
           (bound_vars t ++ bound_vars_utok_sub sub).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; auto.

  - Case "vterm".
    allsimpl; auto.

  - Case "sterm".
    allsimpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f.

      * apply utok_sub_find_some in Heqf.
        apply subset_app_l.
        rw @bound_vars_utok_sub_eq_flat_map.
        apply subsetSingleFlatMap.
        apply implies_utok_sub_range in Heqf; auto.

      * simpl; allrw flat_map_map; unfold compose.
        apply subset_flat_map; introv i; destruct x as [l t]; simpl.
        rw subset_app; dands.

        { apply subset_app_r.
          pose proof (subsetSingleFlatMap bound_vars_bterm bs (bterm l t)) as h; allsimpl.
          allrw subset_app; tcsp. }

        { introv j; apply (ind t l i sub) in j; allrw in_app_iff; repndors; tcsp.
          left.
          rw lin_flat_map; eexists; dands; eauto; simpl; rw in_app_iff; sp. }

    + simpl; allrw flat_map_map; unfold compose.
      apply subset_flat_map; introv i; destruct x as [l t]; simpl.
      rw subset_app; dands.

      { apply subset_app_r.
        pose proof (subsetSingleFlatMap bound_vars_bterm bs (bterm l t)) as h; allsimpl.
        allrw subset_app; tcsp. }

      { introv j; apply (ind t l i sub) in j; allrw in_app_iff; repndors; tcsp.
        left.
        rw lin_flat_map; eexists; dands; eauto; simpl; rw in_app_iff; sp. }
Qed.

Lemma implies_closed_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    closed t
    -> closed (ren_utokens ren t).
Proof.
  introv cl.
  allunfold @closed.
  rw @free_vars_ren_utokens; auto.
Qed.
Hint Resolve implies_closed_ren_utokens : slow.

Lemma computes_in_1step_alpha_fresh2 {o} :
  forall lib (t u : @NTerm o) v a,
    nt_wf t
    -> !LIn a (get_utokens t)
    -> computes_in_1step_alpha lib (lsubst_aux t [(v, mk_utoken a)]) u
    -> computes_in_1step_alpha lib (mk_fresh v t) (mk_fresh v (subst_utokens u [(a,mk_var v)])).
Proof.
  introv wf ni comp.
  unfold computes_in_1step_alpha in comp; exrepnd.
  apply computes_in_1step_alpha_fresh in comp1; auto.
  eapply computes_in_1step_alpha2;[|exact comp1|idtac|]; eauto 2 with slow;
  [apply nt_wf_fresh; auto|];[].
  apply implies_alpha_eq_mk_fresh.
  apply alpha_eq_subst_utokens_same; eauto with slow.
Qed.

Lemma computes_in_1step_preserves_get_utokens {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> computes_in_1step lib t u
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv wf comp.
  inversion comp as [? ? ? ? comp1|? ? ? ? comp1]; subst; clear comp;
  apply compute_step_preserves_utokens in comp1; auto.
Qed.

Lemma noncan_like_tricot {o} :
  forall lib (t : @NTerm o),
    isprogram t
    -> isnoncan_like t
    -> {v : NTerm
        $ compute_step lib t = csuccess v
        # isprogram v
        # (isvalue v[+]isnoncan v[+]isexc v[+]isabs v [+] isseq v)}
       [+]
       computes_step_to_error lib t.
Proof.
  introv isp isn.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    apply noncan_tricot; auto.
  - apply isabs_implies in isn; exrepnd; subst.
    apply noncan_tricot_abs; auto.
Qed.

Lemma computes_step_to_error_ren_utokens {o} :
  forall lib (t : @NTerm o) ren,
    isprogram t
    -> no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_step_to_error lib t
    -> computes_step_to_error lib (ren_utokens ren t).
Proof.
  introv isp norep1 norep2 disj comp.
  applydup @isprogram_error in comp; auto;[].
  fold (isnoncan_like t) in comp0.
  pose proof (isprogram_ren_utokens ren t isp) as ispr.
  pose proof (noncan_like_tricot lib (ren_utokens ren t) ispr) as h.
  autodimp h hyp; eauto 3 with slow.
  repndors; tcsp.
  exrepnd.
  pose proof (compute_step_ren_utokens lib (ren_utokens ren t) v (inv_utok_ren ren)) as q.
  rw @range_utok_ren_inv_utok_ren in q.
  rw @dom_utok_ren_inv_utok_ren in q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom. }
  rw @inv_ren_utokens in q; auto.
  unfold computes_step_to_error in comp.
  remember (compute_step lib t) as c; destruct c; ginv; tcsp.
Qed.

Definition isutok {o} (t : @NTerm o) :=
  match t with
    | oterm (Can (NUTok _)) _ => True
    | _ => False
  end.

Lemma isvalue_like_subst_utokens_aux {o} :
  forall (t : @NTerm o) sub,
    isvalue_like (subst_utokens_aux t sub)
    -> {a : get_patom_set o
        & {bs : list BTerm
        & t = oterm (Can (NUTok a)) bs
        # ({u : NTerm & utok_sub_find sub a = Some u # isvalue_like u}
           [+] !LIn a (utok_sub_dom sub))}}
       [+] (isvalue_like t # !(isutok t)).
Proof.
  introv isv.
  destruct t as [v|f|op bs].

  - allsimpl.
    unfold isvalue_like in isv; allsimpl; repndors; inversion isv.

  - allsimpl.
    right; dands; eauto 3 with slow; tcsp.

  - allrw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok in isv.
      remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f.
      * left.
        exists g bs; dands; auto.
        left.
        exists n; auto.
      * left.
        exists g bs; dands; auto.
        right.
        apply utok_sub_find_none in Heqf; auto.
    + right; dands; eauto with slow.
      destruct op; allsimpl; ginv; tcsp.
      destruct c; allsimpl; ginv; tcsp.
Qed.

Lemma alpha_eq_preserves_isutok {o} :
  forall (t u : @NTerm o),
    alpha_eq t u
    -> isutok t
    -> isutok u.
Proof.
  introv aeq isu.
  allunfold @isutok.
  destruct t as [v|f|op bs]; allsimpl; ginv; tcsp;[].
  destruct op as [can|ncan|exc|abs]; allsimpl; ginv; tcsp;[].
  destruct can; allsimpl; ginv; tcsp;[].
  apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst; allsimpl; auto.
Qed.

Lemma isvalue_like_subst_utokens {o} :
  forall (t : @NTerm o) sub,
    isvalue_like (subst_utokens t sub)
    -> {a : get_patom_set o
        & {bs : list BTerm
        & t = oterm (Can (NUTok a)) bs
        # ({u : NTerm & utok_sub_find sub a = Some u # isvalue_like u}
           [+] !LIn a (utok_sub_dom sub))}}
       [+] (isvalue_like t # !(isutok t)).
Proof.
  introv isv.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0 in isv.
  apply isvalue_like_subst_utokens_aux in isv; repeat (repndors; exrepnd); subst.
  - left.
    apply alpha_eq_sym in h1.
    apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst; allsimpl.
    exists a bs'; dands; auto.
    left.
    exists u; dands; auto.
  - left.
    apply alpha_eq_sym in h1.
    apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst; allsimpl.
    exists a bs'; dands; auto.
  - right; dands; eauto 3 with slow.
    introv i.
    apply alpha_eq_preserves_isutok in h1; auto.
Qed.

Lemma computes_step_to_error_if_isvalue_like {o} :
  forall lib (t : @NTerm o),
    isvalue_like t
    -> computes_step_to_error lib t
    -> False.
Proof.
  introv isv comp.
  unfold computes_step_to_error in comp.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst;
    csunf comp; allsimpl; tcsp.
  - apply isexc_implies2 in isv; exrepnd; subst.
    csunf comp; allsimpl; tcsp.
Qed.

Lemma subst_utokens_aux_eq_vterm_implies {o} :
  forall (t : @NTerm o) sub v,
    subst_utokens_aux t sub = vterm v
    -> {a : get_patom_set o
        & {bs : list BTerm
        & t = oterm (Can (NUTok a)) bs
        # utok_sub_find sub a = Some (vterm v)}}
       [+] t = vterm v.
Proof.
  introv e.
  destruct t as [var|f|op bs].
  - allsimpl; ginv; tcsp.
  - allsimpl; ginv.
  - allrw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; ginv.
    apply get_utok_some in Heqguo; subst; allsimpl.
    unfold subst_utok in e; allsimpl.
    remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f; subst; ginv.
    left.
    exists g bs; sp.
Qed.

Lemma subst_utokens_eq_vterm_implies {o} :
  forall (t : @NTerm o) sub v,
    subst_utokens t sub = vterm v
    -> {a : get_patom_set o
        & {bs : list BTerm
        & t = oterm (Can (NUTok a)) bs
        # utok_sub_find sub a = Some (vterm v)}}
       [+] t = vterm v.
Proof.
  introv e.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0 in e.
  apply subst_utokens_aux_eq_vterm_implies in e; repndors; exrepnd; subst.
  - left.
    apply alpha_eq_sym in h1.
    apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst; allsimpl.
    exists a bs'; dands; auto.
  - right.
    inversion h1; auto.
Qed.

Definition computes_step_to_success {o} lib (t : @NTerm o) :=
  match compute_step lib t with
    | csuccess _ => True
    | cfailure _ _ => False
  end.

Lemma implies_computes_step_to_success {o} :
  forall lib (t : @NTerm o) u,
    compute_step lib t = csuccess u
    -> computes_step_to_success lib t.
Proof.
  introv comp.
  unfold computes_step_to_success; rw comp; auto.
Qed.

Lemma computes_step_to_error_alpha_eq {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> alpha_eq t u
    -> computes_step_to_error lib t
    -> computes_step_to_error lib u.
Proof.
  introv wf aeq comp.
  allunfold @computes_step_to_error.
  applydup @alpha_eq_respects_nt_wf in aeq; auto.
  remember (compute_step lib u) as c; symmetry in Heqc; destruct c; auto.
  eapply compute_step_alpha in Heqc;[| |apply alpha_eq_sym; exact aeq]; auto.
  exrepnd.
  rw Heqc1 in comp; tcsp.
Qed.

Lemma computes_step_to_success_alpha_eq {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> alpha_eq t u
    -> computes_step_to_success lib t
    -> computes_step_to_success lib u.
Proof.
  introv wf aeq comp.
  allunfold @computes_step_to_success.
  remember (compute_step lib t) as c; symmetry in Heqc; destruct c; tcsp; GC.
  eapply compute_step_alpha in Heqc;[| |exact aeq]; exrepnd; auto.
  rw Heqc1; auto.
Qed.

Lemma subset_free_vars_lsubst_aux_app_dom {o} :
  forall (t : @NTerm o) sub,
    subset (free_vars t) (free_vars (lsubst_aux t sub) ++ dom_sub sub).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as f; symmetry in Heqf; destruct f; allsimpl; eauto 3 with slow.
    introv i; rw in_app_iff; allsimpl; repndors; tcsp; subst.
    apply sub_find_some in Heqf.
    apply in_sub_eta in Heqf; sp.

  - Case "oterm".
    apply subset_flat_map; introv i.
    destruct x as [l t]; allsimpl.
    allrw flat_map_map; unfold compose.
    rw <- subvars_eq; rw subvars_remove_nvars; rw subvars_eq.
    pose proof (ind t l i (sub_filter sub l)) as h; clear ind.
    eapply subset_trans;[exact h|clear h].
    apply subset_app; dands; eauto 3 with slow.
    + introv j; allrw in_app_iff.
      destruct (in_deq _ deq_nvar x l) as [k|k]; tcsp.
      left; left.
      rw lin_flat_map.
      eexists; dands; eauto; simpl.
      rw in_remove_nvars; dands; tcsp.
    + rw <- @dom_sub_sub_filter.
      rw <- subvars_eq; rw subvars_remove_nvars; rw subvars_eq.
      eauto with slow.
Qed.

Lemma isprog_vars_lsubst_aux_implies {o} :
  forall (t : @NTerm o) vs sub,
    isprog_vars vs (lsubst_aux t sub)
    -> isprog_vars (vs ++ dom_sub sub) t.
Proof.
  introv isp.
  allrw @isprog_vars_eq; repnd.
  allrw @nt_wf_lsubst_aux_iff; repnd.
  dands; auto.
  allrw subvars_prop.
  introv i; allrw in_app_iff.
  destruct (in_deq _ deq_nvar x (dom_sub sub)) as [j|j]; tcsp.
  left.
  apply isp0.
  apply (subset_free_vars_lsubst_aux_app_dom t sub) in i; allrw in_app_iff; tcsp.
Qed.

Lemma isprog_vars_lsubst_implies {o} :
  forall (t : @NTerm o) vs sub,
    isprog_vars vs (lsubst t sub)
    -> isprog_vars (vs ++ dom_sub sub) t.
Proof.
  introv isp.
  pose proof (unfold_lsubst sub t) as h; exrepnd.
  rw h0 in isp.
  apply isprog_vars_lsubst_aux_implies in isp.
  eapply alphaeq_preserves_isprog_vars;[apply alpha_eq_sym; exact h1|]; auto.
Qed.

Lemma computes_step_to_success_ren_utokens {o} :
  forall lib (t : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_step_to_success lib t
    -> computes_step_to_success lib (ren_utokens ren t).
Proof.
  introv wf norep1 disj comp.
  allunfold @computes_step_to_success.
  remember (compute_step lib t) as c; symmetry in Heqc; destruct c; tcsp; GC.
  pose proof (compute_step_ren_utokens lib t n ren) as h.
  repeat (autodimp h hyp).
  rw h; auto.
Qed.

Lemma computes_step_to_error_and_success {o} :
  forall lib (t : @NTerm o),
    computes_step_to_error lib t
    -> computes_step_to_success lib t
    -> False.
Proof.
  introv comp1 comp2.
  unfold computes_step_to_error in comp1.
  unfold computes_step_to_success in comp2.
  remember (compute_step lib t) as c; destruct c; tcsp.
Qed.


(* by \equiv, Crary means alpha equality : page 6, bottom : Indeed, there
    is no point in holding on to concrete variable names*)

Lemma simple_sub_find_beq_var {o} :
  forall v1 v2 (t : @NTerm o),
    sub_find (if beq_var v1 v2 then [] else [(v1, t)]) v2 = None.
Proof.
  introv; boolvar; simpl; boolvar; tcsp.
Qed.

Lemma co_wf_def_map {o} :
  forall c op (bs : list (@BTerm o)) f,
    co_wf_def c op (map f bs) <=> co_wf_def c op bs.
Proof.
  introv.
  unfold co_wf_def.
  split; introv k; exrepnd; subst; try (destruct bs; allsimpl; ginv);
  exists pk; dands; auto.
Qed.

Lemma ca_wf_def_map {o} :
  forall op (bs : list (@BTerm o)) f,
    ca_wf_def op (map f bs) <=> ca_wf_def op bs.
Proof.
  introv.
  unfold ca_wf_def.
  split; introv k; exrepnd; subst; try (destruct bs; allsimpl; ginv);
  eexists; dands; eauto.
Qed.

Lemma computes_in_1step_alpha_sterm {o} :
  forall lib (f : @ntseq o) t u,
    computes_in_1step_alpha lib t u
    -> computes_in_1step_alpha lib (mk_eapply (sterm f) t) (mk_eapply (sterm f) u).
Proof.
  introv comp.
  allunfold @computes_in_1step_alpha; exrepnd.
  exists (mk_eapply (sterm f) t2a); dands.
  - inversion comp1; subst; constructor; csunf; simpl; dcwf h; simpl; allrw; simpl; auto.
  - repeat prove_alpha_eq4.
Qed.

Lemma computes_in_1step_alpha_lam {o} :
  forall lib v (b : @NTerm o) t u,
    computes_in_1step_alpha lib t u
    -> computes_in_1step_alpha lib (mk_eapply (mk_lam v b) t) (mk_eapply (mk_lam v b) u).
Proof.
  introv comp.
  allunfold @computes_in_1step_alpha; exrepnd.
  exists (mk_eapply (mk_lam v b) t2a); dands.
  - inversion comp1; subst; constructor; csunf; simpl; dcwf h; simpl; allrw; simpl; auto.
  - repeat prove_alpha_eq4.
Qed.

Lemma computes_in_1step_alpha_nseq {o} :
  forall lib s (t u : @NTerm o),
    computes_in_1step_alpha lib t u
    -> computes_in_1step_alpha lib (mk_eapply (mk_nseq s) t) (mk_eapply (mk_nseq s) u).
Proof.
  introv comp.
  allunfold @computes_in_1step_alpha; exrepnd.
  exists (mk_eapply (mk_nseq s) t2a); dands.
  - inversion comp1; subst; constructor; csunf; simpl; dcwf h; simpl; allrw; simpl; auto.
  - repeat prove_alpha_eq4.
Qed.

Hint Rewrite @lsubst_aux_nil : slow.

Lemma iscan_lsubst_aux_implies {o} :
  forall (t : @NTerm o) sub,
    (forall v u, LIn (v,u) sub -> isnoncan_like u)
    -> iscan (lsubst_aux t sub)
    -> iscan t.
Proof.
  introv imp isc.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; tcsp.
  allapply @sub_find_some; apply imp in Heqsf.
  unfold isnoncan_like in Heqsf.
  destruct n as [v1|f|op bs]; allsimpl; tcsp.
  destruct op; allsimpl; tcsp.
Qed.

Lemma free_vars_lsubst_aux_single_if_subset {o} :
  forall (t : @NTerm o) v u,
    subset (free_vars t) [v]
    -> isprogram u
    -> free_vars (lsubst_aux t [(v, u)]) = [].
Proof.
  introv ss isp.
  rw @isprogram_lsubst_aux2; simpl;[|introv i; repndors; tcsp; ginv; auto].
  apply null_iff_nil.
  introv i.
  allrw in_remove_nvars; allrw in_single_iff; repnd.
  apply ss in i0; allsimpl; repndors; tcsp.
Qed.

Lemma two_as_app {T} :
  forall (a b : T), [a,b] = [a] ++ [b].
Proof. sp. Qed.

Lemma computes_in_1step_iff_isnoncan_like {o} :
  forall lib (t u : @NTerm o),
    computes_in_1step lib t u
    <=> (isnoncan_like t # compute_step lib t = csuccess u).
Proof.
  introv; split; intro h;
  try (apply computes_in_1step_if_isnoncan_like; tcsp).
  inversion h; subst; dands; tcsp.
Qed.

Lemma isprogram_error_implies_isnoncan_like {o} :
  forall lib (t : @NTerm o),
    isprogram t
    -> computes_step_to_error lib t
    -> isnoncan_like t.
Proof.
  introv isp comp.
  apply isprogram_error in comp; auto.
Qed.

Lemma isprogram_implies_nt_wf {o} :
  forall (t : @NTerm o), isprogram t -> nt_wf t.
Proof.
  introv isp; inversion isp; sp.
Qed.

Lemma crary5_7_aux_stronger {p} :
  forall lib e1 e2 no lbt vx vy,
    let t := oterm (@NCan p no) lbt in
    let tl := subst_aux e1 vx t in
    vx <> vy
    -> !LIn vx (bound_vars e1)
    -> !LIn vy (bound_vars e1)
    -> isprogram t
    -> isprogram tl
    -> computes_in_1step lib tl e2
    -> {e2' : NTerm $ forall t',
                        isprogram t'
                        -> computes_in_1step_alpha lib
                             (subst_aux e1 vx t')
                             (subst_aux e2' vx t')}
            (* t was merely moved/copied around unchanged in this step*)
       [+]
       {e1',t' : NTerm
        $ alpha_eq e1 (subst e1' vy (vterm vx)) (* except here, we are always subbing closed terms*)
        # computes_in_1step lib t t'
        # forall t'' td td',
            isprogram t''
            -> isprogram td
            -> (computes_in_1step lib td td'
                -> computes_in_1step_alpha lib (lsubst_aux e1' [(vx,t''),(vy,td)])
                                     (lsubst_aux e1' [(vx,t''),(vy,td')]))
                 # (computes_step_to_error lib td
                    -> computes_step_to_error lib (lsubst_aux e1' [(vx,t''),(vy,td)]))}.
     (* one of the occurences of t gets reduced with surroundings being the same.
        that occurence is denoted by y *)
Proof.
  nterm_ind1s e1 as [v1|f1|o1 lbt1 Hind] Case;
  introv Hneq;
  introv Hd nivy (*disjlib*) Hpt He1p Hcs;
  allunfold @subst; allunfold @subst_aux.

  {
    allsimpl; boolvar; tcsp;
    [|destruct He1p as [c w]; unfold closed in c; allsimpl; ginv].
    right; exists (@vterm p vy) e2; allsimpl; boolvar; tcsp.
    unfold lsubst; simpl; boolvar; tcsp.
    dands; tcsp.
    introv isp1 isp2; dands; intro comp; eauto with slow.
  }

  {
    allsimpl.
    inversion Hcs.
  }

  dopid o1 as [oc1|e1o|exc|abs] Case0;
    [complete (inverts Hcs)|idtac|complete (inverts Hcs)|idtac].

  { destruct lbt1 as [|e1bt1 e1lbt]; invertsn Hcs; invertsn Hcs;[].
    destruct e1bt1 as [l e1bt1nt];[].
    destruct l  as [|v l];[|(* fresh case *)].

  { duplicate He1p as Xsss.
    rewrite <- lsubst_lsubst_aux_prog_sub in Xsss;[| prove_sub_range_sat; fail].
    apply lsubst_program_implies in Xsss.
    let T:= type of Xsss in match T with
    | subset ?l ?r => let rs:= eval simpl in r in
                        assert (subset l rs) as Xss by trivial
    end.
    apply subset_disjoint with (l3:=[vy]) in Xss;[|
      introv Hin Hinc; repeat(in_reasoning);subst;
      inverts Hin;cpx; fail].
    apply' (@lsubst_bterm_aux_trim p [vy]) Xss.

  destruct e1bt1nt as [e1bt1v|f| e1bt1o e1bt1lbt]; invertsn Hcs.

  - clear Hind.
    boolvar; tcsp;[|complete (invertsn Hcs)].
    csunf Hcs; allsimpl.
    remember (compute_step lib (oterm (NCan no) lbt)) as t; symmetry in Heqt.
    destruct t as [crt|];[|complete (invertsn Hcs)]; allsimpl; ginv.
    subst. right. exists (oterm (NCan e1o) (bterm [] (vterm vy) :: e1lbt)).
    applydup @preserve_compute_step in Heqt;sp;[].
    exists crt.
    dands; try (spc;fail); allsimpl;[|].
    + unfold lsubst.
      cases_ifd Hd;[|provefalse; apply Hdf;allsimpl; disjoint_reasoningv;cpx;fail].
      simpl. autorewrite with slow in *. repeat(prove_alpha_eq4). repeat(fold_selectbt). rw @selectbt_map;[|omega].
       rw Xss;[ | right;apply selectbt_in;omega];[].
       simpl. unfold memvar. simpl. rw <-beq_deq. autorewrite with slow. rw @lsubst_bterm_aux_trivial. apply alphaeqbt_refl.
       (* the same proof works for equality ... not merely alpha*)
    + simpl. introv Hpr'' Hprtd. simpl.
      boolvar; tcsp.
      autorewrite with slow in *.
      simpl.
      dands;clear Heqt; introv Hcsd.

    Focus 2.
    allunfold @computes_step_to_error;
      destruct td as [?|?|tdoo tdlbt]; auto;
      try (complete (allsimpl; tcsp));
    destruct tdoo as [|tdnc|exc|abs];
    [ csunf Hcsd; simpl in Hcsd; cpx; fail
    | remember (compute_step lib (oterm (NCan tdnc) tdlbt)) as ctd;
      destruct ctd;[cpx|]; simpl; csunf; simpl; rw <- Heqctd; auto; fail
    | csunf Hcsd; simpl in Hcsd; cpx; fail
    | remember (compute_step lib (oterm (Abs abs) tdlbt)) as ctd;
      destruct ctd;[cpx|]; simpl; csunf; simpl; rw <- Heqctd; auto; allsimpl;
      rw <- Heqctd in Hcsd; sp; fail
    ].

    apply computes_in_1step_to_alpha.
    constructor.
      simpl. invertsn Hcsd.

      { csunf; simpl.
        rw Hcsd.
        unfold on_success.
        f_equal. f_equal. f_equal.
        apply eq_maps_bt; auto. introv Hlt.
        let tac2 :=  apply prog_sub_disjoint_bv_sub; prove_sub_range_sat in
        let tac3 := right;apply selectbt_in;omega in
        rw Xss;[| tac3];[]; symmetry;
        rw Xss;[| tac3]; simpl.
        autorewrite with slow. unfold memvar. simpl. cases_if; cpx. }

      { csunf; simpl; rw Hcsd.
        unfold on_success.
        f_equal. f_equal. f_equal.
        apply eq_maps_bt; auto. introv Hlt.
        let tac2 :=  apply prog_sub_disjoint_bv_sub; prove_sub_range_sat in
        let tac3 := right;apply selectbt_in;omega in
        rw Xss;[| tac3];[]; symmetry; rw Xss;[| tac3];simpl.
        autorewrite with slow. unfold memvar. simpl. cases_if; cpx. }

  - allsimpl.
    csunf Hcs; allsimpl.
    dopid_noncan e1o SCase; allsimpl; ginv.

    + SCase "NApply".
      apply compute_step_seq_apply_success in Hcs; exrepnd; subst; allsimpl.
      repeat (destruct e1lbt; allsimpl; ginv).
      destruct b as [l t]; allsimpl.
      destruct l; allsimpl; fold_terms; ginv; allsimpl; autorewrite with slow in *.

      left.
      exists (mk_eapply (sterm f) t); introv isp'.
      apply computes_in_1step_to_alpha.
      constructor; csunf; simpl; auto.

    + SCase "NEApply".
      apply compute_step_eapply_success in Hcs; exrepnd.
      destruct e1lbt; allsimpl; ginv;[].
      destruct b as [vs t].
      destruct vs; allsimpl; fold_terms; ginv;[].
      autorewrite with slow in *.

      repndors; exrepnd; subst.

      * apply compute_step_eapply2_success in Hcs1; repnd.
        destruct e1lbt; allsimpl; ginv;[].
        repndors; exrepnd; ginv;[]; autorewrite with slow in *.
        destruct t as [v|f|op bs]; allsimpl; boolvar; ginv;[].
        allunfold @mk_nat; allunfold @mk_integer; ginv.
        destruct bs; allsimpl; ginv;[]; fold_terms; GC.

        left.
        exists (f0 n); introv isp'.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl; auto.
        dcwf h; simpl; boolvar; try omega;[].
        allrw Znat.Nat2Z.id.
        allrw <- @isprogram_eapply_iff; repnd.
        apply (isprogram_sterm_implies_isprogram_apply _ n) in He1p0.
        rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow.

      * allapply @isprogram_eapply_implies; exrepnd; fold_terms; ginv.
        destruct e1lbt; allsimpl; ginv;[].
        apply isexc_implies in Hcs0; auto;[].
        exrepnd.
        destruct t as [v|f1|op bs]; allsimpl; boolvar; ginv;[].
        allunfold @mk_exception; ginv.
        repeat (destruct bs; allsimpl; ginv).
        destruct b as [l1 t1].
        destruct b0 as [l2 t2].
        destruct l1; allsimpl; fold_terms; ginv.
        destruct l2; allsimpl; fold_terms; ginv.
        allunfold @mk_exception; ginv; fold_terms.
        autorewrite with slow in *.

        left.
        exists (mk_exception t1 t2); introv isp'.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl; auto.

      * allapply @isprogram_eapply_implies; exrepnd; fold_terms; ginv.
        destruct e1lbt; allsimpl; ginv;[]; autorewrite with slow in *.
        pose proof (Hind t t []) as h; clear Hind.
        repeat (autodimp h hyp); eauto 3 with slow;[].
        pose proof (h x no lbt vx vy) as ih; clear h.
        repeat (autodimp ih hyp).
        { apply computes_in_1step_if_isnoncan_like; auto. }

        repndors; exrepnd.

        { left.
          exists (mk_eapply (sterm f) e2'); introv isp'.
          pose proof (ih0 t') as h'; clear ih0; autodimp h' hyp.
          simpl; fold_terms.
          eapply computes_in_1step_alpha_sterm; auto. }

        { right.
          exists (mk_eapply (sterm f) e1') t'.
          dands; auto.
          - revert ih0; unfold lsubst; simpl; autorewrite with slow in *.
            introv aeq.
            boolvar;[|].
            + repeat prove_alpha_eq4.
            + unfold var_ren; simpl; autorewrite with slow in *.
              repeat prove_alpha_eq4.
          - introv isp1 isp2; simpl; fold_terms.
            pose proof (ih1 t'' td td') as h; clear ih1.
            repeat (autodimp h hyp);[].
            repnd; dands; auto;[|].
            + introv comp.
              autodimp h0 hyp.
              eapply computes_in_1step_alpha_sterm; auto.
            + introv comp.
              autodimp h hyp.
              remember (lsubst_aux e1' [(vx, t''), (vy, td)]) as u.
              allunfold @computes_step_to_error.
              destruct u as [v|f1|op bs]; allsimpl; ginv;[].
              remember (compute_step lib (oterm op bs)) as cs; destruct cs; symmetry in Heqcs; ginv; tcsp;[].
              dopid op as [can|ncan|exc|abs] SSCase; allsimpl; ginv; tcsp;[|];
              csunf; simpl;
              unfold compute_step_eapply; simpl; allrw; simpl; auto.
        }

    + SCase "NFix".
      apply compute_step_fix_success in Hcs; exrepnd; subst; allsimpl.
      repeat (destruct e1lbt; allsimpl; ginv); GC.

      left.
      exists (mk_apply (sterm f) (mk_fix (sterm f))); introv isp'.
      apply computes_in_1step_to_alpha.
      constructor; csunf; simpl; auto.

    + SCase "NCbv".
      apply compute_step_cbv_success in Hcs; exrepnd; subst; allsimpl.
      repeat (destruct e1lbt; allsimpl; ginv); GC; autorewrite with slow in *.
      destruct b as [l t].
      repeat (destruct l; allsimpl; ginv;[]).
      allsimpl; allrw memvar_singleton.
      allrw not_over_or; repnd.
      boolvar; tcsp;[].
      fold_terms.

      left.
      exists (subst t v (sterm f)); introv isp'.
      apply computes_in_1step_to_alpha.
      constructor; csunf; simpl; auto.
      unfold apply_bterm; simpl.
      rw @cl_subst_subst_aux; eauto 3 with slow;[].
      rw @cl_lsubst_lsubst_aux; eauto 4 with slow;[].
      unfold subst_aux.
      rw <- (simple_subst_lsubst_aux t (sterm f)); allsimpl; eauto 4 with slow;
      [|unfold covered; simpl; auto];[].
      allrw @memvar_singleton; boolvar; tcsp.

    + SCase "NTryCatch".
      apply compute_step_try_success in Hcs; exrepnd; subst; allsimpl.
      repeat (destruct e1lbt; allsimpl; ginv); GC.
      destruct b as [l1 t1].
      destruct b0 as [l2 t2].
      repeat (destruct l1; allsimpl; ginv;[]).
      repeat (destruct l2; allsimpl; ginv;[]).
      autorewrite with slow in *.
      allrw in_app_iff; allrw in_single_iff; allrw not_over_or; repnd.
      boolvar; tcsp;[].
      fold_terms.

      left.
      exists (mk_atom_eq t1 t1 (sterm f) mk_bot).
      introv isp; simpl.
      allrw memvar_singleton; rw @simple_sub_find_beq_var.
      apply computes_in_1step_to_alpha.
      rw <- @compute_1_step_is_computes_in_1step; reflexivity.

    + SCase "NCanTest".
      apply compute_step_seq_can_test_success in Hcs; exrepnd; subst; allsimpl.
      repeat (destruct e1lbt; allsimpl; ginv); GC.
      destruct b0 as [l1 t1].
      destruct b1 as [l2 t2].
      repeat (destruct l1; allsimpl; ginv;[]).
      repeat (destruct l2; allsimpl; ginv;[]).
      fold_terms; ginv.
      autorewrite with slow in *.
      allrw in_app_iff; allrw in_single_iff; allrw not_over_or; repnd.

      left.
      exists t2.
      introv isp; simpl.
      apply computes_in_1step_to_alpha.
      constructor; csunf; simpl; auto.

  - dopid e1bt1o as [e1bt1oc | e1bt1on | e1bt1oe | e1bt1oa] Case1.

    + dopid_noncan e1o SCase.

      * SCase "NApply". left.
        clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_apply_success in Hcs; repndors; exrepnd; subst; allsimpl.

        { repeat (destruct e1lbt; allsimpl; ginv;[]).
          repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
          destruct b1 as [l1 t1]; allsimpl; ginv.
          destruct b0 as [l2 t2]; allsimpl; ginv.
          allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
          allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          allrw memvar_singleton; boolvar; tcsp;[].
          allrw subset_app; repnd.
          fold_terms.

          exists (subst t1 v t2).
          introv Hp; allsimpl.
          apply computes_in_1step_to_alpha.
          constructor; csunf; simpl.
          unfold apply_bterm; simpl; f_equal.
          rw @lsubst_lsubst_aux; simpl;
          [|rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow; allrw app_nil_r;
            introv i j; rw in_remove_nvars in j; allsimpl; repnd; apply Xsss in j0;
            allsimpl; complete sp].
          unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
          [|introv i j; apply Xsss in j; allsimpl; repndors; subst; complete sp].

          rw <- (simple_subst_lsubst_aux t1 t2); allsimpl;
          allrw memvar_singleton; boolvar; tcsp; eauto 3 with slow.

          { unfold covered; rw subvars_eq; auto. }

          { introv i j; apply Xsss in j; allsimpl; repndors; subst; tcsp. }
        }

        { destruct e1bt1lbt; allsimpl; ginv.
          repeat (destruct e1lbt; allsimpl; ginv).
          destruct b as [l t].
          destruct l; allsimpl; ginv.

          allrw app_nil_r; allrw remove_nvars_nil_l.
          fold_terms.

          exists (mk_eapply (mk_nseq f) t).
          introv Hp; allsimpl.
          fold_terms.
          apply computes_in_1step_to_alpha.
          constructor.
          csunf; simpl; auto.
        }

      * SCase "NEApply".
        allsimpl; autorewrite with slow in *.
        allapply @isprogram_eapply_implies; exrepnd; ginv.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        destruct b as [l t].
        destruct l; allsimpl; ginv;[].
        autorewrite with slow in *.
        csunf Hcs; allsimpl.
        apply compute_step_eapply_success in Hcs; exrepnd.
        allunfold @nobnd; ginv.

        allapply @eapply_wf_def_oterm_implies; exrepnd; ginv.
        destruct Hcs2 as [Hcs2|Hcs2]; exrepnd; ginv.

        { repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
          destruct b as [l u].
          repeat (destruct l; allsimpl; ginv;[]).
          allsimpl; autorewrite with slow in *.
          allrw in_app_iff; allrw not_over_or; repnd; fold_terms.
          repeat (boolvar; tcsp;[]).
          allrw subset_app; repnd.

          repndors; exrepnd; subst; ginv; fold_terms.

          { apply iscan_lsubst_aux_implies in Hcs0;
            [|simpl; introv i; repndors; tcsp; ginv; eauto 3 with slow];[].

            left.
            exists (subst u v t).
            introv isp'.
            eexists;dands;
            [constructor; fold_terms; unfold mk_eapply;
             rw @compute_step_eapply_lam_iscan;[|apply iscan_lsubst_aux;auto];
             eauto
            |].
            unfold subst; rw @lsubst_lsubst_aux;
            [|simpl; autorewrite with slow;
              eapply subset_disjoint_r;[|eauto];
              apply disjoint_singleton_r; auto].
            rw @lsubst_lsubst_aux;
              [|simpl; autorewrite with slow;
                rw @free_vars_lsubst_aux_single_if_subset; auto].

            rw <- @simple_lsubst_aux_lsubst_aux_sub; simpl; eauto 3 with slow;
            [|simpl; autorewrite with slow;
              eapply subset_disjoint_r;[|eauto];
              apply disjoint_singleton_r; auto].
            allrw memvar_singleton; boolvar; tcsp.
          }

          { apply subst_exc in Hcs0; exrepnd; subst; allsimpl.
            allapply @isprogram_exception_implies; exrepnd.
            repeat (destruct lbtc; allsimpl; ginv;[]).
            destruct b as [l1 t1].
            destruct b0 as [l2 t2].
            destruct l1; allsimpl; fold_terms; ginv.
            destruct l2; allsimpl; fold_terms; ginv.
            allsimpl; autorewrite with slow in *.

            allrw in_app_iff; allrw not_over_or; repnd.
            allrw subset_app; repnd.

            left.
            exists (mk_exception t1 t2); introv isp'.
            apply computes_in_1step_to_alpha.
            constructor; csunf; simpl; auto. }

          { apply computation_mark.isnoncan_like_lsubst_aux in Hcs2.

            assert (!LIn vy (free_vars u)) as nivyu.
            { intro i.
              pose proof (Xsss0 vy) as h.
              allrw in_remove_nvars; allrw in_single_iff.
              autodimp h hyp; tcsp. }

            repndors; exrepnd; subst; allsimpl; GC.

            - allrw @singleton_subset; allrw in_single_iff; subst.
              boolvar; tcsp;[]; ginv; GC.

              right.
              exists (mk_eapply (mk_lam v u) (mk_var vy)) x.
              dands; auto.

              + rw @lsubst_lsubst_aux;
                [|simpl; autorewrite with slow;
                  apply disjoint_cons_l; rw in_single_iff; rw disjoint_singleton_r;
                  dands; tcsp].
                simpl; allrw memvar_singleton.
                boolvar; tcsp;[]; fold_terms.
                repeat prove_alpha_eq4;[].
                apply alpha_eq_bterm_congr.
                rw @lsubst_aux_trivial_cl_term; auto.
                simpl; apply disjoint_singleton_r; tcsp.

              + constructor; auto.

              + introv isp1 isp2; dands; intro comp.

                * simpl; allrw memvar_singleton; boolvar; tcsp;[]; fold_terms.
                  allrw @two_as_app.
                  applydup@ computes_in_1step_program in comp; auto;[].
                  repeat (rw @cl_lsubst_aux_app; eauto 3 with slow;[]).
                  repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux u [(vx, t'')]));
                          [|simpl; apply disjoint_singleton_r;
                            rw @free_vars_lsubst_aux_cl; eauto 3 with slow;[];
                            simpl; rw in_remove_nvars; rw in_single_iff; tcsp];[]).
                  apply computes_in_1step_to_alpha.
                  allrw @computes_in_1step_iff_isnoncan_like; repnd; dands; tcsp;[].
                  unfold mk_eapply.
                  rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow;[].
                  rw comp; auto.

                * simpl; allrw memvar_singleton; boolvar; tcsp;[].
                  applydup @isprogram_error_implies_isnoncan_like in comp; auto;[].
                  allunfold @computes_step_to_error.
                  fold_terms.
                  remember (compute_step lib td) as cs; symmetry in Heqcs; destruct cs; ginv; tcsp; GC;[].
                  unfold mk_eapply; rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
                  rw Heqcs; auto.

            - pose proof (Hind t t []) as h; clear Hind.
              repeat (autodimp h hyp); eauto 3 with slow;[].
              pose proof (h x no lbt vx vy) as ih; clear h.
              repeat (autodimp ih hyp).
              { apply computes_in_1step_if_isnoncan_like; auto.
                apply isnoncan_like_lsubst_aux; auto. }

              repndors; exrepnd.

              { left.
                exists (mk_eapply (mk_lam v u) e2'); introv isp'.
                pose proof (ih0 t') as h'; clear ih0; autodimp h' hyp.
                simpl; fold_terms.
                allrw memvar_singleton; boolvar; tcsp;[].
                eapply computes_in_1step_alpha_lam; auto. }

              { right.
                exists (mk_eapply (mk_lam v u) e1') t'.
                dands; auto.

                - pose proof (unfold_lsubst [(vy,mk_var vx)] (mk_eapply (mk_lam v u) e1')) as h.
                  exrepnd; rw h0; clear h0; allsimpl; allrw disjoint_singleton_r.
                  apply alpha_eq_mk_eapply in h1; exrepnd; subst; allsimpl; autorewrite with slow in *; fold_terms.
                  apply implies_alpha_eq_mk_eapply.
                  + rw @lsubst_aux_trivial_cl_term; auto.
                    simpl; apply disjoint_singleton_r.
                    apply alphaeq_preserves_free_vars in h3; rw <- h3; simpl; autorewrite with slow.
                    rw in_remove_nvars; rw in_single_iff; tcsp.
                  + eapply alpha_eq_trans;[exact ih0|].
                    pose proof (unfold_lsubst [(vy,mk_var vx)] e1') as q.
                    exrepnd; rw q0; clear q0; allsimpl; allrw disjoint_singleton_r.
                    allrw in_app_iff; allrw not_over_or; repnd.
                    apply lsubst_aux_alpha_congr_same_disj; simpl; eauto 3 with slow;
                    apply disjoint_singleton_r; tcsp.

                - introv isp1 isp2; simpl; fold_terms.
                  allrw memvar_singleton; boolvar; tcsp;[].
                  pose proof (ih1 t'' td td') as h; clear ih1.
                  repeat (autodimp h hyp);[].
                  repnd; dands; auto;[|].
                  + introv comp.
                    autodimp h0 hyp.
                    allrw @two_as_app.
                    applydup@ computes_in_1step_program in comp; auto;[].
                    repeat (rw @cl_lsubst_aux_app; eauto 3 with slow;[]).
                    repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux u [(vx, t'')]));
                            [|simpl; apply disjoint_singleton_r;
                              rw @free_vars_lsubst_aux_cl; eauto 3 with slow;[];
                              simpl; rw in_remove_nvars; rw in_single_iff; tcsp];[]).
                    repeat (rw @cl_lsubst_aux_app in h0; eauto 3 with slow;[]).
                    eapply computes_in_1step_alpha_lam; auto.
                  + introv comp.
                    clear h0.
                    autodimp h hyp.
                    remember (lsubst_aux e1' [(vx, t''), (vy, td)]) as xx.
                    allunfold @computes_step_to_error.
                    destruct xx as [v1|f1|op bs]; allsimpl; ginv;[].
                    remember (compute_step lib (oterm op bs)) as cs; destruct cs; symmetry in Heqcs; ginv; tcsp;[].
                    dopid op as [can|ncan|exc|abs] SSCase; allsimpl; ginv; tcsp;[|];
                    csunf; simpl;
                    unfold compute_step_eapply; simpl; allrw; simpl; auto.
              }
          }
        }

        { destruct e1bt1lbt; allsimpl; ginv;[].
          autorewrite with slow in *.

          repndors; exrepnd; subst; ginv; fold_terms.

          - apply iscan_lsubst_aux_implies in Hcs0;
            [|simpl; introv i; repndors; tcsp; ginv; eauto 3 with slow];[].

            left.
            destruct t as [v|f|op bs]; allsimpl; ginv; tcsp;[].
            dopid op as [can|ncan|exc|abs] SSCase; allsimpl; ginv; tcsp; GC;[].
            destruct can; allsimpl; ginv; tcsp;[].
            destruct bs; allsimpl; ginv; tcsp;[].
            boolvar; ginv; GC;[].

            exists (@mk_nat p (s (Z.to_nat z))).
            introv isp; simpl; fold_terms.
            apply computes_in_1step_to_alpha.
            constructor; csunf; simpl; dcwf h; simpl; boolvar; auto; try omega.

          - apply subst_exc in Hcs0; exrepnd; subst; allsimpl.
            allapply @isprogram_exception_implies; exrepnd.
            repeat (destruct lbtc; allsimpl; ginv;[]).
            destruct b as [l1 t1].
            destruct b0 as [l2 t2].
            destruct l1; allsimpl; fold_terms; ginv.
            destruct l2; allsimpl; fold_terms; ginv.
            allsimpl; autorewrite with slow in *.

            allrw in_app_iff; allrw not_over_or; repnd.
            allrw subset_app; repnd.

            left.
            exists (mk_exception t1 t2); introv isp'.
            apply computes_in_1step_to_alpha.
            constructor; csunf; simpl; auto.

          - apply computation_mark.isnoncan_like_lsubst_aux in Hcs2.
            repndors; exrepnd; subst; allsimpl; GC.

            { allrw @singleton_subset; allrw in_single_iff; subst.
              boolvar; tcsp;[]; ginv; GC.

              right.
              exists (mk_eapply (@mk_nseq p s) (mk_var vy)) x.
              dands; auto.

              + unfold lsubst; simpl; boolvar; tcsp.

              + constructor; auto.

              + introv isp1 isp2; dands; intro comp.

                * simpl; boolvar; tcsp.
                  apply computes_in_1step_to_alpha.
                  allrw @computes_in_1step_iff_isnoncan_like; repnd; dands; tcsp;[].
                  fold_terms; unfold mk_eapply.
                  rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow;[].
                  rw comp; auto.

                * simpl; allrw memvar_singleton; boolvar; tcsp;[].
                  applydup @isprogram_error_implies_isnoncan_like in comp; auto;[].
                  allunfold @computes_step_to_error.
                  fold_terms.
                  remember (compute_step lib td) as cs; symmetry in Heqcs; destruct cs; ginv; tcsp; GC;[].
                  unfold mk_eapply; rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
                  rw Heqcs; auto. }

            { pose proof (Hind t t []) as h; clear Hind.
              repeat (autodimp h hyp); eauto 3 with slow;[].
              pose proof (h x no lbt vx vy) as ih; clear h.
              repeat (autodimp ih hyp).
              { apply computes_in_1step_if_isnoncan_like; auto.
                apply isnoncan_like_lsubst_aux; auto. }

              repndors; exrepnd.

              { left.
                exists (mk_eapply (mk_nseq s) e2'); introv isp'.
                pose proof (ih0 t') as h'; clear ih0; autodimp h' hyp.
                simpl; fold_terms.
                allrw memvar_singleton; boolvar; tcsp;[].
                eapply computes_in_1step_alpha_nseq; auto. }

              { right.
                exists (mk_eapply (mk_nseq s) e1') t'.
                dands; auto.

                - pose proof (unfold_lsubst [(vy,mk_var vx)] (mk_eapply (mk_nseq s) e1')) as h.
                  exrepnd; rw h0; clear h0; allsimpl; allrw disjoint_singleton_r.
                  apply alpha_eq_mk_eapply in h1; exrepnd; subst; allsimpl; autorewrite with slow in *; fold_terms.
                  inversion h3; subst; allsimpl; cpx; fold_terms; clear h3; allsimpl; fold_terms.
                  apply implies_alpha_eq_mk_eapply; eauto 3 with slow.
                  eapply alpha_eq_trans;[exact ih0|].
                  pose proof (unfold_lsubst [(vy,mk_var vx)] e1') as q.
                  exrepnd; rw q0; clear q0; allsimpl; allrw disjoint_singleton_r.
                  allrw in_app_iff; allrw not_over_or; repnd.
                  apply lsubst_aux_alpha_congr_same_disj; simpl; eauto 3 with slow;
                  apply disjoint_singleton_r; tcsp.

                - introv isp1 isp2; simpl; fold_terms.
                  allrw memvar_singleton; boolvar; tcsp;[].
                  pose proof (ih1 t'' td td') as h; clear ih1.
                  repeat (autodimp h hyp);[].
                  repnd; dands; auto;[|].
                  + introv comp.
                    autodimp h0 hyp.
                    allrw @two_as_app.
                    applydup@ computes_in_1step_program in comp; auto;[].
                    repeat (rw @cl_lsubst_aux_app; eauto 3 with slow;[]).
                    repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux u [(vx, t'')]));
                            [|simpl; apply disjoint_singleton_r;
                              rw @free_vars_lsubst_aux_cl; eauto 3 with slow;[];
                              simpl; rw in_remove_nvars; rw in_single_iff; tcsp];[]).
                    repeat (rw @cl_lsubst_aux_app in h0; eauto 3 with slow;[]).
                    eapply computes_in_1step_alpha_nseq; auto.
                  + introv comp.
                    clear h0.
                    autodimp h hyp.
                    remember (lsubst_aux e1' [(vx, t''), (vy, td)]) as xx.
                    allunfold @computes_step_to_error.
                    destruct xx as [v1|f1|op bs]; allsimpl; ginv;[].
                    remember (compute_step lib (oterm op bs)) as cs; destruct cs; symmetry in Heqcs; ginv; tcsp;[].
                    dopid op as [can|ncan|exc|abs] SSCase; allsimpl; ginv; tcsp;[|];
                    csunf; simpl;
                    unfold compute_step_eapply; simpl; allrw; simpl; auto.
              }
          }
        }

(*      * SCase "NApseq". left.
        clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_apseq_success in Hcs; repndors; exrepnd; subst; allsimpl.

        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        fold_terms; GC.

        exists (@mk_nat p (n n0)).
        introv Hp; allsimpl.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl.
        rw @Znat.Nat2Z.id.
        boolvar; try omega; auto.*)

      * SCase "NFix". left. clear Hind.
        csunf Hcs; allsimpl; apply compute_step_fix_success in Hcs; repnd; subst.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        allrw app_nil_r; allrw remove_nvars_nil_l.
        exists (mk_apply (oterm (Can e1bt1oc) e1bt1lbt) (mk_fix (oterm (Can e1bt1oc) e1bt1lbt))).
        introv Hp; simpl.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl.
        unfold apply_bterm.
        simpl. f_equal.

      * SCase "NSpread". left. clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_spread_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        destruct b1 as [l1 t1]; allsimpl; ginv.
        destruct b0 as [l2 t2]; allsimpl; ginv.
        destruct b2 as [l3 t3]; allsimpl; ginv.
        allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
        allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allsimpl.
        allrw not_over_or; repnd.
        allrw memvar_cons; allsimpl; boolvar; tcsp; GC;[].
        allrw subset_app; repnd.
        fold_terms.

        exists (lsubst t2 [(va,t1),(vb,t3)]).
        introv Hp; allsimpl.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl.
        unfold apply_bterm; simpl; f_equal.
        rw @lsubst_lsubst_aux; simpl;
        [|repeat (rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow); allrw app_nil_r;
          introv i j; allrw in_app_iff; repndors; allrw in_remove_nvars; allsimpl; repnd;
          allrw not_over_or; repnd; GC; try (apply Xsss1 in j0); try (apply Xsss0 in j0);
          allsimpl; complete sp].
        unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
        [|introv i j; allrw in_app_iff; repndors; try (apply Xsss1 in j); try (apply Xsss0 in j);
          allsimpl; repndors; subst; complete sp].

        rw <- (simple_lsubst_aux_lsubst_aux_sub t2 [(va,t1),(vb,t3)]); allsimpl;
        allrw memvar_cons; allsimpl; boolvar; tcsp; eauto 3 with slow.

        { introv i j; allrw in_app_iff; repndors; tcsp;
          try (apply Xsss0 in j); try (apply Xsss1 in j);
          allsimpl; repndors; subst; tcsp. }

      * SCase "NDsup". left. clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_dsup_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        destruct b1 as [l1 t1]; allsimpl; ginv.
        destruct b0 as [l2 t2]; allsimpl; ginv.
        destruct b2 as [l3 t3]; allsimpl; ginv.
        allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
        allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allsimpl.
        allrw not_over_or; repnd.
        allrw memvar_cons; allsimpl; boolvar; tcsp; GC;[].
        allrw subset_app; repnd.
        fold_terms.

        exists (lsubst t2 [(va,t1),(vb,t3)]).
        introv Hp; allsimpl.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl.
        unfold apply_bterm; simpl; f_equal.
        rw @lsubst_lsubst_aux; simpl;
        [|repeat (rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow); allrw app_nil_r;
          introv i j; allrw in_app_iff; repndors; allrw in_remove_nvars; allsimpl; repnd;
          allrw not_over_or; repnd; GC; try (apply Xsss1 in j0); try (apply Xsss0 in j0);
          allsimpl; complete sp].
        unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
        [|introv i j; allrw in_app_iff; repndors; try (apply Xsss1 in j); try (apply Xsss0 in j);
          allsimpl; repndors; subst; complete sp].

        rw <- (simple_lsubst_aux_lsubst_aux_sub t2 [(va,t1),(vb,t3)]); allsimpl;
        allrw memvar_cons; allsimpl; boolvar; tcsp; eauto 3 with slow.

        { introv i j; allrw in_app_iff; repndors; tcsp;
          try (apply Xsss0 in j); try (apply Xsss1 in j);
          allsimpl; repndors; subst; tcsp. }

      * SCase "NDecide". left. clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_decide_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        destruct b1 as [l1 u1]; allsimpl; ginv.
        destruct b as [l2 u2]; allsimpl; ginv.
        destruct b0 as [l3 u3]; allsimpl; ginv.
        allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
        allrw disjoint_singleton_l; allsimpl.
        repeat (allrw in_app_iff; allsimpl).
        allrw not_over_or; repnd.
        allrw memvar_cons; allsimpl; boolvar; tcsp; GC;[].
        allrw subset_app; repnd.
        fold_terms.

        repndors; repnd; subst; allsimpl.

        { exists (lsubst u2 [(v1,u1)]).
          introv Hp; allsimpl.
          apply computes_in_1step_to_alpha.
          constructor; csunf; simpl.
          unfold apply_bterm; simpl; f_equal.
          rw @lsubst_lsubst_aux; simpl;
          [|repeat (rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow); allrw app_nil_r;
            introv i j; allrw in_app_iff; repndors; allrw in_remove_nvars; allsimpl; repnd;
            allrw not_over_or; repnd; GC; try (apply Xsss1 in j0); try (apply Xsss0 in j0);
            allsimpl; complete sp].
          unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
          [|introv i j; allrw in_app_iff; repndors; try (apply Xsss1 in j); try (apply Xsss0 in j);
            allsimpl; repndors; subst; complete sp].

          rw <- (simple_lsubst_aux_lsubst_aux_sub u2 [(v1,u1)]); allsimpl;
          allrw memvar_cons; allsimpl; boolvar; tcsp; eauto 3 with slow.

          { introv i j; allrw in_app_iff; repndors; tcsp;
            try (apply Xsss0 in j); try (apply Xsss1 in j);
            allsimpl; repndors; subst; tcsp. }
        }

        { exists (lsubst u3 [(v2,u1)]).
          introv Hp; allsimpl.
          apply computes_in_1step_to_alpha.
          constructor; csunf; simpl.
          unfold apply_bterm; simpl; f_equal.
          rw @lsubst_lsubst_aux; simpl;
          [|repeat (rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow); allrw app_nil_r;
            introv i j; allrw in_app_iff; repndors; allrw in_remove_nvars; allsimpl; repnd;
            allrw not_over_or; repnd; GC; try (apply Xsss1 in j0); try (apply Xsss0 in j0);
            allsimpl; complete sp].
          unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
          [|introv i j; allrw in_app_iff; repndors; try (apply Xsss1 in j); try (apply Xsss0 in j);
            allsimpl; repndors; subst; complete sp].

          rw <- (simple_lsubst_aux_lsubst_aux_sub u3 [(v2,u1)]); allsimpl;
          allrw memvar_cons; allsimpl; boolvar; tcsp; eauto 3 with slow.

          { introv i j; allrw in_app_iff; repndors; tcsp;
            try (apply Xsss0 in j); try (apply Xsss1 in j);
            allsimpl; repndors; subst; tcsp. }
        }

      * SCase "NCbv". left. clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_cbv_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        destruct b as [l1 u1]; allsimpl; ginv.
        allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
        allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allsimpl.
        allrw not_over_or; repnd.
        allrw memvar_cons; allsimpl; boolvar; tcsp; GC;[].
        allrw subset_app; repnd.
        fold_terms.

        exists (lsubst u1 [(v,oterm (Can e1bt1oc) e1bt1lbt)]).
        introv Hp; allsimpl.
        apply computes_in_1step_to_alpha.
        constructor; csunf; simpl.
        unfold apply_bterm; simpl; f_equal.
        rw @lsubst_lsubst_aux; simpl;
        [|allrw app_nil_r; allrw flat_map_map; allunfold @compose;
          apply disjoint_flat_map_r; introv k; destruct x as [l u]; allsimpl;
          rw @free_vars_lsubst_aux_cl; allsimpl;
          try (complete (boolvar; allsimpl; eauto 3 with slow));
          allrw subset_flat_map; applydup Xsss0 in k; allsimpl;
          rw remove_nvars_comm; introv i j; rw in_remove_nvars in j; repnd;
          applydup k0 in j0; allsimpl; repndors; subst; tcsp;
          boolvar; allsimpl; tcsp; GC; allrw in_remove_nvars; complete sp].

        unfold subst; rw @lsubst_lsubst_aux; simpl; allrw app_nil_r;
        [|introv i j; allrw in_app_iff; repndors; try (apply Xsss1 in j); try (apply Xsss0 in j);
          allsimpl; repndors; subst; complete sp].

        rw <- (simple_lsubst_aux_lsubst_aux_sub u1 [(v,oterm (Can e1bt1oc) e1bt1lbt)]); allsimpl;
        allrw memvar_cons; allsimpl; boolvar; tcsp; eauto 3 with slow.

        { introv i j; allrw in_app_iff; repndors; tcsp;
          try (apply Xsss0 in j); try (apply Xsss1 in j);
          allsimpl; repndors; subst; tcsp. }

      * SCase "NSleep".
        allsimpl; left; clear Hind.
        apply @isprogram_sleep_implies in He1p; exrepnd; subst; cpx.
        csunf Hcs; allsimpl.
        apply compute_step_sleep_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        exists (@mk_axiom p).
        simpl; introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step; reflexivity.

      * SCase "NTUni".
        allsimpl; left; clear Hind.
        apply @isprogram_tuni_implies in He1p; exrepnd; subst; cpx.
        csunf Hcs; allsimpl.
        apply compute_step_tuni_success in Hcs; exrepnd; subst; allsimpl.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        exists (@mk_uni p n).
        simpl; introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step.
        simpl; csunf; simpl; unfold compute_step_tuni; simpl.
        destruct (Z_le_gt_dec 0 (Z.of_nat n)); try (complete omega).
        rw Znat.Nat2Z.id; auto.

      * SCase "NMinus".
        allsimpl; left; clear Hind.
        apply @isprogram_minus_implies in He1p; exrepnd; subst; cpx.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        repeat (destruct e1bt1lbt; allsimpl; ginv;[]).
        csunf Hcs; allsimpl; apply compute_step_minus_success in Hcs; exrepnd; subst; allsimpl; GC.
        exists (@mk_integer p (- z)).
        simpl; introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step.
        simpl; csunf; simpl; unfold compute_step_minus; simpl; auto.

      * SCase "NFresh".
        allsimpl; csunf Hcs; allsimpl; ginv.

      * SCase "NTryCatch".
        left; clear Hind.
        allsimpl.
        allapply @isprogram_trycatch_implies; exrepnd; subst; GC.
        repeat (destruct e1lbt; allsimpl; ginv;[]).
        destruct b1 as [l1 u1]; allsimpl; ginv.
        destruct b0 as [l2 u2]; allsimpl; ginv.
        csunf Hcs; allsimpl; ginv; allsimpl.
        allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
        allrw disjoint_singleton_l; allsimpl.
        repeat (allrw in_app_iff; allsimpl).
        allrw not_over_or; repnd.
        allrw memvar_cons; allsimpl; boolvar; tcsp; GC;[].
        allrw subset_app; repnd.
        fold_terms.
        exists (mk_atom_eq u2 u2 (oterm (Can e1bt1oc) e1bt1lbt) mk_bot).
        introv isp; simpl.
        allrw memvar_singleton; rw @simple_sub_find_beq_var.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step; reflexivity.

      * SCase "NParallel".
        allsimpl; left; clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_parallel_success in Hcs; subst; allsimpl.
        allrw remove_nvars_nil_l; allrw subset_app; repnd.
        allrw disjoint_singleton_l; allsimpl.
        repeat (allrw in_app_iff; allsimpl).
        allrw not_over_or; repnd.
        exists (@mk_axiom p); introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step; reflexivity.

      * SCase "NCompOp".
        csunf Hcs; allsimpl.
        dcwf h.
        destruct e1lbt as [| bt2 e1lbt]; allsimpl; ginv;[].
        destruct bt2 as [l t]; allsimpl.
        destruct l; allsimpl; ginv;[].
        allrw remove_nvars_nil_l.
        allrw in_app_iff; allrw not_over_or.
        allrw subset_app; repnd.
        ntermd t as [bt2v|f|o bt2lbt] SSCase.

        { SSCase "vterm".
          allsimpl.
          allrw singleton_subset; allsimpl; repndors; subst; tcsp;[].
          boolvar; tcsp.
          clear Hind.
          remember (compute_step lib (oterm (NCan no) lbt)) as t.
          destruct t; ginv;[]; allsimpl.
          right. exists (oterm (NCan (NCompOp c))
                               (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                      :: bterm [] (vterm vy) :: e1lbt))
                        n.
          symmetry in Heqt; apply c1step_nc in Heqt.

          assert (!LIn vy (free_vars_bterms e1bt1lbt)) as nivyl1.
          { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
            rw subset_flat_map in Xsss0; apply Xsss0 in i1; apply i1 in i0; allsimpl; sp. }

          assert (!LIn vy (free_vars_bterms e1lbt)) as nivyl2.
          { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
            rw subset_flat_map in Xsss; apply Xsss in i1; apply i1 in i0; allsimpl; sp. }

          assert (forall u z, lsubst_bterms_aux e1bt1lbt [(bt2v, u), (vy, z)]
                              = lsubst_bterms_aux e1bt1lbt [(bt2v, u)]) as els1.
          { introv.
            unfold lsubst_bterms_aux; apply eq_maps; introv i.
            pose proof (lsubst_bterm_aux_trim [vy] Exc e1bt1lbt) as h.
            simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
            rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

          assert (forall u z, lsubst_bterms_aux e1lbt [(bt2v, u), (vy, z)]
                              = lsubst_bterms_aux e1lbt [(bt2v, u)]) as els2.
          { introv.
            unfold lsubst_bterms_aux; apply eq_maps; introv i.
            pose proof (lsubst_bterm_aux_trim [vy] Exc e1lbt) as h.
            simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
            rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

          dands; tcsp.
          { unfold lsubst; simpl; boolvar; allrw disjoint_singleton_r; allrw in_app_iff;
            allrw not_over_or; repnd; tcsp; GC; try (complete (provefalse; sp));[].
            apply isprogram_compop_implies in He1p; exrepnd.
            repeat (destruct e1lbt; allsimpl; ginv).
            destruct b0, b1; allsimpl; ginv; allsimpl.
            allrw remove_nvars_nil_l; allrw app_nil_r.
            allrw subset_app; allrw disjoint_singleton_r; allrw in_app_iff; allrw not_over_or; repnd.
            allsimpl; GC.
            repeat prove_alpha_eq4; cpx;
            try (complete (rw @lsubst_aux_trivial_cl_term; simpl; auto;
                           apply disjoint_singleton_r; introv i;
                           try (apply Xsss1 in i); try (apply Xsss in i);
                           allsimpl; tcsp)).
            rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
            pose proof (nth_in _ n2 e1bt1lbt default_bt) as i; autodimp i hyp.
            remember (nth n2 e1bt1lbt default_bt) as b; clear Heqb.
            rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
            apply disjoint_singleton_r; introv j.
            rw subset_flat_map in Xsss0; apply Xsss0 in i; apply i in j; allsimpl; sp.
          }

          introv Hprt'' Hprtd; dands; introv Hcsd; allsimpl; boolvar; tcsp; GC;[|].

          { apply computes_in_1step_to_alpha.
            constructor; csunf; simpl.
            dcwf h;[]; allsimpl.
            invertsn Hcsd; rw Hcsd; simpl; auto; allrw @fold_lsubst_bterms_aux;
            allrw els1; allrw els2; auto. }

          { allunfold @computes_step_to_error.
            destruct td as [v|f|op bs];
              try (allrw @isprogram_vterm; tcsp);
              try (complete (allsimpl; tcsp));[].

            dopid op as [can|ncan|exc|abs] Case.
            - allsimpl; tcsp.
            - rw @compute_step_ncompop_ncan2.
              dcwf h;[].
              remember (compute_step lib (oterm (NCan ncan) bs)) as cs; destruct cs; tcsp.
            - allsimpl; tcsp.
            - rw @compute_step_ncompop_abs2.
              csunf Hcsd; allsimpl.
              dcwf h;[].
              remember (compute_step_lib lib abs bs) as cs; destruct cs; tcsp.
          }
        }

        { SSCase "sterm".
          allsimpl; GC; ginv. }

        { SSCase "oterm".

          dopid o as [e1bt2oc | e1bt2on | e1bt2oe | e1bt2oa] SSSSCase.

          - SSSSCase "Can". left. clear Hind.
            csunf Hcs; allsimpl.
            apply compute_step_compop_success_can_can in Hcs; exrepnd.
            repeat (destruct e1lbt; allsimpl; ginv).
            repeat (destruct e1bt1lbt; allsimpl; ginv).
            repeat (destruct bt2lbt; allsimpl; ginv).
            destruct b as [l1 u1]; destruct b0 as [l2 u2]; allsimpl; allunfold @nobnd; ginv.
            allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; allrw subset_app; repnd.
            allrw in_app_iff; allrw not_over_or; repnd; GC.
            repndors; exrepnd; subst; allsimpl;
            allrw @get_param_from_cop_some; subst; GC;
            allrw in_app_iff; allrw not_over_or; repnd.
            + exists (if Z_lt_le_dec n1 n2 then u1 else u2); introv isp.
              apply computes_in_1step_to_alpha; constructor; simpl; csunf; simpl.
              dcwf h.
              unfold compute_step_comp; simpl; boolvar; tcsp.
            + exists (if param_kind_deq pk1 pk2 then u1 else u2); introv isp.
              apply computes_in_1step_to_alpha; constructor; simpl; csunf; simpl.
              dcwf h.
              unfold compute_step_comp; simpl.
              allrw @get_param_from_cop_pk2can; boolvar; tcsp.

          - SSSSCase "NCan".
            allsimpl.
            allrw @co_wf_def_map.
            allrw @fold_lsubst_bterms_aux.
            remember (compute_step lib (oterm (NCan e1bt2on)
                                              (lsubst_bterms_aux bt2lbt [(vx, oterm (NCan no) lbt)]))) as t.
            allsimpl.
            destruct t as [crt| ?]; ginv;[].
            symmetry in Heqt; apply @c1step_nc in Heqt.
            rw <- @computation2.lsubst_aux_oterm in Heqt.
            eapply Hind with (lv:=nil) in Heqt;eauto 3 with slow;[].
            repndors;[left | right ]; exrepnd.

            { exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                   :: bterm [] e2'
                                   :: e1lbt)).
              introv Hp.
              apply Heqt0 in Hp; simpl in Hp; invertsn Hp.
              destruct Hp as [Hp aeq].
              invertsn Hp; allsimpl.
              eexists; dands.
              { constructor; csunf; simpl; dcwf h; simpl;
                allrw @fold_lsubst_bterms_aux;
                try (rw Hp; simpl; eauto). }
              unfold lsubst_bterms_aux.
              prove_alpha_eq4.
              introv z; allrw map_length.
              repeat (destruct n; cpx; tcsp).
              prove_alpha_eq4.
              complete auto.
            }

            assert (!LIn vy (free_vars_bterms e1bt1lbt)) as nivyl1.
            { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
              rw subset_flat_map in Xsss0; apply Xsss0 in i1; apply i1 in i0; allsimpl; sp. }

            assert (!LIn vy (free_vars_bterms e1lbt)) as nivyl2.
            { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
              rw subset_flat_map in Xsss; apply Xsss in i1; apply i1 in i0; allsimpl; sp. }

            assert (forall u z, lsubst_bterms_aux e1bt1lbt [(vx, u), (vy, z)]
                                = lsubst_bterms_aux e1bt1lbt [(vx, u)]) as els1.
            { introv.
              unfold lsubst_bterms_aux; apply eq_maps; introv i.
              pose proof (lsubst_bterm_aux_trim [vy] Exc e1bt1lbt) as h.
              simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
              rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

            assert (forall u z, lsubst_bterms_aux e1lbt [(vx, u), (vy, z)]
                                = lsubst_bterms_aux e1lbt [(vx, u)]) as els2.
            { introv.
              unfold lsubst_bterms_aux; apply eq_maps; introv i.
              pose proof (lsubst_bterm_aux_trim [vy] Exc e1lbt) as h.
              simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
              rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

            exists (oterm (NCan (NCompOp c))
                          (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                 :: bterm [] e1'
                                 :: e1lbt)) t'.
            dands; auto; [SSSSSCase "left" | SSSSSCase "right"].

            { SSSSSSCase "left".
              match goal with
                | [ |- alpha_eq ?l (lsubst (oterm ?o (?bt1 :: bterm [] ?nnt2 :: ?rlbt)) ?sub) ]
                  => apply alpha_eq_trans with
                     (nt2:= oterm o ((lsubst_bterm_aux bt1 sub)
                                       :: (bterm [] (lsubst nnt2 sub))
                                       :: (map (fun t : BTerm => lsubst_bterm_aux t sub) rlbt)));
                    auto;
                    [|apply lsubst_over_alpha_bt2; simpl;apply disjoint_singleton_r; sp;fail]

              end.

              repeat(prove_alpha_eq4).

              { rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
                pose proof (nth_in _ n e1bt1lbt default_bt) as i; autodimp i hyp; try omega.
                remember (nth n e1bt1lbt default_bt) as b; clear Heqb.
                rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
                apply disjoint_singleton_r; introv j.
                rw subset_flat_map in Xsss0; apply Xsss0 in i; apply i in j; allsimpl; sp.
              }

              { rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
                pose proof (nth_in _ n e1lbt default_bt) as i; autodimp i hyp; try omega.
                remember (nth n e1lbt default_bt) as b; clear Heqb.
                rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
                apply disjoint_singleton_r; introv j.
                rw subset_flat_map in Xsss; apply Xsss in i; apply i in j; allsimpl; sp.
              }
            }

            { SSSSSCase "right".

              introv Hpt'' Hptf.
              dands; introv Hcsd.

              { applydup @computes_in_1step_program in Hcsd as Htd'p; auto.
                apply Heqt1 with (t'':=t'') in Hcsd; auto.
                simpl in Xsss. repeat(disjoint_consl).
                simpl.
                allrw @fold_lsubst_bterms_aux.
                unfold computes_in_1step_alpha in Hcsd; exrepnd.
                invertsna Hcsd1 Hcc.

                - exists (oterm (NCan (NCompOp c))
                                (bterm []
                                       (oterm (Can e1bt1oc)
                                              (lsubst_bterms_aux e1bt1lbt [(vx, t''), (vy, td')]))
                                       :: bterm [] t2a
                                       :: lsubst_bterms_aux e1lbt [(vx, t''), (vy, td')])).
                  dands;[|complete (repeat prove_alpha_eq4)].
                  constructor.
                  allrw els1; allrw els2; auto.
                  unfold lsubst_bterms_aux.
                  csunf; simpl.
                  dcwf h;[].
                  rw Hcc; simpl; auto.

                - exists (oterm (NCan (NCompOp c))
                                (bterm []
                                       (oterm (Can e1bt1oc)
                                              (lsubst_bterms_aux e1bt1lbt [(vx, t''), (vy, td')]))
                                       :: bterm [] t2a
                                       :: lsubst_bterms_aux e1lbt [(vx, t''), (vy, td')])).
                  dands;[|complete (repeat prove_alpha_eq4)].
                  constructor.
                  allrw els1; allrw els2; auto.
                  unfold lsubst_bterms_aux.
                  csunf; simpl.
                  dcwf h;[].
                  rw Hcc; simpl; auto.
              }

              { apply Heqt1 with (t'':=t'') in Hcsd; auto.
                simpl.
                allrw @fold_lsubst_bterms_aux.
                allrw els1; allrw els2; auto.
                allunfold @computes_step_to_error.
                remember (lsubst_aux e1' [(vx, t''), (vy, td)]) as t; symmetry in Heqt.
                destruct t as [v|f|op bs]; allsimpl; tcsp; GC;[|].
                { csunf; simpl; dcwf h. }
                dopid op as [can|ncan|exc|abs] Case; allsimpl; tcsp.
                - rw @compute_step_ncompop_ncan2.
                  dcwf h;[].
                  remember (compute_step lib (oterm (NCan ncan) bs)) as cs; symmetry in Heqcs.
                  destruct cs; tcsp.
                - rw @compute_step_ncompop_abs2.
                  dcwf h;[].
                  csunf Hcsd; allsimpl.
                  remember (compute_step_lib lib abs bs) as cs; symmetry in Heqcs.
                  destruct cs; tcsp.
              }
            }

          - SSSSCase "Exc".
            left. clear Hind.
            csunf Hcs; allsimpl; ginv.
            allapply @isprogram_compop_implies; exrepnd.
            repeat (destruct e1lbt; allsimpl; cpx).
            destruct b0; destruct b; allsimpl; cpx.
            allapply @isprogram_exception_implies; exrepnd.
            repeat (destruct bt2lbt; allsimpl; ginv).
            destruct b; destruct b0; allsimpl; cpx.
            allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
            exists (mk_exception n1 n2); introv isp.
            apply computes_in_1step_to_alpha.
            rw <- @compute_1_step_is_computes_in_1step.
            simpl; csunf; simpl; dcwf h; auto.

          - SSSSCase "Abs".

            allsimpl.
            csunf Hcs; allsimpl.

            remember (compute_step_lib
                        lib e1bt2oa
                        (map
                           (fun t : BTerm =>
                              lsubst_bterm_aux t [(vx, oterm (NCan no) lbt)]) bt2lbt)) as clib.
            destruct clib; inversion Hcs; subst; GC.
            symmetry in Heqclib.
            apply compute_step_lib_success in Heqclib; exrepnd; subst.

            left.
            pose proof (change_bvars_alpha_eq_lib [vx] lib) as ch; exrepnd.
            eapply found_entry_alpha_eq_lib in Heqclib0; eauto; exrepnd.

            exists (oterm (NCan (NCompOp c))
                          ((bterm [] (oterm (Can e1bt1oc) e1bt1lbt))
                             :: (bterm [] (mk_instance vars2 bt2lbt rhs2))
                             :: e1lbt)).
            introv isp; simpl.
            eapply computes_in_1step_alpha_lib; eauto with slow.
            exists (oterm (NCan (NCompOp c))
                          ((bterm [] (oterm (Can e1bt1oc) (map (fun t => lsubst_bterm_aux t [(vx, t')]) e1bt1lbt)))
                             :: (bterm [] (mk_instance vars2 (map (fun t => lsubst_bterm_aux t [(vx, t')]) bt2lbt) rhs2))
                             :: map (fun t => lsubst_bterm_aux t [(vx, t')]) e1lbt)).
            dands.

            { apply c1step_nc.
              rw @compute_step_ncompop_abs2.
              dcwf h;[].
              simpl.
              dup Heqclib1 as fe.
              apply compute_step_lib_success_change_bs with (bs2 := map (fun t : BTerm => lsubst_bterm_aux t [(vx, t')]) bt2lbt)
                in Heqclib1;
                [ | repeat (rw map_map); unfold compose, num_bvars;
                    apply eq_maps; introv i; destruct x; simpl; auto ].
              rw Heqclib1; auto. }

            { prove_alpha_eq4.
              allrw map_length.
              introv i.
              destruct n; cpx.
              destruct n; cpx.
              prove_alpha_eq4.
              dup Heqclib1 as fe.
              apply found_entry_change_bs with (bs2 := bt2lbt) in fe; auto;
              [|rw map_map; unfold compose;
                apply eq_maps; introv ib; destruct x; simpl;
                unfold num_bvars; simpl; auto];[].
              allunfold @correct_abs; repnd.
              apply alpha_eq_sym.
              allrw @fold_lsubst_bterms_aux.
              apply alpha_eq_lsubst_aux_mk_instance; simpl; eauto with slow.
              apply found_entry_implies_matching_entry in fe.
              unfold matching_entry in fe; repnd; auto.
            }
        }

      * SCase "NArithOp".
        csunf Hcs; allsimpl.
        dcwf h;[].

        destruct e1lbt as [| bt2 e1lbt];allsimpl;ginv;[].
        destruct bt2 as [l t]; allsimpl.
        destruct l; allsimpl; ginv;[].
        allsimpl; allrw remove_nvars_nil_l.
        allrw in_app_iff; allrw not_over_or.
        allrw subset_app; repnd.
        ntermd t as [bt2v|f|o bt2lbt] SSCase.

        { SSCase "vterm".
          allsimpl.
          allrw singleton_subset; allsimpl; repndors; subst; tcsp;[].
          boolvar; tcsp.
          clear Hind.
          remember (compute_step lib (oterm (NCan no) lbt)) as t.
          destruct t; ginv;[]; allsimpl.
          right. exists (oterm (NCan (NArithOp a))
                               (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                      :: bterm [] (vterm vy) :: e1lbt))
                        n.
          symmetry in Heqt; apply c1step_nc in Heqt.

          assert (!LIn vy (free_vars_bterms e1bt1lbt)) as nivyl1.
          { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
            rw subset_flat_map in Xsss0; apply Xsss0 in i1; apply i1 in i0; allsimpl; sp. }

          assert (!LIn vy (free_vars_bterms e1lbt)) as nivyl2.
          { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
            rw subset_flat_map in Xsss; apply Xsss in i1; apply i1 in i0; allsimpl; sp. }

          assert (forall u z, lsubst_bterms_aux e1bt1lbt [(bt2v, u), (vy, z)]
                              = lsubst_bterms_aux e1bt1lbt [(bt2v, u)]) as els1.
          { introv.
            unfold lsubst_bterms_aux; apply eq_maps; introv i.
            pose proof (lsubst_bterm_aux_trim [vy] Exc e1bt1lbt) as h.
            simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
            rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

          assert (forall u z, lsubst_bterms_aux e1lbt [(bt2v, u), (vy, z)]
                              = lsubst_bterms_aux e1lbt [(bt2v, u)]) as els2.
          { introv.
            unfold lsubst_bterms_aux; apply eq_maps; introv i.
            pose proof (lsubst_bterm_aux_trim [vy] Exc e1lbt) as h.
            simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
            rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

          dands; tcsp.
          { unfold lsubst; simpl; boolvar; allrw disjoint_singleton_r;
            allrw in_app_iff; allrw not_over_or; repnd; tcsp;
            try (complete (provefalse; sp));[].
            apply isprogram_arithop_implies in He1p; exrepnd.
            repeat (destruct e1lbt; allsimpl; ginv); GC.
            repeat prove_alpha_eq4; cpx;
            try (complete (rw @lsubst_aux_trivial_cl_term; simpl; auto;
                           apply disjoint_singleton_r; introv i;
                           try (apply Xsss1 in i); try (apply Xsss in i);
                           allsimpl; tcsp)).
            rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
            pose proof (nth_in _ n0 e1bt1lbt default_bt) as i; autodimp i hyp.
            remember (nth n0 e1bt1lbt default_bt) as b; clear Heqb.
            rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
            apply disjoint_singleton_r; introv j.
            rw subset_flat_map in Xsss0; apply Xsss0 in i; apply i in j; allsimpl; sp.
          }

          introv Hprt'' Hprtd; dands; introv Hcsd; allsimpl; boolvar; tcsp; GC;[|].

          { apply computes_in_1step_to_alpha.
            constructor; csunf; simpl.
            dcwf h;[].
            invertsn Hcsd; rw Hcsd; simpl; auto; allrw @fold_lsubst_bterms_aux;
            allrw els1; allrw els2; auto. }

          { allunfold @computes_step_to_error.
            destruct td as [v|f|op bs]; try (allrw @isprogram_vterm;tcsp);[|].
            { allsimpl; tcsp. }
            dopid op as [can|ncan|exc|abs] Case.
            - allsimpl; tcsp.
            - rw @compute_step_narithop_ncan2.
              dcwf h;[].
              remember (compute_step lib (oterm (NCan ncan) bs)) as cs; destruct cs; tcsp.
            - allsimpl; tcsp.
            - rw @compute_step_narithop_abs2.
              csunf Hcsd; allsimpl.
              dcwf h;[].
              remember (compute_step_lib lib abs bs) as cs; destruct cs; tcsp.
          }
        }

        { SSCase "sterm".
          allsimpl; GC; ginv. }

        { SSCase "oterm".

          dopid o as [e1bt2oc | e1bt2on | e1bt2oe | e1bt2oa] SSSSCase.

          - SSSSCase "Can". left. clear Hind.
            csunf Hcs; allsimpl.
            apply compute_step_arithop_success_can_can in Hcs; exrepnd.
            repeat (destruct e1lbt; allsimpl; ginv).
            repeat (destruct e1bt1lbt; allsimpl; ginv).
            repeat (destruct bt2lbt; allsimpl; ginv).
            repndors; exrepnd; subst; allsimpl;
            allapply @get_param_from_cop_pki; subst;
            allapply @get_param_from_cop_pka; subst;
            allapply @get_param_from_cop_pks; subst;
            allrw disjoint_app_l; repnd.
            exists (@mk_integer p (get_arith_op a n1 n2)); introv isp.
            apply computes_in_1step_to_alpha; constructor; simpl; csunf; simpl.
            unfold compute_step_comp; simpl; boolvar; tcsp.

          - SSSSCase "NCan".
            allsimpl.
            allrw @ca_wf_def_map.
            allrw @fold_lsubst_bterms_aux.
            remember (compute_step lib (oterm (NCan e1bt2on)
                                              (lsubst_bterms_aux bt2lbt [(vx, oterm (NCan no) lbt)]))) as t.
            allsimpl.
            destruct t as [crt| ?]; ginv.
            symmetry in Heqt; apply @c1step_nc in Heqt.
            rw <- @computation2.lsubst_aux_oterm in Heqt.
            eapply Hind with (lv:=nil) in Heqt;eauto 3 with slow;[].

            repndors;[left | right ]; exrepnd.

            { exists (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                   :: bterm [] e2'
                                   :: e1lbt)).
              introv Hp.
              apply Heqt0 in Hp; simpl in Hp; invertsn Hp.
              destruct Hp as [Hp aeq].
              invertsn Hp; allsimpl.
              eexists; dands.
              { constructor; csunf; simpl; dcwf h; simpl;
                allrw @fold_lsubst_bterms_aux;
                try (rw Hp; simpl; eauto). }
              unfold lsubst_bterms_aux.
              prove_alpha_eq4.
              introv z; allrw map_length.
              repeat (destruct n; cpx; tcsp).
              prove_alpha_eq4.
              complete auto.
            }

            assert (!LIn vy (free_vars_bterms e1bt1lbt)) as nivyl1.
            { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
              rw subset_flat_map in Xsss0; apply Xsss0 in i1; apply i1 in i0; allsimpl; sp. }

            assert (!LIn vy (free_vars_bterms e1lbt)) as nivyl2.
            { introv i; unfold free_vars_bterms in i; rw lin_flat_map in i; exrepnd.
              rw subset_flat_map in Xsss; apply Xsss in i1; apply i1 in i0; allsimpl; sp. }

            assert (forall u z, lsubst_bterms_aux e1bt1lbt [(vx, u), (vy, z)]
                                = lsubst_bterms_aux e1bt1lbt [(vx, u)]) as els1.
            { introv.
              unfold lsubst_bterms_aux; apply eq_maps; introv i.
              pose proof (lsubst_bterm_aux_trim [vy] Exc e1bt1lbt) as h.
              simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
              rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

            assert (forall u z, lsubst_bterms_aux e1lbt [(vx, u), (vy, z)]
                                = lsubst_bterms_aux e1lbt [(vx, u)]) as els2.
            { introv.
              unfold lsubst_bterms_aux; apply eq_maps; introv i.
              pose proof (lsubst_bterm_aux_trim [vy] Exc e1lbt) as h.
              simpl in h; rw disjoint_singleton_r in h; autodimp h hyp.
              rw h; simpl; allrw memvar_singleton; boolvar; tcsp. }

            exists (oterm (NCan (NArithOp a))
                          (bterm [] (oterm (Can e1bt1oc) e1bt1lbt)
                                 :: bterm [] e1'
                                 :: e1lbt)) t'.
            dands; auto; [SSSSSCase "left" | SSSSSCase "right"].

            { SSSSSSCase "left".
              match goal with
                | [ |- alpha_eq ?l (lsubst (oterm ?o (?bt1 :: bterm [] ?nnt2 :: ?rlbt)) ?sub) ]
                  => apply alpha_eq_trans with
                     (nt2:= oterm o ((lsubst_bterm_aux bt1 sub)
                                       :: (bterm [] (lsubst nnt2 sub))
                                       :: (map (fun t : BTerm => lsubst_bterm_aux t sub) rlbt)));
                    auto;
                    [|apply lsubst_over_alpha_bt2; simpl;allrw disjoint_singleton_r; sp;fail]

              end.

              repeat(prove_alpha_eq4).

              { rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
                pose proof (nth_in _ n e1bt1lbt default_bt) as i; autodimp i hyp; try omega.
                remember (nth n e1bt1lbt default_bt) as b; clear Heqb.
                rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
                apply disjoint_singleton_r; introv j.
                rw subset_flat_map in Xsss0; apply Xsss0 in i; apply i in j; allsimpl; sp.
              }

              { rw (map_nth2 BTerm (@BTerm p) (@default_bt p)); auto.
                pose proof (nth_in _ n e1lbt default_bt) as i; autodimp i hyp; try omega.
                remember (nth n e1lbt default_bt) as b; clear Heqb.
                rw @lsubst_bterm_aux_trivial_cl_term; simpl; auto.
                apply disjoint_singleton_r; introv j.
                rw subset_flat_map in Xsss; apply Xsss in i; apply i in j; allsimpl; sp.
              }
            }

            { SSSSSCase "right".

              introv Hpt'' Hptf.
              dands; introv Hcsd.

              { applydup @computes_in_1step_program in Hcsd as Htd'p; auto.
                apply Heqt1 with (t'':=t'') in Hcsd; auto.
                allsimpl. repeat(disjoint_consl).
                allrw @fold_lsubst_bterms_aux.
                unfold computes_in_1step_alpha in Hcsd; exrepnd.
                invertsna Hcsd1 Hcc.

                - exists (oterm (NCan (NArithOp a))
                                (bterm []
                                       (oterm (Can e1bt1oc)
                                              (lsubst_bterms_aux e1bt1lbt [(vx, t''), (vy, td')]))
                                       :: bterm [] t2a
                                       :: lsubst_bterms_aux e1lbt [(vx, t''), (vy, td')])).
                  dands;[|complete (repeat prove_alpha_eq4)].
                  constructor.
                  allrw els1; allrw els2; auto.
                  unfold lsubst_bterms_aux.
                  csunf; simpl.
                  dcwf h;[].
                  rw Hcc; simpl; auto.

                - exists (oterm (NCan (NArithOp a))
                                (bterm []
                                       (oterm (Can e1bt1oc)
                                              (lsubst_bterms_aux e1bt1lbt [(vx, t''), (vy, td')]))
                                       :: bterm [] t2a
                                       :: lsubst_bterms_aux e1lbt [(vx, t''), (vy, td')])).
                  dands;[|complete (repeat prove_alpha_eq4)].
                  constructor.
                  allrw els1; allrw els2; auto.
                  unfold lsubst_bterms_aux.
                  csunf; simpl.
                  dcwf h;[].
                  rw Hcc; simpl; auto.
              }

              { apply Heqt1 with (t'':=t'') in Hcsd; auto.
                simpl.
                allrw @fold_lsubst_bterms_aux.
                allrw els1; allrw els2; auto.
                allunfold @computes_step_to_error.
                remember (lsubst_aux e1' [(vx, t''), (vy, td)]) as t; symmetry in Heqt.
                destruct t as [v|f|op bs]; allsimpl; tcsp; GC;[|].
                { csunf; simple; dcwf h. }
                dopid op as [can|ncan|exc|abs] Case; allsimpl; tcsp.
                - rw @compute_step_narithop_ncan2.
                  dcwf h;[].
                  remember (compute_step lib (oterm (NCan ncan) bs)) as cs; symmetry in Heqcs.
                  destruct cs; tcsp.
                - rw @compute_step_narithop_abs2.
                  csunf Hcsd; allsimpl.
                  dcwf h;[].
                  remember (compute_step_lib lib abs bs) as cs; symmetry in Heqcs.
                  destruct cs; tcsp.
              }
            }

          - SSSSCase "Exc".
            left. clear Hind.
            csunf Hcs; allsimpl; ginv.
            allapply @isprogram_arithop_implies; exrepnd.
            repeat (destruct e1lbt; allsimpl; cpx).
            allapply @isprogram_exception_implies; exrepnd.
            repeat (destruct bt2lbt; allsimpl; ginv).
            destruct b; destruct b0; allsimpl; cpx.
            allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl.
            exists (mk_exception n n0); introv isp.
            apply computes_in_1step_to_alpha.
            rw <- @compute_1_step_is_computes_in_1step.
            simpl; csunf; simpl; dcwf h; auto.

          - SSSSCase "Abs".

            allsimpl.
            csunf Hcs; allsimpl.

            remember (compute_step_lib
                        lib e1bt2oa
                        (map
                           (fun t : BTerm =>
                              lsubst_bterm_aux t [(vx, oterm (NCan no) lbt)]) bt2lbt)) as clib.
            destruct clib; inversion Hcs; subst; GC.
            symmetry in Heqclib.
            apply compute_step_lib_success in Heqclib; exrepnd; subst.

            left.
            pose proof (change_bvars_alpha_eq_lib [vx] lib) as ch; exrepnd.
            eapply found_entry_alpha_eq_lib in Heqclib0; eauto; exrepnd.

            exists (oterm (NCan (NArithOp a))
                          ((bterm [] (oterm (Can e1bt1oc) e1bt1lbt))
                             :: (bterm [] (mk_instance vars2 bt2lbt rhs2))
                             :: e1lbt)).
            introv isp; simpl.
            eapply computes_in_1step_alpha_lib; eauto with slow.
            exists (oterm (NCan (NArithOp a))
                          ((bterm [] (oterm (Can e1bt1oc) (map (fun t => lsubst_bterm_aux t [(vx, t')]) e1bt1lbt)))
                             :: (bterm [] (mk_instance vars2 (map (fun t => lsubst_bterm_aux t [(vx, t')]) bt2lbt) rhs2))
                             :: map (fun t => lsubst_bterm_aux t [(vx, t')]) e1lbt)).
            dands.

            { apply c1step_nc.
              rw @compute_step_narithop_abs2.
              dcwf h;[].
              simpl.
              dup Heqclib1 as fe.
              apply compute_step_lib_success_change_bs with (bs2 := map (fun t : BTerm => lsubst_bterm_aux t [(vx, t')]) bt2lbt)
                in Heqclib1;
                [ | repeat (rw map_map); unfold compose, num_bvars;
                    apply eq_maps; introv i; destruct x; simpl; auto ].
              rw Heqclib1; auto. }

            { prove_alpha_eq4.
              allrw map_length.
              introv i.
              destruct n; cpx.
              destruct n; cpx.
              prove_alpha_eq4.
              dup Heqclib1 as fe.
              apply found_entry_change_bs with (bs2 := bt2lbt) in fe; auto;
              [|rw map_map; unfold compose;
                apply eq_maps; introv ib; destruct x; simpl;
                unfold num_bvars; simpl; auto];[].
              allunfold @correct_abs; repnd.
              apply alpha_eq_sym.
              allrw @fold_lsubst_bterms_aux.
              apply alpha_eq_lsubst_aux_mk_instance; simpl; eauto with slow.
              apply found_entry_implies_matching_entry in fe.
              unfold matching_entry in fe; repnd; auto.
            }
        }

      * SCase "NCanTest".
        left. clear Hind.
        csunf Hcs; allsimpl.
        apply compute_step_can_test_success in Hcs; exrepnd; subst.
        destruct e1lbt as [| bt2 e1lbt]; allsimpl; ginv;[].
        destruct e1lbt as [| bt3 e1lbt]; allsimpl; ginv;[].
        destruct e1lbt; allsimpl; ginv;[].
        destructbtdeep bt2 Hcs0.
        destructbtdeep bt3 Hcs0.
        allrw remove_nvars_nil_l; allrw app_nil_r.
        exists (if canonical_form_test_for c e1bt1oc then bt2nt else bt3nt).
        introv Hp; simpl.
        apply computes_in_1step_to_alpha.
        constructor.
        csunf; simpl.
        destruct (canonical_form_test_for c e1bt1oc); auto.

    + rw @compute_step_ncan_ncan in Hcs.
      allrw @fold_lsubst_bterms_aux.
      remember (compute_step lib (oterm (NCan e1bt1on) (lsubst_bterms_aux e1bt1lbt [(vx, oterm (NCan no) lbt)]))) as t.
      destruct t; symmetry in Heqt; ginv; [].
      rw <- @fold_lsubst_bterms_aux in Heqt.
      apply @c1step_nc in Heqt.
      rw @fold_lsubst_bterms_aux in Heqt.
      rw <- @computation2.lsubst_aux_oterm in Heqt.
      simpl in Hd, nivy; allrw in_app_iff; allrw not_over_or; repnd.
      eapply Hind with (lv:=nil) in Heqt; try (left; sp; fail); eauto 3 with slow;[|];
      [|allsimpl;repeat(decomp_progh2); show_hyps;sp
      ];[].
      repndors; exrepnd.

      * left.
        exists (oterm (NCan e1o) (bterm [] (e2') :: e1lbt)).
        introv Hp.
        apply Heqt0 in Hp. simpl in Hp.
        invertsn Hp.
        destruct Hp as [Hp aeq]; invertsn Hp; simpl in Hp; simpl.
        eexists; dands.
        { constructor; csunf; simpl; rw Hp; simpl; eauto. }
        clear Hp; prove_alpha_eq4.
        introv z.
        allrw map_length.
        destruct n0; auto.
        prove_alpha_eq4; complete auto.

      * right.
        exists (oterm (NCan e1o) (bterm [] e1' :: e1lbt)) t'.
        dands; try (sp; fail); [SCase "left" | SCase "right"].

        { SCase "left".
          match goal with
          | [ |- alpha_eq ?l (lsubst (oterm ?o ((bterm [] ?nt)::?lbt)) ?sub) ]
            => apply alpha_eq_trans with (nt2:= (oterm o ((bterm [] (lsubst nt sub))
                                                            :: (map (fun t : BTerm => lsubst_bterm_aux t sub) lbt) ))); auto;
               [|apply lsubst_over_alpha_bt1; simpl;allrw disjoint_singleton_r; sp; fail]
          end.
          repeat(prove_alpha_eq4). repeat(fold_selectbt). rw @selectbt_map;[|omega].
          rw  Xss; [ | right;apply selectbt_in;omega];[].
          simpl. autorewrite with slow; rw @lsubst_bterm_aux_trivial. apply alphaeqbt_refl;fail.
        }

        { SCase "right".
          introv Hpt'' Hptd.
          dands; introv Hcsd.

          - applydup @computes_in_1step_program in Hcsd as Htd'p; auto.
            duplicate Hcsd as Hcsdb.
            apply Heqt1 with(t'':=t'') in Hcsd; auto;[].
            unfold computes_in_1step_alpha in Hcsd; exrepnd.
            allsimpl.
            allrw @fold_lsubst_bterms_aux.
            exists (oterm (NCan e1o)
                          (bterm [] t2a
                                 :: lsubst_bterms_aux e1lbt [(vx, t''), (vy, td')])).
            dands;[|complete (repeat prove_alpha_eq4)].
            apply @computes_in_1step_prinarg
            with (op:= e1o)
                   (lbt:= lsubst_bterms_aux e1lbt [(vx, t''), (vy, td)]) in Hcsd1; eauto.
            clear Heqt2.
            invertsn Hcsdb.

            + apply preserve_compute_step in Hcsdb;[| trivial].
              match goal with
                | [ H : computes_in_1step ?lib ?l ?r1 |- computes_in_1step ?lib ?l ?r2] =>
                  assert (r2=r1) as Heq;[| rw Heq; trivial]
              end.
              f_equal. f_equal.
              apply eq_maps_bt; auto. introv Hlt.
              let tac2 :=  apply prog_sub_disjoint_bv_sub; prove_sub_range_sat in
              let tac3 := right;apply selectbt_in;omega in
              rw Xss; [simpl | tac3];[];
              symmetry; rw Xss; simpl;
              autorewrite with slow;[| tac3];sp.

            + apply preserve_compute_step in Hcsdb;[| trivial].
              match goal with
                | [ H : computes_in_1step ?lib ?l ?r1 |- computes_in_1step ?lib ?l ?r2] =>
                  assert (r2=r1) as Heq;[| rw Heq; trivial]
              end.
              f_equal. f_equal.
              apply eq_maps_bt; auto. introv Hlt.
              let tac2 := apply prog_sub_disjoint_bv_sub; prove_sub_range_sat in
              let tac3 := right;apply selectbt_in;omega in
              rw Xss; [simpl | tac3];[]; symmetry; rw Xss; simpl; autorewrite with slow;[| tac3];sp.

          - apply Heqt1 with (t'':=t'') in Hcsd; auto.
            simpl; remember ((lsubst_aux e1' [(vx, t''), (vy, td)])) as tdd.
            allunfold @computes_step_to_error.
            destruct tdd as [?|?|tdoo tdlbt]; allsimpl; tcsp;[].
            destruct tdoo as [c|nc|e|a]; allsimpl; tcsp.
            + rw @compute_step_ncan_ncan.
              remember (compute_step lib (oterm (NCan nc) tdlbt)) as cs; destruct cs; tcsp.
            + csunf Hcsd; allsimpl.
              rw @compute_step_ncan_abs.
              remember (compute_step_lib lib a tdlbt) as cs; destruct cs; tcsp.
        }

    + csunf Hcs; allsimpl.
      apply compute_step_catch_success in Hcs.
      repndors; exrepnd; subst.

      * repeat (destruct e1lbt; allsimpl; ginv).
        destruct b0; destruct b1; allsimpl; ginv.
        repeat (destruct e1bt1lbt; allsimpl; ginv).
        destruct b; destruct b0; allsimpl; cpx.
        allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        allrw in_app_iff; allsimpl; allrw not_over_or; repnd; GC.
        allrw memvar_singleton; boolvar; tcsp;[].
        allrw subset_app; repnd.

        left.
        exists (mk_atom_eq n n1 (subst n0 v n2) (mk_exception n1 n2)); introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step.
        simpl.
        csunf; simpl.
        unfold mk_atom_eq, nobnd;repeat(f_equal;[]).
        unfold subst.
        apply @isprogram_try_iff in He1p; repnd.
        apply @isprogram_exception_iff in He1p0; repnd.

        rw @lsubst_lsubst_aux;
          [|simpl; allrw app_nil_r; rw @free_vars_lsubst_aux_cl; simpl; eauto 3 with slow;
            introv i j; rw in_remove_nvars in j; allsimpl; repnd; allrw not_over_or; repnd; GC;
            apply Xsss0 in j0; allsimpl; sp].

        rw @lsubst_lsubst_aux;
          [|simpl; allrw app_nil_r;
            introv i j; apply Xsss0 in j; allsimpl; repndors; subst; tcsp].

        rw <- (simple_lsubst_aux_lsubst_aux_sub_disj n0 [(v,n2)]);
          simpl; allrw app_nil_r; allrw memvar_singleton; boolvar; tcsp;
          allrw disjoint_singleton_l; tcsp; destruct isp as [c w]; try (rw c); tcsp.
        introv i j; apply Xsss0 in j; allsimpl; repndors; subst; tcsp.

      * left; exists (oterm Exc e1bt1lbt).
        introv isp.
        apply computes_in_1step_to_alpha.
        rw <- @compute_1_step_is_computes_in_1step.
        simpl; csunf; simpl.
        unfold compute_step_catch.
        destruct e1o; tcsp.

    + rw @compute_step_ncan_abs in Hcs.
      allrw @fold_lsubst_bterms_aux.
      remember (compute_step_lib
                  lib e1bt1oa
                  (lsubst_bterms_aux e1bt1lbt [(vx, oterm (NCan no) lbt)])) as clib.
      destruct clib; inversion Hcs; subst; GC.

      symmetry in Heqclib.
      apply compute_step_lib_success in Heqclib; exrepnd; subst.

      left.
      pose proof (change_bvars_alpha_eq_lib [vx] lib) as ch; exrepnd.
      eapply found_entry_alpha_eq_lib in Heqclib0; eauto; exrepnd.

      exists (oterm (NCan e1o) (bterm [] (mk_instance vars2 e1bt1lbt rhs2) :: e1lbt)).
      introv isp; simpl.
      eapply computes_in_1step_alpha_lib; eauto with slow.
      allrw @fold_lsubst_bterms_aux.
      allsimpl.
      allrw remove_nvars_nil_l; allrw subset_app; repnd.
      allrw disjoint_app_r; allrw disjoint_singleton_l; repnd.

      exists (oterm (NCan e1o)
                    (bterm [] (mk_instance vars2 (lsubst_bterms_aux e1bt1lbt [(vx, t')]) rhs2)
                       :: lsubst_bterms_aux e1lbt [(vx, t')])).
      dands.

      { apply c1step_nc.
        rw @compute_step_ncan_abs.
        dup Heqclib1 as fe.
        apply compute_step_lib_success_change_bs with (bs2 := lsubst_bterms_aux e1bt1lbt [(vx, t')])
          in Heqclib1;
          [ | unfold lsubst_bterms_aux; repeat (rw map_map); unfold compose, num_bvars;
              apply eq_maps; introv i; destruct x; simpl; complete auto ].
        rw Heqclib1; auto. }

      { repeat (prove_alpha_eq4).
        dup Heqclib1 as fe.
        apply found_entry_change_bs with (bs2 := e1bt1lbt) in fe; auto;
        [|unfold lsubst_bterms_aux; rw map_map; unfold compose;
          apply eq_maps; introv ib; destruct x; simpl;
          unfold num_bvars; simpl; complete auto].
        allunfold @correct_abs; repnd.
        apply alpha_eq_sym.
        apply alpha_eq_lsubst_aux_mk_instance; simpl; eauto with slow.
        apply found_entry_implies_matching_entry in fe.
        unfold matching_entry in fe; repnd; auto. }
  }

  { (* fresh case *)
    allsimpl.
    allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
    apply compute_step_ncan_bterm_cons_success in Hcs; repd; subst; allsimpl; GC.
    destruct e1lbt; allsimpl; ginv.
    allrw memvar_singleton; boolvar; tcsp;[].
    fold_terms.
    repndors; exrepnd; subst; GC;[|idtac|].

    - destruct e1bt1nt as [x|f|op bs]; allsimpl; boolvar; tcsp; ginv;[].
      left.
      fold_terms; ginv.
      exists (@mk_fresh p v (mk_var v)).
      introv isp.
      rw @lsubst_aux_trivial_cl2; simpl; eauto 3 with slow;[].
      apply computes_in_1step_to_alpha.
      constructor.
      csunf; simpl; boolvar; tcsp.

    - applydup @isvalue_like_lsubst_aux_implies in s0; repndors; exrepnd;
      [|subst; allsimpl; boolvar; tcsp; allapply @isvalue_like_ncan; complete sp].
      left; clear Hind.
      exists (pushdown_fresh v e1bt1nt).
      introv isp.
      pose proof (cl_lsubst_aux_pushdown_fresh e1bt1nt v [(vx,t')]) as aeq.
      repeat (autodimp aeq hyp); eauto 3 with slow.
      allsimpl; allrw memvar_singleton; boolvar; tcsp; [].

      applydup @isprogram_implies_nt_wf in He1p.
      allrw @nt_wf_fresh.
      apply lsubst_aux_nt_wf in He1p0.

      eapply computes_in_1step_alpha2;
        [| |apply alpha_eq_refl|apply alpha_eq_sym;exact aeq];
        [apply nt_wf_fresh;
          apply implies_wf_lsubst_aux; eauto 3 with slow
         |].

      apply computes_in_1step_to_alpha.
      constructor.
      fold_terms.
      rw @compute_step_fresh_if_isvalue_like; auto.
      apply isvalue_like_lsubst_aux; auto.

    - remember (get_fresh_atom (lsubst_aux e1bt1nt [(vx, oterm (NCan no) lbt)])) as a.
      unfsubst in s2.

      apply computation_mark.isnoncan_like_lsubst_aux in s1; repndors;[|].

      { exrepnd; subst; allsimpl; boolvar; tcsp;[]; GC.
        ginv; allsimpl; boolvar; tcsp;[]; GC.
        allrw @fold_lsubst_bterms_aux.
        allrw <- @lsubst_aux_oterm.
        rw @lsubst_aux_trivial_cl_term2 in s2; eauto 3 with slow.
        right.
        pose proof (ex_fresh_var
                      ([v,vy,v0]
                         ++ all_vars (oterm (NCan no) lbt))) as h;
          exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
        exists (@mk_fresh p v1 (mk_var vy)) x; dands; eauto 3 with slow.

        - rw @lsubst_lsubst_aux; allsimpl; allrw disjoint_singleton_l; allsimpl; tcsp.
          allrw memvar_singleton; boolvar; tcsp; allsimpl.
          boolvar; tcsp; fold_terms.
          pose proof (ex_fresh_var [v,v1,v0,vy]) as g; exrepnd; allsimpl; allrw not_over_or; repnd; GC.
          apply (implies_alpha_eq_mk_fresh_sub v2); allsimpl; allrw not_over_or; tcsp.
          unfold lsubst; simpl; boolvar; tcsp.

        - introv ispt'' isptd; dands; introv comp; allsimpl; allrw memvar_singleton;
          boolvar; tcsp; allsimpl; boolvar; tcsp; fold_terms.

          + inversion comp as [? ? ? ? comp1|? ? ? ? comp1]; subst.

            * pose proof (computation2.compute_step_fresh_if_isnoncan_like
                            lib v1 (oterm (NCan no0) lbt0)) as h.
              simpl in h; repeat (autodimp h hyp).
              rw @cl_subst_trivial in h; simpl; eauto with slow;
              [|destruct isptd as [c w];unfold closed in c; allsimpl; rw c; simpl; complete sp].
              rw comp1 in h; simpl in h.
              pose proof (get_fresh_atom_prop (oterm (NCan no0) lbt0)) as gfa.
              applydup @compute_step_preserves_utokens in comp1; eauto 3 with slow;[].
              assert (!LIn (get_fresh_atom (oterm (NCan no0) lbt0))
                       (get_utokens td')) as ni by (intro k; apply comp0 in k; sp).
              applydup @computes_in_1step_program in comp; auto.
              pose proof (subst_utokens_trivial1
                            td' [(get_fresh_atom (oterm (NCan no0) lbt0), mk_var v1)]) as q.
              allsimpl; allrw disjoint_singleton_r; repeat (autodimp q hyp); eauto 3 with slow.

              exists (mk_fresh
                        v1
                        (subst_utokens
                           td'
                           [(get_fresh_atom (oterm (NCan no0) lbt0), mk_var v1)])).
              dands; eauto 3 with slow;[|apply implies_alpha_eq_mk_fresh; complete (eauto 2 with slow)].
              constructor; fold_terms; auto.

            * pose proof (computation2.compute_step_fresh_if_isnoncan_like
                            lib v1 (oterm (Abs x0) lbt0)) as h.
              simpl in h; repeat (autodimp h hyp).
              rw @cl_subst_trivial in h; simpl; eauto with slow;
              [|destruct isptd as [c w];unfold closed in c; allsimpl; rw c; simpl; complete sp].
              rw comp1 in h; simpl in h.
              pose proof (get_fresh_atom_prop (oterm (Abs x0) lbt0)) as gfa.
              applydup @compute_step_preserves_utokens in comp1; eauto 3 with slow;[].
              assert (!LIn (get_fresh_atom (oterm (Abs x0) lbt0))
                       (get_utokens td')) as ni by (intro k; apply comp0 in k; sp).
              applydup @computes_in_1step_program in comp; auto.
              pose proof (subst_utokens_trivial1
                            td' [(get_fresh_atom (oterm (Abs x0) lbt0), mk_var v1)]) as q.
              allsimpl; allrw disjoint_singleton_r; repeat (autodimp q hyp); eauto 3 with slow.

              exists (mk_fresh
                        v1
                        (subst_utokens
                           td'
                           [(get_fresh_atom (oterm (Abs x0) lbt0), mk_var v1)])).
              dands; eauto 3 with slow;[|apply implies_alpha_eq_mk_fresh; complete (eauto 2 with slow)].
              constructor; fold_terms; auto.

          + allunfold @computes_step_to_error.
            remember (compute_step lib td) as c; symmetry in Heqc; destruct c; tcsp; GC.
            pose proof (nterm_trico_like td) as q; repndors.

            * apply isvariable_implies in q; exrepnd; subst.
              allrw @isprogram_vterm; tcsp.

            * rw @compute_step_value_like in Heqc; ginv; auto.

            * rw @computation2.compute_step_fresh_if_isnoncan_like; auto; simpl;[].
              rw @cl_subst_trivial; simpl; eauto with slow;
              [|destruct isptd as [c w];unfold closed in c; allsimpl; rw c; simpl; complete sp].
              rw Heqc; simpl; auto.
      }

      { pose proof (Hind e1bt1nt (lsubst_aux e1bt1nt [(v, mk_utoken a)]) [v]) as q; clear Hind; repeat (autodimp q hyp).
        { rw @simple_osize_lsubst_aux; eauto 4 with slow.
          introv i; allsimpl; repndors; tcsp; subst; simpl; auto. }
        pose proof (q x no lbt vx vy) as ih; clear q.
        allrw disjoint_singleton_l.
        repeat (autodimp ih hyp).
        { intro i; apply subset_bound_vars_lsubst_aux in i; allsimpl; allrw app_nil_r; sp. }
        { intro i; apply subset_bound_vars_lsubst_aux in i; allsimpl; allrw app_nil_r; sp. }
        { allrw @isprogram_fresh.
          applydup @cl_isprog_vars_lsubst_aux_implies in He1p; allsimpl; eauto 3 with slow.
          apply isprogram_lsubst_aux_if_isprog_vars; allsimpl; eauto 3 with slow.
          apply isprog_vars_lsubst_aux_if_isprog_vars; allsimpl; eauto 3 with slow.
          eapply isprog_vars_subvars;[|exact He1p0].
          rw subvars_prop; simpl; sp. }
        { apply computes_in_1step_if_isnoncan_like; eauto with slow.
          rw <- @simple_lsubst_aux_lsubst_aux_sub_disj in s2; allsimpl; auto;
          [|destruct Hpt as [c w]; unfold closed in c; allsimpl; rw c; simpl; complete auto].
          allrw memvar_singleton; boolvar; tcsp;[].
          allrw @fold_lsubst_bterms_aux.
          allrw <- @lsubst_aux_oterm.
          rw (lsubst_aux_trivial_cl_term2 (oterm (NCan no) lbt)) in s2; auto.
          destruct Hpt as [c w]; complete auto. }

        pose proof (get_fresh_atom_prop (lsubst_aux e1bt1nt [(vx, oterm (NCan no) lbt)])) as gfa.
        rw <- Heqa in gfa.

        assert (!LIn a (get_utokens e1bt1nt)) as nia1.
        { allrw @get_utokens_lsubst_aux; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; tcsp. }

        applydup @isprogram_implies_nt_wf in He1p.
        allrw @nt_wf_fresh.
        apply lsubst_aux_nt_wf in He1p0.

        repndors; exrepnd; fold_terms.

        - left.
          exists (mk_fresh v (subst_utokens e2' [(a, mk_var v)])).
          introv isp.
          allsimpl; allrw memvar_singleton; boolvar; tcsp; []; fold_terms.

          destruct (fresh_atom p (a :: get_utokens t'
                                    ++ get_utokens e1bt1nt
                                    ++ get_utokens e2')) as [a' fa]; allsimpl.
          allrw in_app_iff; allrw not_over_or; repnd.

          (* replace [a] by a fresh atom in [t'] first? *)
          pose proof (ih0 (ren_utokens [(a,a')] t')) as q.
          autodimp q hyp; eauto 2 with slow;[].
          unfold computes_in_1step_alpha in q; exrepnd.
          rw @cl_lsubst_aux_swap in q1; allsimpl; eauto 4 with slow;[].

          assert (!LIn a (get_utokens (lsubst_aux e1bt1nt [(vx, ren_utokens [(a, a')] t')]))) as nia2.
          { intro i.
            allrw @get_utokens_lsubst_aux; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
            boolvar; repndors; tcsp;[].
            allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl; allrw app_nil_r.
            allrw @get_utokens_ren_utokens; allsimpl.
            allrw in_map_iff; exrepnd.
            allunfold @ren_atom; allsimpl; boolvar; subst; tcsp. }

          apply computes_in_1step_alpha_fresh in q1; auto;
          [|apply implies_wf_lsubst_aux; eauto 4 with slow];[].
          pose proof (computes_in_1step_alpha_ren_utokens
                        lib
                        (mk_fresh v (lsubst_aux e1bt1nt [(vx, ren_utokens [(a, a')] t')]))
                        (mk_fresh v (subst_utokens t2a [(a, mk_var v)]))
                        [(a',a)]) as q'.
          allsimpl; allrw app_nil_r; allrw disjoint_singleton_l; allrw in_remove; fold_terms.
          repeat (autodimp q' hyp); tcsp.

          { apply nt_wf_fresh.
            apply implies_wf_lsubst_aux; eauto 4 with slow. }

          allrw @lsubst_aux_ren_utokens; allsimpl.
          rw (ren_utokens_trivial [(a', a)] e1bt1nt) in q';
            allsimpl; allrw disjoint_singleton_l; auto;[].

          pose proof (inv_ren_utokens t' [(a,a')]) as et'; allsimpl; allrw disjoint_singleton_l; allrw in_remove.
          repeat (autodimp et' hyp); tcsp; rw et' in q'.

          pose proof (alpha_eq_subst_utokens
                        (lsubst_aux e2' [(vx, ren_utokens [(a, a')] t')]) t2a
                        [(a, mk_var v)] [(a, mk_var v)]) as e.
          repeat (autodimp e hyp); tcsp; eauto 3 with slow;[].
          apply (alpha_eq_ren_utokens _ _ [(a', a)]) in e.
          apply (implies_alpha_eq_mk_fresh v) in e.
          eapply computes_in_1step_alpha2 in q';
            [| |apply alpha_eq_refl|apply alpha_eq_sym;exact e];
            [|apply nt_wf_fresh;
               apply implies_wf_lsubst_aux; eauto 4 with slow];[].

          pose proof (lsubst_aux_subst_utokens_disj_cl2
                        e2' [(vx, ren_utokens [(a, a')] t')]
                        [(a, mk_var v)]) as aeq.
          unfold get_utokens_sub in aeq; allsimpl; allrw app_nil_r.
          allrw disjoint_singleton_r; allsimpl.
          repeat (autodimp aeq hyp); eauto 4 with slow; tcsp.
          { intro k; rw @get_utokens_ren_utokens in k; allrw in_map_iff; exrepnd.
            allunfold @ren_atom; allsimpl; boolvar; tcsp. }
          apply (alpha_eq_ren_utokens _ _ [(a', a)]) in aeq.
          apply (implies_alpha_eq_mk_fresh v) in aeq.
          eapply computes_in_1step_alpha2 in q';
            [| |apply alpha_eq_refl|apply alpha_eq_sym;exact aeq];
            [|apply nt_wf_fresh;
               apply implies_wf_lsubst_aux; eauto 4 with slow];[].

          rw @lsubst_aux_ren_utokens in q'; allsimpl.
          rw et' in q'.
          rw @ren_utokens_trivial in q'; allsimpl; allrw disjoint_singleton_l;
          [|intro k; apply get_utokens_subst_utokens_subset in k; allsimpl;
            unfold get_utokens_utok_ren in k; allsimpl; allrw app_nil_r;
            allrw in_remove; tcsp].
          auto.

        - right.
          exists (mk_fresh v (subst_utokens e1' [(a, mk_var v)])) t'.
          dands; auto;[|].

          + apply (alpha_eq_subst_utokens _ _ [(a, mk_var v)] [(a, mk_var v)]) in ih0; eauto 3 with slow;[].

            pose proof (subst_utokens_lsubst_aux_trivial1 e1bt1nt v a) as aeq1.
            autodimp aeq1 hyp.
            eapply alpha_eq_trans in ih0;[clear aeq1|apply alpha_eq_sym; complete (exact aeq1)].
            apply (implies_alpha_eq_mk_fresh v) in ih0.
            eapply alpha_eq_trans;[exact ih0|clear ih0].

            pose proof (change_bvars_alpha_wspec [v,vx,vy] e1') as ch; exrepnd.
            rename ntcv into u.
            eapply alpha_eq_trans;
              [apply implies_alpha_eq_mk_fresh;
                apply alpha_eq_subst_utokens_same;
                apply lsubst_alpha_congr2; exact ch0|].
            eapply alpha_eq_trans;
              [|apply lsubst_alpha_congr2;
                 apply implies_alpha_eq_mk_fresh;
                 apply alpha_eq_subst_utokens_same;
                 apply alpha_eq_sym; exact ch0].

            allrw disjoint_cons_l; repnd.
            rw @lsubst_lsubst_aux; allsimpl; allrw disjoint_singleton_r; tcsp;[].
            rw @subst_utokens_subst_utokens_aux; simpl; allrw disjoint_singleton_r;
            [|intro i; apply subset_bound_vars_lsubst_aux in i; allsimpl; allrw app_nil_r;
              complete tcsp].
            rw @subst_utokens_subst_utokens_aux; simpl; allrw disjoint_singleton_r; auto;[].
            rw @lsubst_lsubst_aux; allsimpl; allrw memvar_singleton; boolvar; tcsp;
            allrw app_nil_r; allrw disjoint_singleton_r; simpl; try (rw not_over_or);
            dands; tcsp;
            [|intro i; apply bound_vars_subst_utokens_aux_subset in i; allsimpl;
              allrw app_nil_r; complete tcsp]; fold_terms.

            apply implies_alpha_eq_mk_fresh.
            rw @lsubst_aux_subst_utokens_aux_disj; simpl;
            allrw disjoint_singleton_r; allsimpl; tcsp.

          + introv ispt'' isptd; allsimpl; allrw memvar_singleton; boolvar; tcsp;[]; fold_terms.

            destruct (fresh_atom p (a :: get_utokens t''
                                      ++ get_utokens td
                                      ++ get_utokens e1'
                                      ++ get_utokens e1bt1nt)) as [a' fa]; allsimpl.
            allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (ih1 (ren_utokens [(a,a')] t'')
                            (ren_utokens [(a,a')] td)
                            (ren_utokens [(a,a')] td')) as q.
            repeat (autodimp q hyp); eauto 2 with slow;[].
            repnd.

            assert (wf_term e1bt1nt) as wfe1bt1nt.
            { apply isprogram_implies_wf in He1p.
              allrw @wf_fresh_iff.
              rw @wf_term_eq in He1p.
              rw @nt_wf_lsubst_aux_iff in He1p.
              rw @nt_wf_eq in He1p; sp. }

            assert (wf_term e1') as wfe1'.
            { apply alphaeq_preserves_wf_term in ih0.
              { rw @wf_term_eq in ih0.
                rw @nt_wf_lsubst_iff in ih0.
                rw @nt_wf_eq in ih0; sp. }
              apply lsubst_aux_preserves_wf_term2; eauto 3 with slow. }

            assert (!LIn v (free_vars e1')) as nive1'.
            { intro i.
              apply alphaeq_preserves_free_vars in ih0.
              rw @free_vars_lsubst_aux_cl in ih0; allsimpl; eauto 3 with slow.
              assert (LIn v (free_vars (lsubst e1' [(vy, mk_var vx)]))) as j.
              { pose proof (eqvars_free_vars_disjoint e1' [(vy,mk_var vx)]) as e.
                rw eqvars_prop in e; apply e; clear e; simpl; boolvar; simpl;
                allrw app_nil_r; allrw in_app_iff; allrw in_remove_nvars; allsimpl; tcsp.
                left; tcsp. }
              rw <- ih0 in j; allrw in_remove_nvars; allsimpl; tcsp. }

            pose proof (pull_out_nrut_sub e1' [(v,mk_utoken a)] []) as aeq; allsimpl.
            repeat (autodimp aeq hyp); eauto 3 with slow;
            [apply nrut_sub_cons; simpl; eexists; dands; eauto with slow; tcsp
            |apply disjoint_singleton_r; auto
            |];[].
            exrepnd.
            allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r; allsimpl.
            allrw disjoint_singleton_l; allrw disjoint_singleton_r.

            assert (!LIn a
                     (get_utokens
                        (lsubst_aux u [(vx, ren_utokens [(a, a')] t''),
                                       (vy, ren_utokens [(a, a')] td)]))) as nia.
            { intro i; apply get_utokens_lsubst_aux in i; allrw in_app_iff.
              repndors; tcsp;[].
              allsimpl; boolvar; allrw in_remove_nvars; allsimpl; allrw not_over_or; repnd; tcsp;
              allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r;
              allrw in_app_iff; repndors; GC;
              allrw @get_utokens_ren_utokens; allrw in_map_iff; allunfold @ren_atom; allsimpl; exrepnd;
              boolvar; subst; tcsp. }

            dup aeq1 as aeq'.
            apply (alpha_eq_subst_utokens_same _ _ [(a,mk_var v)]) in aeq'.
            unflsubst in aeq'.
            apply alpha_eq_sym in aeq'; eapply alpha_eq_trans in aeq';
            [|apply alpha_eq_sym; apply subst_utokens_lsubst_aux_trivial1; auto];[].

            assert (!LIn a' (get_utokens u)) as nia'u.
            { intro i; apply alphaeq_preserves_utokens in aeq'; rw aeq' in i.
              apply get_utokens_subst_utokens_subset in i; allsimpl.
              unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
              rw in_remove in i; tcsp. }

            assert (isprog_vars [v,vx] e1bt1nt) as isp1.
            { apply isprogram_fresh in He1p;
              apply cl_isprog_vars_lsubst_aux_implies in He1p; eauto 3 with slow; allsimpl. }

            assert (isprog_vars [vx,vy] e1') as isp2.
            { apply (alphaeq_preserves_isprog_vars _ _ [vx]) in ih0;
              [|apply isprog_vars_lsubst_aux_if_isprog_vars; simpl;[|complete (eauto with slow)];
                eapply isprog_vars_subvars;[|exact isp1];
                rw subvars_prop; simpl; complete sp].
              apply isprog_vars_lsubst_implies in ih0; allsimpl; auto. }

            assert (isprog_vars [v,vx,vy] u) as isp3.
            { eapply alphaeq_preserves_isprog_vars;[apply alpha_eq_sym; exact aeq'|].
              apply implies_isprog_vars_subst_utokens;[complete (eauto 3 with slow)|].
              eapply isprog_vars_subvars;[|exact isp2].
              rw subvars_prop; simpl; complete sp. }

            dands; introv comp;[clear q|clear q0].

            * autodimp q0 hyp; eauto 3 with slow.
              { apply computes_in_1step_ren_utokens; simpl; eauto 3 with slow;[].
                apply disjoint_singleton_l; rw in_remove; tcsp. }
              applydup @computes_in_1step_program in comp; auto;[].

              eapply computes_in_1step_alpha2 in q0;
                try (complete (apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                               [|apply cl_sub_cons; dands; eauto 4 with slow];
                               exact aeq1));
                [|apply implies_wf_lsubst_aux; eauto 2 with slow;
                  repeat (apply wf_sub_cons); eauto 2 with slow;
                  apply wf_term_ren_utokens; eauto 3 with slow];[].

              repeat (unflsubst in q0).
              rw @cl_lsubst_aux_swap in q0; allsimpl; allrw disjoint_singleton_l; allsimpl;
              eauto 3 with slow; tcsp; try (complete (apply cl_sub_cons; dands; eauto 4 with slow));[].

              apply computes_in_1step_alpha_fresh2 in q0; auto;
              try (complete (try (apply nt_wf_fresh);
                             apply implies_wf_lsubst_aux; eauto 2 with slow;
                             repeat (apply wf_sub_cons); eauto 2 with slow;
                             apply wf_term_ren_utokens; eauto 3 with slow)).

              apply (computes_in_1step_alpha_ren_utokens _ _ _ [(a',a)]) in q0; allsimpl; tcsp;
              try (complete (try (apply nt_wf_fresh);
                             apply implies_wf_lsubst_aux; eauto 2 with slow;
                             repeat (apply wf_sub_cons); eauto 2 with slow;
                             apply wf_term_ren_utokens; eauto 3 with slow));
              [|apply disjoint_singleton_l; rw app_nil_r; rw in_remove; complete sp]; fold_terms.
              rw @lsubst_aux_ren_utokens in q0; allsimpl.
              rw (ren_utokens_trivial [(a', a)] u) in q0; allsimpl; allrw disjoint_singleton_l; auto;[].

              pose proof (inv_ren_utokens t'' [(a,a')]) as et''; allsimpl; allrw disjoint_singleton_l; allrw in_remove.
              repeat (autodimp et'' hyp); tcsp; rw et'' in q0.

              pose proof (inv_ren_utokens td [(a,a')]) as etd; allsimpl; allrw disjoint_singleton_l; allrw in_remove.
              repeat (autodimp etd hyp); tcsp; rw etd in q0.

              pose proof (inv_ren_utokens td' [(a,a')]) as etd'; allsimpl; allrw disjoint_singleton_l; allrw in_remove.
              repeat (autodimp etd' hyp); tcsp.
              { apply computes_in_1step_preserves_get_utokens in comp; eauto 3 with slow.
                intro i; repnd; apply comp in i; sp. }

              eapply computes_in_1step_alpha2;[|exact q0|idtac|];
              try (complete (try (apply nt_wf_fresh);
                             apply implies_wf_lsubst_aux; eauto 2 with slow;
                             repeat (apply wf_sub_cons); eauto 3 with slow)).
              { apply implies_alpha_eq_mk_fresh.
                apply lsubst_aux_alpha_congr_same_cl_sub; auto.
                apply cl_sub_cons; dands; eauto 4 with slow. }

              apply implies_alpha_eq_mk_fresh.

              pose proof (lsubst_aux_subst_utokens_disj_cl2
                            (lsubst_aux u [(v, mk_utoken a)])
                            [(vx, ren_utokens [(a, a')] t''),
                             (vy, ren_utokens [(a, a')] td')]
                            [(a, mk_var v)]) as aeq; allsimpl.
              unfold get_utokens_sub in aeq; allsimpl; allrw app_nil_r.
              allrw disjoint_singleton_l; allrw disjoint_singleton_r; allsimpl.
              allrw in_app_iff; allrw not_over_or.
              repeat (autodimp aeq hyp); dands; tcsp;
              try (complete (intro i; allrw @get_utokens_ren_utokens; allrw in_map_iff;
                             allunfold @ren_atom; allsimpl; exrepnd; boolvar; tcsp));
              try (complete (apply cl_sub_cons; dands; eauto 4 with slow));[].

              eapply alpha_eq_trans;
                [apply alpha_eq_ren_utokens;apply alpha_eq_sym;exact aeq|clear aeq].
              rw @lsubst_aux_ren_utokens; simpl.
              rw et'';rw etd'.

              apply lsubst_aux_alpha_congr_same_cl_sub; [| eauto 4 with slow];[].

              eapply alpha_eq_trans;
                [apply alpha_eq_ren_utokens; apply subst_utokens_lsubst_aux_trivial1;complete auto|].

              eapply alpha_eq_trans;[|exact aeq'].
              rw @ren_utokens_trivial; simpl; auto.
              apply disjoint_singleton_l; auto.


            * autodimp q hyp.
              { apply computes_step_to_error_ren_utokens; allsimpl; auto.
                apply disjoint_singleton_l; rw in_remove; tcsp. }
              { remember (compute_step
                            lib
                            (mk_fresh v (lsubst_aux (subst_utokens e1' [(a, mk_var v)]) [(vx, t''), (vy, td)]))) as c.
                symmetry in Heqc; destruct c; tcsp;
                [|unfold computes_step_to_error; rw Heqc; complete auto].
                provefalse.

                apply compute_step_ncan_bterm_cons_success in Heqc; repnd; allsimpl; GC.
                clear Heqa.
                repndors; exrepnd; subst n.

                - apply lsubst_aux_eq_vterm_implies in Heqc0; repndors.

                  + exrepnd.
                    apply subst_utokens_eq_vterm_implies in Heqc1; repndors;
                    exrepnd; subst; allsimpl; boolvar; ginv; tcsp; GC; allsimpl;
                    allrw @isprogram_vterm; ginv; tcsp.

                  + apply subst_utokens_eq_vterm_implies in Heqc0; repndors;
                    exrepnd; subst; allsimpl; boolvar; ginv; tcsp; GC; allsimpl;
                    allrw @isprogram_vterm; ginv; tcsp.

                - apply isvalue_like_lsubst_aux_implies in Heqc0; repndors;[|].

                  + apply isvalue_like_subst_utokens in Heqc0.
                    repndors;[|].

                    * exrepnd; subst e1'.
                      allrw @wf_term_utok; subst bs; allsimpl; GC.
                      unfold computes_step_to_error in q.
                      csunf q; allsimpl; tcsp.

                    * repnd.
                      apply computes_step_to_error_if_isvalue_like in q; tcsp.
                      apply isvalue_like_lsubst_aux; auto.

                  + exrepnd.
                    apply subst_utokens_eq_vterm_implies in Heqc2;[].
                    repndors; exrepnd; subst; allsimpl.

                    * apply computes_step_to_error_if_isvalue_like in q; tcsp.

                    * allrw not_over_or; repnd; GC; boolvar; tcsp; allsimpl; ginv; [|].

                      { unfold lsubst in ih0; allsimpl; boolvar; tcsp;[].
                        inversion ih0 as [? e| |]; subst;[].
                        symmetry in e.
                        apply lsubst_aux_eq_vterm_implies in e; repndors; exrepnd; subst; allsimpl;
                        boolvar; tcsp; ginv; GC;[].
                        unfold isnoncan_like in s1; allsimpl; repndors; tcsp. }

                      { unfold lsubst in ih0; allsimpl; boolvar; tcsp;[].
                        inversion ih0 as [? e| |]; subst;[].
                        symmetry in e.
                        apply lsubst_aux_eq_vterm_implies in e; repndors; exrepnd; subst; allsimpl;
                        boolvar; tcsp; ginv; GC;[].
                        unfold isnoncan_like in s1; allsimpl; repndors; tcsp. }

                - remember (get_fresh_atom
                              (lsubst_aux (subst_utokens e1' [(a, mk_var v)])
                                          [(vx, t''), (vy, td)])) as a''.
                  pose proof (get_fresh_atom_prop
                                (lsubst_aux (subst_utokens e1' [(a, mk_var v)])
                                            [(vx, t''), (vy, td)])) as gfap.
                  rw <- Heqa'' in gfap; clear Heqa''.

                  assert (!LIn a'
                           (get_utokens
                              (lsubst_aux (subst_utokens e1' [(a, mk_var v)])
                                          [(vx, t''), (vy, td)]))) as niagu'.
                  { intro i.
                    apply get_utokens_lsubst_aux in i; allsimpl.
                    allrw in_app_iff; repndors.
                    - apply get_utokens_subst_utokens_subset in i; allsimpl.
                      unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
                      allrw in_remove; repnd; tcsp.
                    - boolvar; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil;
                      allrw app_nil_r; allrw in_app_iff; repndors; tcsp. }

                  pose proof (compute_step_subst_utoken
                                lib
                                (lsubst_aux (subst_utokens e1' [(a, mk_var v)]) [(vx, t''), (vy, td)])
                                x0
                                [(v,mk_utoken a'')]) as comp2.
                  allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl; allrw app_nil_r.
                  allrw disjoint_singleton_l.
                  repeat (autodimp comp2 hyp);[|].
                  { apply implies_wf_lsubst_aux; eauto 2 with slow;
                    repeat (apply wf_sub_cons); eauto 3 with slow. }
                  exrepnd.
                  clear comp1 comp2 comp3 comp4.
                  pose proof (comp0 [(v,mk_utoken a')]) as comp'; clear comp0; allsimpl.
                  allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl; allrw app_nil_r.
                  allrw disjoint_singleton_l.
                  repeat (autodimp comp' hyp);[].
                  exrepnd.
                  clear comp'0.
                  rename Heqc2 into comp'.
                  rename comp'1 into Heqc2.

                  apply implies_computes_step_to_success in Heqc2.

                  rw @cl_lsubst_lsubst_aux in Heqc2; eauto 3 with slow;[].

                  rw @cl_lsubst_aux_swap in Heqc2; allsimpl; allrw disjoint_singleton_r;
                  allsimpl; tcsp; eauto 3 with slow;
                  try (complete (apply cl_sub_cons; dands; eauto 4 with slow));[].

                  eapply computes_step_to_success_alpha_eq in Heqc2;
                    [| |apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                       try (complete (apply cl_sub_cons; dands; complete (eauto 4 with slow)));
                       apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                       try (complete (apply cl_sub_cons; dands; complete (eauto 4 with slow)));
                       apply alpha_eq_subst_utokens_same; exact aeq1];
                    [|repeat (apply implies_wf_lsubst_aux; eauto 3 with slow);
                       repeat (apply wf_sub_cons); eauto 3 with slow];[].

                  rw @cl_lsubst_lsubst_aux in Heqc2;[|eauto 3 with slow].

                  eapply computes_step_to_success_alpha_eq in Heqc2;
                    [| |apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                       try (complete (apply cl_sub_cons; dands; complete (eauto 4 with slow)));
                       apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                       try (complete (apply cl_sub_cons; dands; complete (eauto 4 with slow)));
                       apply subst_utokens_lsubst_aux_trivial1; auto];
                    [|repeat (apply implies_wf_lsubst_aux; eauto 2 with slow);
                       try (apply nt_wf_eq); try (apply wf_subst_utokens);
                       try (apply lsubst_aux_preserves_wf_term2);
                       repeat (apply wf_sub_cons); eauto 3 with slow];[].

                  eapply computes_step_to_error_alpha_eq in q;
                    [| |apply computation2.lsubst_aux_alpha_congr_same_cl_sub;
                       try (complete (apply cl_sub_cons; dands; complete (eauto 4 with slow)));
                       exact aeq1];
                    [|repeat (apply implies_wf_lsubst_aux; eauto 2 with slow);
                       repeat (apply wf_sub_cons); eauto 3 with slow;
                       apply wf_term_ren_utokens; eauto 3 with slow].

                  rw @cl_lsubst_lsubst_aux in q;[|eauto 3 with slow].

                  (* let's rename the atoms now to make Heqc2 and q be the same *)
                  destruct (fresh_atom p (a :: a'
                                            :: a''
                                            :: get_utokens t''
                                            ++ get_utokens td
                                            ++ get_utokens e1'
                                            ++ get_utokens u
                                            ++ get_utokens e1bt1nt)) as [a''' faa]; allsimpl.
                  allrw in_app_iff; allrw not_over_or; repnd.

                  assert (!LIn a'''
                           (get_utokens
                              (lsubst_aux (lsubst_aux u [(v, mk_utoken a)])
                                          [(vx, ren_utokens [(a, a')] t''),
                                           (vy, ren_utokens [(a, a')] td)]))) as nia2.
                  { intro i.
                    apply get_utokens_lsubst_aux in i; allsimpl.
                    allrw in_app_iff; repndors.
                    - apply get_utokens_lsubst_aux in i; allsimpl.
                      allrw in_app_iff; repndors; tcsp.
                      boolvar; allunfold @get_utokens_sub; allsimpl; tcsp.
                    - boolvar; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil;
                      allrw app_nil_r; allrw in_app_iff; repndors; tcsp;
                      allrw @get_utokens_ren_utokens; allrw in_map_iff;
                      exrepnd; allunfold @ren_atom; allsimpl; boolvar; subst; tcsp. }

                  apply (computes_step_to_error_ren_utokens _ _ [(a',a''')]) in q;
                    allsimpl; tcsp;
                    [|apply isprogram_lsubst_aux_if_isprog_vars; simpl;[|complete (eauto with slow)];
                      apply isprog_vars_lsubst_aux_if_isprog_vars; simpl;[|complete (eauto with slow)];
                      eapply isprog_vars_subvars;[|exact isp3];
                      rw subvars_prop; simpl; complete sp
                     |rw disjoint_singleton_l; rw in_remove; complete sp].

                  repeat (rw @lsubst_aux_ren_utokens in q; allsimpl).
                  unfold ren_atom in q; allsimpl; boolvar; tcsp;[]; fold_terms.
                  rw (ren_utokens_trivial [(a', a''')] u) in q; allsimpl;[|apply disjoint_singleton_l; complete auto].
                  repeat (rw @ren_utokens_ren_utokens in q); allsimpl.
                  unfold ren_atom in q; allsimpl; boolvar; tcsp; GC;[].

                  pose proof (ren_utokens_app_weak_l t'' [(a, a''')] [(a', a''')]) as e1; allsimpl.
                  rw disjoint_singleton_l in e1; autodimp e1 hyp;[].
                  rw e1 in q; clear e1.

                  pose proof (ren_utokens_app_weak_l td [(a, a''')] [(a', a''')]) as e1; allsimpl.
                  rw disjoint_singleton_l in e1; autodimp e1 hyp;[].
                  rw e1 in q; clear e1.

                  assert (!LIn a'
                           (get_utokens
                              (lsubst_aux (lsubst_aux u [(v, mk_utoken a)])
                                          [(vx, ren_utokens [(a, a''')] t''),
                                           (vy, ren_utokens [(a, a''')] td)]))) as nia3.
                  { intro i.
                    apply get_utokens_lsubst_aux in i; allsimpl.
                    allrw in_app_iff; repndors.
                    - apply get_utokens_lsubst_aux in i; allsimpl.
                      allrw in_app_iff; repndors; tcsp.
                      boolvar; allunfold @get_utokens_sub; allsimpl; tcsp.
                    - boolvar; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil;
                      allrw app_nil_r; allrw in_app_iff; repndors; tcsp;
                      allrw @get_utokens_ren_utokens; allrw in_map_iff;
                      exrepnd; allunfold @ren_atom; allsimpl; boolvar; subst; tcsp. }

                  apply (computes_step_to_error_ren_utokens _ _ [(a,a')]) in q;
                    allsimpl; tcsp;
                    [|apply isprogram_lsubst_aux_if_isprog_vars; simpl;[|complete (eauto with slow)];
                      apply isprog_vars_lsubst_aux_if_isprog_vars; simpl;[|complete (eauto with slow)];
                      eapply isprog_vars_subvars;[|exact isp3];
                      rw subvars_prop; simpl; complete sp
                     |rw disjoint_singleton_l; rw in_remove; complete sp].

                  repeat (rw @lsubst_aux_ren_utokens in q; allsimpl).
                  unfold ren_atom in q; allsimpl; boolvar; tcsp; GC;[]; fold_terms.
                  rw (ren_utokens_trivial [(a, a')] u) in q; allsimpl;[|apply disjoint_singleton_l; complete auto].
                  repeat (rw (ren_utokens_trivial [(a,a')]) in q; allsimpl;
                          [|apply disjoint_singleton_l; introv i;
                            rw @get_utokens_ren_utokens in i; rw in_map_iff in i; exrepnd;
                            unfold ren_atom in i0; allsimpl; boolvar; complete sp]).

                  assert (!LIn a'''
                           (get_utokens
                              (lsubst_aux (lsubst_aux u [(v, mk_utoken a')]) [(vx, t''), (vy, td)]))) as nia4.
                  { intro i.
                    apply get_utokens_lsubst_aux in i; allsimpl.
                    allrw in_app_iff; repndors.
                    - apply get_utokens_lsubst_aux in i; allsimpl.
                      allrw in_app_iff; repndors; tcsp.
                      boolvar; allunfold @get_utokens_sub; allsimpl; tcsp.
                    - boolvar; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil;
                      allrw app_nil_r; allrw in_app_iff; repndors; tcsp;
                      allrw @get_utokens_ren_utokens; allrw in_map_iff;
                      exrepnd; allunfold @ren_atom; allsimpl; boolvar; subst; tcsp. }

                  apply (computes_step_to_success_ren_utokens _ _ [(a,a''')]) in Heqc2;
                    allsimpl; tcsp; [| |rw disjoint_singleton_l; rw in_remove; complete sp];
                    [|repeat (apply implies_wf_lsubst_aux; eauto 2 with slow);
                       repeat (apply wf_sub_cons); eauto 3 with slow;
                       apply wf_term_ren_utokens; eauto 3 with slow].

                  repeat (rw @lsubst_aux_ren_utokens in Heqc2; allsimpl).
                  unfold ren_atom in Heqc2; allsimpl; boolvar; tcsp; GC;[]; fold_terms.
                  rw (ren_utokens_trivial [(a,a''')] u) in Heqc2; allsimpl;[|apply disjoint_singleton_l; complete auto].

                  apply computes_step_to_error_and_success in Heqc2; tcsp.
              }

      }
  } }

  { (* Abs case *)
    inversion Hcs as [|? ? ? ? comp]; subst; clear Hcs.
    csunf comp; allsimpl.
    allapply @compute_step_lib_success; exrepnd; subst.

    left.
    pose proof (change_bvars_alpha_eq_lib [vx] lib) as ch; exrepnd.
    match goal with
      | [ H : found_entry ?lib ?abs ?bs ?oa2 ?vars ?rhs ?correct |- _ ] =>
        assert (found_entry lib abs bs oa2 vars rhs correct) as fen by trivial
    end.
    eapply found_entry_alpha_eq_lib in fen; eauto; exrepnd.

    exists (mk_instance vars2 lbt1 rhs2).

    introv isp; simpl.
    eapply computes_in_1step_alpha_lib; eauto with slow.

    exists (mk_instance vars2 (map (fun t => lsubst_bterm_aux t [(vx, t')]) lbt1) rhs2).
    dands.

    { apply c1step_ab.
      csunf; simpl.
      dup fen0 as fe.
      apply compute_step_lib_success_change_bs with (bs2 := map (fun t : BTerm => lsubst_bterm_aux t [(vx, t')]) lbt1)
        in fen0;
        [ | repeat (rw map_map); unfold compose, num_bvars;
            apply eq_maps; introv i; destruct x; simpl; auto ].
      rw fen0; auto. }

    { dup fen0 as fe.
      apply found_entry_change_bs with (bs2 := lbt1) in fe; auto;
      [|rw map_map; unfold compose;
        apply eq_maps; introv ib; destruct x; simpl;
        unfold num_bvars; simpl; auto].
      allunfold @correct_abs; repnd.
      apply alpha_eq_sym.
      allrw @fold_lsubst_bterms_aux.
      apply alpha_eq_lsubst_aux_mk_instance; simpl; eauto with slow.
      apply found_entry_implies_matching_entry in fe.
      unfold matching_entry in fe; repnd; auto.
 } }
Qed.




Ltac alpharw2 H := let X99:= fresh "Xalrw" in
let lhs := get_alpha_lhs H in
match goal with
| [ |- alpha_eq (lsubst (lsubst lhs ?sub1) ?sub2) ?rhs] =>
    pose proof  (lsubst_alpha_congr2 _ _ sub2 (lsubst_alpha_congr2 _ _ sub1 H)) as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- alpha_eq (lsubst lhs ?sub) ?rhs] => pose proof  (lsubst_alpha_congr2 _ _ sub H) as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- alpha_eq lhs ?rhs ] => pose proof H as X99;
    apply alpha_eq_trans with (nt3:=rhs)  in X99;[exact X99;fail|clear X99]
| [ |- context [ free_vars lhs ] ] => 
    pose proof (alphaeq_preserves_free_vars _ _ H) as X99;
    rewrite X99; clear X99
| [ |- context [ free_vars (lsubst lhs ?sub) ] ] => 
    pose proof (alphaeq_preserves_free_vars _ _ ((lsubst_alpha_congr2 _ _ sub H))) as X99;
    rewrite X99; clear X99
| [ |- context[isprogram lhs] ] => 
  rw (alphaeq_preserves_program _ _ H)
| [ |- context [ isprogram (lsubst lhs ?sub) ] ] => 
    trw (alphaeq_preserves_program _ _ ((lsubst_alpha_congr2 _ _ sub H))) 
end.


(* remove the disjointness condition and replace subst_aux by subst.
  In the first case, it seems we need to weaken computes_in_1step
  to computes_in_1step_alpha *)

(* end hide *)

(** %\noindent% The following lemma is an (at least apparently) stronger version
    of Crary's lemma 5.7. Although its statement might seem overly complicated.
    it is expressing a very intuitive property of our(and Crary's)
    computation system that closed,
    noncanonical terms that lie within a term being evaluated are
    not destructed.  They either are
    moved or copied around unchanged (the first case in the disjunction in the
    lemma's conclusion) or are
    evaluated in place with the surrounding
    term left unchanged (the second case).

    More concretely, in the first case, the behaviour remains unchanged
    even when we replace that closed noncanonical subterm with
    some other term. The second case might look like a complicated
    way to express the property above. Intuitively, it says that
    some of the occurences of that non-canonical term get evaluated
    in place. These occurences are denoted by [y]. It turns out
    from the proof that exactly 1 of the occurences gets evaluated in
    a step. Crary's original statement can be derived as a corollary
    (see [crary5_7_original] below). Our strengthening only affects
    the second case where we additionally require that
    if that closed non-canonical subterm is replaced by
    any other closed non-canonical subterm, the behaviour
    will remain unchanged. It is not immediately clear
    if this strenghening puts additional restrictions on
    the kind of computation systems for this this property holds.
    The first case in Crary's(and our) statement
    already forces the computation system to behave in the same way
    if the noncanonical subterm is replaced by some other subterm.
*)

Lemma crary5_7 {o} : forall lib vx vy e1 e2 no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e1 vx t in
vx <> vy
-> isprogram t
-> isprogram tl
-> computes_in_1step lib tl e2
-> {e2' : NTerm $ forall t', isprogram t'
              -> computes_in_1step_alpha lib (subst e1 vx t')
                                         (subst e2' vx t')}
                              [+]
   {e1',t' : NTerm $ alpha_eq e1 (subst e1' vy (vterm vx)) (* except here, we are always subbing closed terms*)
        # computes_in_1step lib t t'
        # forall t'' td td',
              isprogram t''
              -> isprogram td
              -> (computes_in_1step lib td td'
                      -> computes_in_1step_alpha lib (lsubst e1' [(vx,t''),(vy,td)])
                                        (lsubst e1' [(vx,t''),(vy,td')]))
                 # (computes_step_to_error lib td
                        -> computes_step_to_error lib
                            (lsubst e1' [(vx,t''),(vy,td)]))}.
Proof.
  introv Hneq. introns HH.
  pose proof (change_bvars_alpha_wspec [vx,vy] e1) as Hfr; exrepnd.
  allunfold @subst.
  allrw disjoint_cons_l; repnd.
  revert HH0. alpharw2 Hfr0. rename ntcv into e1a.
  introv HH0. duplicate Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx, oterm (NCan no) lbt)]) in Hfr0.
  eapply compute_1step_alpha in Hfr0; eauto; exrepnd.
  assert (alpha_eq e2 t2') as aeq by eauto with slow.
  rename t2' into e2a.
  clear HH1.
  rewrite lsubst_lsubst_aux_prog_sub in Hfr0; [| prove_sub_range_sat;fail].
  rewrite lsubst_lsubst_aux_prog_sub in HH0; [| prove_sub_range_sat;fail].
  apply @crary5_7_aux_stronger with (vy:=vy) in Hfr0; auto;[].
  dorn Hfr0;[left|right]; exrepnd.

  - exists e2'.
    introv Hp.
    applydup_clear Hfr6 in Hp.
    unfold subst_aux in Hp0.
    rewrite <- lsubst_lsubst_aux_prog_sub in Hp0; [| prove_sub_range_sat;fail].
    rewrite <- lsubst_lsubst_aux_prog_sub in Hp0; [| prove_sub_range_sat;fail].
    apply lsubst_alpha_congr2 with (sub:= [(vx, t')]) in Hfr4.
    apply alpha_eq_sym in Hfr4.
    pose proof (change_bvars_alpha_eq_lib [vx] lib) as aeqlib; exrepnd.
    eapply computes_in_1step_alpha_lib in Hp0; eauto.
    eapply computes_in_1step_alpha_lib; eauto with slow.
    eapply computes_in_1step_alpha2;[|eauto| |]; eauto 2 with slow.

    apply isprogram_implies_nt_wf in HH0.
    apply lsubst_aux_nt_wf in HH0.
    apply lsubst_wf_if_eauto; eauto 3 with slow.

  - exists e1' t'.
    dands; eauto 2 with slow.
    introv Hp Hptd;dands; introv  Hcsd;
     duplicate Hcsd as Hcsdb; apply Hfr0 with (t'':=t'') in Hcsd; auto;
    invertsn Hfr7; apply preserve_compute_step in Hfr7; auto;[|];
    rewrite lsubst_lsubst_aux_prog_sub; try( prove_sub_range_sat;fail);auto.
    rewrite lsubst_lsubst_aux_prog_sub; [| prove_sub_range_sat]; eauto 2 with slow.

  - apply isprogram_implies_nt_wf in HH0.
    apply lsubst_nt_wf in HH0.
    apply alpha_eq_respects_nt_wf_inv in Hfr4; auto.
    apply lsubst_wf_if_eauto; eauto 3 with slow.
Qed.

Corollary crary5_7_original {o} : forall lib e1 e2 no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e1 nvarx t in
isprogram t
-> isprogram tl
-> computes_in_1step lib tl e2
-> {e2' : NTerm $ forall t', isprogram t'
        -> computes_in_1step_alpha lib (subst e1 nvarx t')
                                   (subst e2' nvarx t')}
                              [+]
   {e1',t' : NTerm $ alpha_eq e1 (subst e1' nvary (vterm nvarx))
        # computes_in_1step lib t t'
        # forall t'', isprogram t''
           -> computes_in_1step_alpha lib (lsubst e1' [(nvarx,t''),(nvary,t)])
                                (lsubst e1' [(nvarx,t''),(nvary,t')])}.
Proof.
  introns XX.
  apply crary5_7 with (vy:=nvary) in XX1; eauto;[|unfold nvarx,nvary;intro H; inverts H].
  dorn XX1;[left | right]; auto;[]; exrepnd; eexists; eexists; dands; spc; eauto.
  apply XX1; auto.
Qed.


(* begin hide *)

Lemma crary5_7_alpha {o} : forall lib vx vy e1 e2 no lbt,
  let t := @oterm o (NCan no) lbt in
  let tl := subst e1 vx t in
  vx <> vy
  -> isprogram t
  -> isprogram tl
  -> computes_in_1step_alpha lib tl e2
  -> {e2' : NTerm
       $ forall t',
           isprogram t'
           -> computes_in_1step_alpha lib
                (subst e1 vx t')
                (subst e2' vx t')}
     [+]
     {e1' , t' : NTerm
       $ alpha_eq e1 (subst e1' vy (vterm vx)) (* except here, we are always subbing closed terms*)
       # computes_in_1step lib t t'
       # forall t'' td td',
           isprogram t''
           -> isprogram td
           -> (computes_in_1step lib td td'
               -> computes_in_1step_alpha lib (lsubst e1' [(vx,t''),(vy,td)])
                                    (lsubst e1' [(vx,t''),(vy,td')]))
              # (computes_step_to_error lib td
                 -> computes_step_to_error lib (lsubst e1' [(vx,t''),(vy,td)]))}.
Proof.
  introns XX.
  repnud XX2.
  exrepnd.
  apply @crary5_7 with (vy:=vy) in XX2; auto.
Qed.

(* use it in 5_9 *)
Lemma prog_sub_reduce_to {p} : forall lib sub f,
  @isprogram p f
  -> sub_range_sat sub (fun t : NTerm => reduces_to lib f t)
  -> prog_sub (map_sub_range mk_fix sub).
Proof.
  unfold map_sub_range; introv Hp Hsrrrr Hin;apply in_map_iff in Hin;exrepnd;invertsn Hin0;
  apply Hsrrrr in Hin1;eauto 3 with slow.
Qed.


Ltac arithsimpl := let XX:= fresh "XX" in  repeat match goal with 
[ |- context [?n-0]] => assert (n-0 = n) as XX by omega; rw XX; clear XX
end.

Hint Resolve isprogram_bt_implies  isprogram_fix : slow.


Lemma lsubst_single_varren {p} : forall vx vy e,
  subset (@free_vars p e) [vx]
  -> subset (free_vars (lsubst e [(vx,vterm vy)])) [vy].
Abort.

Lemma lsubst_single_varren_if {p} : forall vx vy e,
  subset (@free_vars p (lsubst e [(vx,vterm vy)])) [vy]
  ->   subset (free_vars e) [vx,vy].
Abort.

Lemma compute_step_fix_iscan {o} :
  forall lib (t : @NTerm o),
    iscan t
    -> compute_step lib (mk_fix t) = csuccess (mk_apply t (mk_fix t)).
Proof.
  introv isc; apply iscan_implies in isc; repndors; exrepnd; subst; csunf; simpl; auto.
Qed.

Lemma crary_5_8_aux {p} : forall lib (f e1 e2 : @NTerm p),
  let bt1:= bterm [nvarx] e1 in
  computes_in_1step lib (apply_bterm bt1 [(mk_fix f)]) e2
  -> isvalue f
  -> isprogram_bt bt1
  ->  {e2' : NTerm  $ let bt2 := (bterm [nvarx] e2') in 
                 alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
                 # {j : nat $ j <=1 # forall k,
                               k >= j
                               -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                                         (apply_bterm bt1 [(fix_approx (k) f)])
                                      }}.
Proof.
  introv Hcv  Hp Hpb.
  invertsn Hp.
  assert (isprogram (mk_fix f)) by eauto 2 with slow.
  assert (prog_sub [(nvarx, mk_fix f)]) as XX by prove_sub_range_sat.
  unfold apply_bterm in Hcv.
  simpl in Hcv.
  applydup @crary5_7_original in Hcv; simpl;repeat(decomp_progc2);auto;
    [ |unfold subst;fold_applybt; apply @isprogram_bt_implies; spc; try(in_reasoning); subst; spc].
  dorn Hcv0; exrepnd.
  - exists e2'. dands.
    + dimp (Hcv1 (mk_fix f)). invertsn hyp.
      repnd. allunfold @apply_bterm. allunfold @subst.
      allsimpl. eapply  compute_1step_eq in Hcv; eauto. subst.
      eauto 2 with slow.
    + exists 0. dands; auto. introv Hlt. arithsimpl.
      dimp (Hcv1 (fix_approx k f));[ eauto 2 with slow |].
      invertsn hyp.
      repnd.
      invertsna hyp0 Hcc.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc; 
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc; 
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.
  - invertsn Hcv2.
    fold_terms.
    rw @compute_step_fix_iscan in Hcv2; auto.
    exists (subst e1' nvary (mk_apply f (vterm nvarx))).
    dands.
    + invertsn Hcv2.
      dimp (Hcv0 (mk_fix f)).
      allfold (mk_fix f).
      apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
      unfold subst in Hcv1.
      match type of Hcv1 with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
      simpl in YY.
      rw (lsubst_lsubst_aux_prog_sub (@vterm p nvarx)) in YY; auto;[].
      simpl in YY.
      match type of YY with
      context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
      end.
      rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
      simpl in YY. unfold apply_bterm, subst. simpl.
      match goal with
      [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
        pose proof (combine_sub_nest t subin subout) as ZZ
      end.
      alpharws ZZ. clear ZZ.
      simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;[].
      simpl. rw @lsubst_aux_trivial2; auto;[].
      allrw @fold_nobnd.
      rw @fold_apply.
      match goal with
      [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
      end.
      assert (isprogram (mk_apply f (mk_fix f))) by eauto 2 with slow.
      rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
      [| introv Hinc; invertsn Hinc; inverts Hinc].
      eapply computes_in_1step_alpha_r;[|eauto|eauto|eauto]; eauto 3 with slow.
      apply lsubst_wf_if_eauto; eauto 3 with slow.
    + exists 1. dands; auto. introv Hgt.
      unfold apply_bterm, subst. simpl.
      apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
      unfold subst in Hcv1.
      match type of Hcv1 with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
      simpl in YY.
      assert (isprogram  (fix_approx k f)) by (eauto with slow).
      assert (prog_sub  [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
      rw (lsubst_lsubst_aux_prog_sub (@vterm p nvarx)) in YY; auto;[].
      simpl in YY.
      match type of YY with
      context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
      end.
      rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
      simpl in YY. apply (approx_alpha_rw_r _ _ _ _ YY);[].
      assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
      match goal with
      [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
        pose proof (combine_sub_nest t subin subout) as ZZ
      end.
      apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
      simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;
      try prove_sub_range_sat;[].
      simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
      allrw @fold_nobnd.
      rw @fold_apply.
      let t := constr:(fix_approx (S (k-1)) f) in
      let ts := eval simpl in t in
      (assert (ts=t) as X99 by refl; rw X99; clear X99).
      assert ((S (k - 1)) = k) as X99 by omega; rw X99; clear X99.
      match goal with
      [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
      end.
      rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
    apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
    simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
    unfold apply_bterm in Hpb.
    simpl in Hpb.
    Hint Constructors t_iff : slow.
    apply alphaeq_preserves_program in YY.
    apply YY in Hpb. clear YY.
    applydup @isprogram_lsubst_implies_ispbt in Hpb.
    simpl in Hpb0.
    applydup @isprogam_bt_nt_wf_eauto in Hpb0.
    apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), fix_approx k f]) in Hpb0;
    simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
    apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial].
    simpl.
    dands; auto;[| apply approx_refl; trivial].
    remember (k-1) as kp.
    assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
    subst kp.
    apply (is_approx_chain_fix_aprox _ _ Hp (k-1)).
Qed.

Lemma crary_5_8_aux_exc {o} : forall lib (f e1 e2 : @NTerm o),
  let bt1:= bterm [nvarx] e1 in
  computes_in_1step lib (apply_bterm bt1 [(mk_fix f)]) e2
  -> isp_can_or_exc f
  -> isprogram_bt bt1
  -> {e2' : NTerm  $ let bt2 := (bterm [nvarx] e2') in
                alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
                # {j : nat $ j <=1 # forall k,
                              k >= j
                              -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                                        (apply_bterm bt1 [(fix_approx (k) f)])
                                     }}.
Proof.
  introv Hcv Hp Hpb.
  destruct Hp as [isp Hp].
  assert (isprogram (mk_fix f)) as ispfix by eauto 2 with slow.
  assert (prog_sub [(nvarx, mk_fix f)]) as XX by prove_sub_range_sat.
  unfold apply_bterm in Hcv.
  simpl in Hcv.
  applydup @crary5_7_original in Hcv; simpl;repeat(decomp_progc2);auto;
    [ |unfold subst;fold_applybt; apply @isprogram_bt_implies; spc; try(in_reasoning); subst; spc].
  dorn Hcv0; exrepnd.

  - exists e2'. dands.

    + dimp (Hcv1 (mk_fix f)). invertsn hyp.
      repnd. allunfold @apply_bterm. allunfold @subst.
      allsimpl. eapply  compute_1step_eq in Hcv; eauto. subst.
      eauto 2 with slow.

    + exists 0. dands; auto. introv Hlt. arithsimpl.
      dimp (Hcv1 (fix_approx k f));[ eauto 2 with slow |].
      invertsn hyp.
      repnd.
      invertsna hyp0 Hcc.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc;
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc;
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.

  - invertsn Hcv2.
    destruct Hp as [Hp|Hp].

    + fold_terms; rw @compute_step_fix_iscan in Hcv2; auto.
      exists (subst e1' nvary (mk_apply f (vterm nvarx))).
      dands.

      * invertsn Hcv2.
        dimp (Hcv0 (mk_fix f)).
        allfold (mk_fix f).
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. unfold apply_bterm, subst. simpl.
        match goal with
            [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        alpharws ZZ. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;[].
        simpl. rw @lsubst_aux_trivial2; auto;[].
        allrw @fold_nobnd.
        rw @fold_apply.
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        assert (isprogram (mk_apply f (mk_fix f))) by eauto 2 with slow.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        eapply computes_in_1step_alpha_r;[|eauto|eauto|eauto]; eauto 3 with slow.
        apply lsubst_wf_if_eauto; eauto 3 with slow.

      * exists 1. dands; auto. introv Hgt.
        unfold apply_bterm, subst. simpl.
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        assert (isprogram  (fix_approx k f)) by (eauto with slow).
        assert (prog_sub  [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. apply (approx_alpha_rw_r _ _ _ _ YY);[].
        assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
        match goal with
            [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;
               try prove_sub_range_sat;[].
        simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
        allrw @fold_nobnd.
        rw @fold_apply.
        let t := constr:(fix_approx (S (k-1)) f) in
        let ts := eval simpl in t in
                                 (assert (ts=t) as X99 by refl; rw X99; clear X99).
        assert ((S (k - 1)) = k) as X99 by omega; rw X99; clear X99.
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        unfold apply_bterm in Hpb.
        simpl in Hpb.
        Hint Constructors t_iff : slow.
        apply alphaeq_preserves_program in YY.
        apply YY in Hpb. clear YY.
        applydup @isprogram_lsubst_implies_ispbt in Hpb.
        simpl in Hpb0.
        applydup @isprogam_bt_nt_wf_eauto in Hpb0.
        apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), fix_approx k f]) in Hpb0;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial].
        simpl.
        dands; auto;[| apply approx_refl; trivial].
        remember (k-1) as kp.
        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        subst kp.
        apply (is_approx_chain_fix_aprox _ _ isp (k-1)).

    + apply isexc_implies in Hp; auto; exrepnd.
      rw Hp1 in Hcv2; csunf Hcv2; simpl in Hcv2.
      unfold compute_step_catch in Hcv2.
      inversion Hcv2 as [h]; clear Hcv2.
      allrw @fold_exception.
      rw <- Hp1 in h.
      rw <- h in Hcv0.
      clear dependent t'.

      exists (subst e1' nvary f).
      dands.

      * dimp (Hcv0 (mk_fix f)).
        allfold (mk_fix f).
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. unfold apply_bterm, subst. simpl.
        match goal with
            [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        alpharws ZZ. clear ZZ.
        simpl.
        rw (lsubst_lsubst_aux_prog_sub f); auto;[].
        simpl. rw @lsubst_aux_trivial2; auto;[].
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        eapply computes_in_1step_alpha_r;[|eauto|eauto|eauto]; eauto 3 with slow.
        apply lsubst_wf_if_eauto; eauto 3 with slow.

      * exists 1. dands; auto. introv Hgt.
        unfold apply_bterm, subst. simpl.
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        assert (isprogram (fix_approx k f)) by (eauto with slow).
        assert (prog_sub [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY.
        apply (approx_alpha_rw_r _ _ _ _ YY);[].
        assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
        match goal with
            [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub f); auto;
               try prove_sub_range_sat;[].
        simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        unfold apply_bterm in Hpb.
        simpl in Hpb.
        Hint Constructors t_iff : slow.
        apply alphaeq_preserves_program in YY.
        apply YY in Hpb. clear YY.
        applydup @isprogram_lsubst_implies_ispbt in Hpb.
        simpl in Hpb0.
        applydup @isprogam_bt_nt_wf_eauto in Hpb0.
        apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), f]) in Hpb0;
          simpl; auto;
          [|introv Hin; repeat(in_reasoning); cpx; repeat subst; prove_isprogram; fail].

        apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial];

        simpl.
        dands; auto.

        remember (k-1) as kp.
        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        subst kp.
        apply (is_approx_chain_fix_aprox _ _ isp (k-1)).

        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        simpl.
        apply reduces_to_implies_approx1; auto; prove_isprogram.
        subst.
        exists 1.
        rw @reduces_in_atmost_k_steps_S.
        exists (mk_exception a e); simpl; dands; try reflexivity.
Qed.

Lemma crary_5_8_aux_val_like {o} : forall lib (f e1 e2 : @NTerm o),
  let bt1:= bterm [nvarx] e1 in
  computes_in_1step lib (apply_bterm bt1 [(mk_fix f)]) e2
  -> isprogram f
  -> isvalue_like f
  -> isprogram_bt bt1
  -> {e2' : NTerm  $ let bt2 := (bterm [nvarx] e2') in
                alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
                # {j : nat $ j <=1 # forall k,
                              k >= j
                              -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                                        (apply_bterm bt1 [(fix_approx (k) f)])
                                     }}.
Proof.
  introv Hcv Hp Hvl Hpb.
  assert (isprogram (mk_fix f)) as ispfix by eauto 2 with slow.
  assert (prog_sub [(nvarx, mk_fix f)]) as XX by prove_sub_range_sat.
  unfold apply_bterm in Hcv.
  simpl in Hcv.
  applydup @crary5_7_original in Hcv; simpl;repeat(decomp_progc2);auto;
    [ |unfold subst;fold_applybt; apply @isprogram_bt_implies; spc; try(in_reasoning); subst; spc].
  dorn Hcv0; exrepnd.

  - exists e2'. dands.

    + dimp (Hcv1 (mk_fix f)). invertsn hyp.
      repnd. allunfold @apply_bterm. allunfold @subst.
      allsimpl. eapply  compute_1step_eq in Hcv; eauto. subst.
      eauto 2 with slow.

    + exists 0. dands; auto. introv Hlt. arithsimpl.
      dimp (Hcv1 (fix_approx k f));[ eauto 2 with slow |].
      invertsn hyp.
      repnd.
      invertsna hyp0 Hcc.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc;
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.
      * unfold apply_bterm.
        simpl. allunfold @subst.
        apply (approx_alpha_rw_l _ _ _ _ hyp).
        apply reduces_to_implies_approx_eauto;
          [fold_applybt;apply @isprogram_bt_implies; spc;
           try(in_reasoning); subst; spc; eauto 2 with slow|].
        rw <- Hcc0.
        exists 1;simpl; eauto.

  - invertsn Hcv2.
    dorn Hvl.

    + fold_terms; rw @compute_step_fix_iscan in Hcv2; auto.
      exists (subst e1' nvary (mk_apply f (vterm nvarx))).
      dands.

      * invertsn Hcv2.
        dimp (Hcv0 (mk_fix f)).
        allfold (mk_fix f).
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. unfold apply_bterm, subst. simpl.
        match goal with
            [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        alpharws ZZ. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;[].
        simpl. rw @lsubst_aux_trivial2; auto;[].
        allrw @fold_nobnd.
        rw @fold_apply.
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        assert (isprogram (mk_apply f (mk_fix f))) by eauto 2 with slow.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        eapply computes_in_1step_alpha_r;[|eauto|eauto|eauto]; eauto 3 with slow.
        apply lsubst_wf_if_eauto; eauto 3 with slow.

      * exists 1. dands; auto. introv Hgt.
        unfold apply_bterm, subst. simpl.
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        assert (isprogram  (fix_approx k f)) by (eauto with slow).
        assert (prog_sub  [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. apply (approx_alpha_rw_r _ _ _ _ YY);[].
        assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
        match goal with
            [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub (mk_apply f (vterm nvarx))); auto;
               try prove_sub_range_sat;[].
        simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
        allrw @fold_nobnd.
        rw @fold_apply.
        let t := constr:(fix_approx (S (k-1)) f) in
        let ts := eval simpl in t in
                                 (assert (ts=t) as X99 by refl; rw X99; clear X99).
        assert ((S (k - 1)) = k) as X99 by omega; rw X99; clear X99.
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        unfold apply_bterm in Hpb.
        simpl in Hpb.
        Hint Constructors t_iff : slow.
        apply alphaeq_preserves_program in YY.
        apply YY in Hpb. clear YY.
        applydup @isprogram_lsubst_implies_ispbt in Hpb.
        simpl in Hpb0.
        applydup @isprogam_bt_nt_wf_eauto in Hpb0.
        apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), fix_approx k f]) in Hpb0;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial].
        simpl.
        dands; auto;[| apply approx_refl; trivial].
        remember (k-1) as kp.
        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        subst kp.
        apply (is_approx_chain_fix_aprox _ _ Hp (k-1)).

    + apply isexc_implies in Hvl; auto; exrepnd.
      rw Hvl1 in Hcv2; csunf Hcv2; simpl in Hcv2.
      unfold compute_step_catch in Hcv2.
      inversion Hcv2 as [h]; clear Hcv2.
      allrw @fold_exception.
      rw <- Hvl1 in h.
      rw <- h in Hcv0.
      clear dependent t'.

      exists (subst e1' nvary f).
      dands.

      * dimp (Hcv0 (mk_fix f)).
        allfold (mk_fix f).
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. unfold apply_bterm, subst. simpl.
        match goal with
            [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        alpharws ZZ. clear ZZ.
        simpl.
        rw (lsubst_lsubst_aux_prog_sub f); auto;[].
        simpl. rw @lsubst_aux_trivial2; auto;[].
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        eapply computes_in_1step_alpha_r;[|eauto|eauto|eauto]; eauto 3 with slow.
        apply lsubst_wf_if_eauto; eauto 3 with slow.

      * exists 1. dands; auto. introv Hgt.
        unfold apply_bterm, subst. simpl.
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        assert (isprogram (fix_approx k f)) by (eauto with slow).
        assert (prog_sub [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY.
        apply (approx_alpha_rw_r _ _ _ _ YY);[].
        assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
        match goal with
            [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub f); auto;
               try prove_sub_range_sat;[].
        simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        unfold apply_bterm in Hpb.
        simpl in Hpb.
        Hint Constructors t_iff : slow.
        apply alphaeq_preserves_program in YY.
        apply YY in Hpb. clear YY.
        applydup @isprogram_lsubst_implies_ispbt in Hpb.
        simpl in Hpb0.
        applydup @isprogam_bt_nt_wf_eauto in Hpb0.
        apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), f]) in Hpb0;
          simpl; auto;
          [|introv Hin; repeat(in_reasoning); cpx; repeat subst; prove_isprogram; fail].

        apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial];

        simpl.
        dands; auto.

        remember (k-1) as kp.
        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        subst kp.
        apply (is_approx_chain_fix_aprox _ _ Hp (k-1)).

        assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
        simpl.
        apply reduces_to_implies_approx1; auto; prove_isprogram.
        subst.
        exists 1.
        rw @reduces_in_atmost_k_steps_S.
        exists (mk_exception a e); simpl; dands; try reflexivity.

        (*
    + apply ismrk_implies in Hvl; auto; exrepnd.
      rw Hvl0 in Hcv2; simpl in Hcv2; ginv.

      remember (mk_marker s) as f.
      exists (subst e1' nvary (mk_fix f)).
      fold_terms.
      dands.

      * dimp (Hcv0 (mk_fix f)).
        allfold (mk_fix f).
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, mk_fix f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY. unfold apply_bterm, subst. simpl.
        match goal with
            [ |- alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout)]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        alpharws ZZ. clear ZZ.
        simpl.
        rw (lsubst_lsubst_aux_prog_sub (mk_fix f)); auto;[].
        simpl.
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        subst.
        eapply compute_1step_alpha2; eauto.

      * exists 1. dands; auto. introv Hgt.
        unfold apply_bterm, subst. simpl.
        apply lsubst_alpha_congr2 with (sub:= [(nvarx, fix_approx k f)]) in Hcv1.
        unfold subst in Hcv1.
        match type of Hcv1 with
            alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
            pose proof (combine_sub_nest t subin subout) as YY;
              apply alpha_eq_trans with (nt1:=l )in YY; auto
        end.
        simpl in YY.
        assert (isprogram (fix_approx k f)) by (eauto with slow).
        assert (prog_sub [(nvarx, fix_approx k f)]) by prove_sub_range_sat.
        rw (lsubst_lsubst_aux_prog_sub (@vterm o nvarx)) in YY; auto;[].
        simpl in YY.
        match type of YY with
            context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
        end.
        rewrite lsubst_app_swap in YY; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        simpl in YY.
        apply (approx_alpha_rw_r _ _ _ _ YY);[].
        assert (isprogram  (fix_approx (k-1) f)) by (eauto with slow).
        match goal with
            [ |- approx _ (lsubst (lsubst ?t ?subin) ?subout) ?r]  =>
            pose proof (combine_sub_nest t subin subout) as ZZ
        end.
        apply (approx_alpha_rw_l _ _ _ _ ZZ);[]. clear ZZ.
        simpl. rw (lsubst_lsubst_aux_prog_sub (mk_fix f)); auto;
               try prove_sub_range_sat;[].
        simpl. rw @lsubst_aux_trivial2; auto;try prove_sub_range_sat;[].
        match goal with
            [ |-  context[[?s1,?s2]]] => rewrite (cons_as_app _ s1 [s2])
        end.
        rewrite lsubst_app_swap; simpl; auto; try prove_sub_range_sat;
        [| introv Hinc; invertsn Hinc; inverts Hinc].
        apply @isprogram_bt_implies with (lnt:= [fix_approx k f]) in Hpb;
          simpl; auto; [|introv Hin; repeat(in_reasoning); cpx; subst; auto;fail].
        unfold apply_bterm in Hpb.
        simpl in Hpb.
        Hint Constructors t_iff : slow.
        apply alphaeq_preserves_program in YY.
        apply YY in Hpb. clear YY.
        applydup @isprogram_lsubst_implies_ispbt in Hpb.
        simpl in Hpb0.
        applydup @isprogam_bt_nt_wf_eauto in Hpb0.
        apply @isprogram_bt_implies with (lnt:= [(fix_approx (k - 1) f), mk_fix f]) in Hpb0;
          simpl; auto;
          [|introv Hin; repeat(in_reasoning); cpx; repeat subst; prove_isprogram; fail].
        unfold apply_bterm in Hpb0; simpl in Hpb0.

        apply lsubst_approx_congr; auto; [| apply approx_open_refl; trivial];
        simpl.
        dands; auto.

        { remember (k-1) as kp.
          assert (k = (S (k - 1))) as X99 by omega; rewrite X99 ; clear X99.
          subst kp.
          apply (is_approx_chain_fix_aprox _ _ Hp (k-1)). }

        { fold_terms; subst.
          apply approx_ncan_primarg_marker; auto. }*)
Qed.


Lemma crary_5_8_aux2 {o} : forall lib (f e1 e2 : @NTerm o),
  let bt1:= bterm [nvarx] e1 in
  compute_step lib (apply_bterm bt1 [(mk_fix f)]) = csuccess e2
  -> isvalue f
  -> isprogram_bt bt1
  ->  {e2' : NTerm  $ let bt2 := (bterm [nvarx] e2') in
                 alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
                 # {j : nat $ j <= 1 # forall k,
                               k >= j
                               -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                                         (apply_bterm bt1 [(fix_approx (k) f)])
                                      }}.
Proof.
  simpl. introv Hcv Hv Hpb.
  remember ((apply_bterm (bterm [nvarx] e1) [mk_fix f])) as e1s.
  destruct e1s as [|?| e1so e1slbt]; [invertsn Hcv| | ].

  { csunf Hcv; allsimpl; ginv.
    allunfold @apply_bterm; allsimpl.
    unflsubst in Heqe1s;
      [|apply cl_sub_cons; dands; eauto 3 with slow;
        unfold closed; simpl; simpl; autorewrite with slow;
        inversion Hv as [? w c]; subst; inversion w as [cl wf]; auto].
    Opaque beq_var.
    destruct e1 as [v|f1|op bs]; allsimpl; ginv.
    - boolvar; ginv.
    - exists (sterm f1); autorewrite with slow; dands; auto.
      exists 0; dands; auto.
      introv i; autorewrite with slow; auto.
      apply approx_refl; eauto 3 with slow. }

  destruct e1so as [e1sc | e1snc | e1se | e1sa].
  - simpl in Hcv. invertsn Hcv. exists e1. rw <- Heqe1s. dands; auto.
    exists 0. dands; auto. intros. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.
  - apply c1step_nc in Hcv. rw Heqe1s in Hcv.
    apply crary_5_8_aux in Hcv; auto.
  - simpl in Hcv; inversion Hcv; subst; GC.
    exists e1; dands; auto.
    rw Heqe1s; apply alpha_eq_refl.
    exists 0; dands; auto; intros; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.
(*  - allsimpl; ginv.
    allrw.
    exists e1; dands; auto.
    exists 0; dands; auto; introv i; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.*)
  - apply c1step_ab in Hcv. rw Heqe1s in Hcv.
    apply crary_5_8_aux in Hcv; auto.
Qed.

Lemma crary_5_8_aux2_exc {o} :
  forall lib (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    compute_step lib (apply_bterm bt1 [(mk_fix f)]) = csuccess e2
    -> isp_can_or_exc f
    -> isprogram_bt bt1
    -> {e2' : NTerm
         $ let bt2 := (bterm [nvarx] e2') in
           alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
           # {j : nat
               $ j <= 1
                 # forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
       }}.
Proof.
  simpl.
  introv Hcv Hv Hpb.
  remember ((apply_bterm (bterm [nvarx] e1) [mk_fix f])) as e1s.
  destruct e1s as [| | e1so e1slbt]; [invertsn Hcv| | ].

  { csunf Hcv; allsimpl; ginv.
    allunfold @apply_bterm; allsimpl.
    unflsubst in Heqe1s; [|eauto 5 with slow].
    destruct e1 as [v|f1|op bs]; allsimpl; ginv.
    - boolvar; ginv.
    - exists (sterm f1); autorewrite with slow; dands; auto.
      exists 0; dands; auto.
      introv i; autorewrite with slow; auto.
      apply approx_refl; eauto 3 with slow. }

  destruct e1so as [e1sc | e1snc | e1se | e1sa].
  - simpl in Hcv. invertsn Hcv. exists e1. rw <- Heqe1s. dands; auto.
    exists 0. dands; auto. intros. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.
  - apply c1step_nc in Hcv. rw Heqe1s in Hcv.
    apply crary_5_8_aux_exc in Hcv; auto.
  - simpl in Hcv; inversion Hcv; subst; GC.
    exists e1; dands; auto.
    rw Heqe1s; apply alpha_eq_refl.
    exists 0; dands; auto; intros; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.
(*  - allsimpl; ginv.
    allrw.
    exists e1; dands; auto.
    exists 0; dands; auto; intros; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    invertsn Hv. prove_sub_range_sat. eauto with slow.*)
  - apply c1step_ab in Hcv. rw Heqe1s in Hcv.
    apply crary_5_8_aux_exc in Hcv; auto.
Qed.

Lemma crary_5_8_aux2_val_like {o} :
  forall lib (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    compute_step lib (apply_bterm bt1 [(mk_fix f)]) = csuccess e2
    -> isprogram f
    -> isvalue_like f
    -> isprogram_bt bt1
    -> {e2' : NTerm
         $ let bt2 := (bterm [nvarx] e2') in
           alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
           # {j : nat
               $ j <= 1
                 # forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
       }}.
Proof.
  simpl.
  introv Hcv Hp Hvl Hpb.
  remember ((apply_bterm (bterm [nvarx] e1) [mk_fix f])) as e1s.
  destruct e1s as [| | e1so e1slbt]; [invertsn Hcv| | ].

  { csunf Hcv; allsimpl; ginv.
    allunfold @apply_bterm; allsimpl.
    unflsubst in Heqe1s;[|eauto 5 with slow].
    destruct e1 as [v|f1|op bs]; allsimpl; ginv.
    - boolvar; ginv.
    - exists (sterm f1); autorewrite with slow; dands; auto.
      exists 0; dands; auto.
      introv i; autorewrite with slow; auto.
      apply approx_refl; eauto 3 with slow. }

  destruct e1so as [e1sc | e1snc | e1se | e1sa].
  - simpl in Hcv. invertsn Hcv. exists e1. rw <- Heqe1s. dands; auto.
    exists 0. dands; auto. intros. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto with slow.
  - apply c1step_nc in Hcv.
    rw Heqe1s in Hcv.
    apply crary_5_8_aux_val_like in Hcv; auto.
  - simpl in Hcv; inversion Hcv; subst; GC.
    exists e1; dands; auto.
    rw Heqe1s; apply alpha_eq_refl.
    exists 0; dands; auto; intros; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto with slow.
(*  - allsimpl; ginv.
    allrw.
    exists e1; dands; auto.
    exists 0; dands; auto; intros; arithsimpl.
    apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto with slow.*)
  - apply c1step_ab in Hcv. rw Heqe1s in Hcv.
    apply crary_5_8_aux_val_like in Hcv; auto.
Qed.

(* end hide *)
(** %\noindent% Here is a weaker version of Crary's 5.8
    that certainly holds for our system. In the place of the hypothesis
    [isvalue f], Crary only had the hypothesis
    [isprogram f].
    In his proof, Crary uses the fact that [mk_fix f] evaluates to
    [mk_apply f (mk_fix f)] in his computation system.
    In our system, [f] needs to be a value for that to be true.
*)


Lemma weaker_crary_5_8_aux2 {o} : forall lib k (f e1 e2 : @NTerm o),
let bt1:= bterm [nvarx] e1 in
compute_at_most_k_steps lib k (apply_bterm bt1 [(mk_fix f)])  = csuccess e2
-> isvalue f (* this was only isprogram in Crary_5_8 *)
-> isprogram_bt bt1
->  {e2' : NTerm  $ let bt2 := (bterm [nvarx] e2') in
       alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
       # {j : nat $ forall k,
               k >= j
               -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                         (apply_bterm bt1 [(fix_approx (k) f)])
                      }}.
Proof.
  induction k as [| K Hind]; introv Hcv Hv Hpb; applydup @isvalue_program in Hv.
  - allsimpl. exists e1. invertsn Hcv. dands; spc.
    exists 0. spc. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto 2 with slow.
  - simpl in Hcv.
    match type of Hcv with
    context [compute_at_most_k_steps ?lib ?K ?t] =>
      remember (compute_at_most_k_steps lib K t) as ck
    end.
    destruct ck as [cks | ?];[ | invertsn Hcv];[].
    symmetry in Heqck.
    applydup @computek_preserves_program in Heqck;
      [ | apply @isprogram_bt_implies; auto;[];
        prove_sub_range_sat; eauto 2 with slow; fail].
    apply Hind in Heqck; auto;[].
    allsimpl. exrepnd.
    eapply compute_step_alpha in Hcv;[| |exact Heqck2]; eauto 3 with slow;[].
    exrepnd.
    apply (alphaeq_preserves_program  _ _ Heqck2) in Heqck0.
    apply @isprogram_lsubst_implies_ispbt in Heqck0.
    simpl in Heqck0.
    apply  crary_5_8_aux2 in Hcv1; auto. allsimpl.
    exrepnd.
    rename e2'0 into e2''. exists e2''.
    dands; eauto 2 with slow.
    exists (j+j0).
    introv Hlt.
    dimp (Heqck3 k);[ omega |].
    dimp (Hcv3 (k-j) );[ omega |].
    assert ((k - (j + j0)) = (k - j - j0)) as XX by omega.
    rw XX.
    eapply approx_trans; eauto.
Qed.

Lemma weaker_crary_5_8_aux2_exc {o} :
  forall lib k (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    compute_at_most_k_steps lib k (apply_bterm bt1 [(mk_fix f)])  = csuccess e2
    -> isp_can_or_exc f
    -> isprogram_bt bt1
    ->  {e2' : NTerm
          $ let bt2 := (bterm [nvarx] e2') in
            alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                $ forall k,
                    k >= j
                    -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                              (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  induction k as [| K Hind]; introv Hcv Hv Hpb;
  dup Hv as ispce;
  invertsn Hv.

  - allsimpl. exists e1. invertsn Hcv. dands; spc.
    exists 0. spc. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto 2 with slow.

  - simpl in Hcv.
    match type of Hcv with
    context [compute_at_most_k_steps ?lib ?K ?t] =>
      remember (compute_at_most_k_steps lib K t) as ck
    end.
    destruct ck as [cks | ?];[ | invertsn Hcv];[].
    symmetry in Heqck.
    applydup @computek_preserves_program in Heqck;
      [ | apply @isprogram_bt_implies; auto;[];
        prove_sub_range_sat; eauto 2 with slow; fail].
    apply Hind in Heqck; auto; [].
    allsimpl. exrepnd.
    eapply compute_step_alpha in Hcv;[| |exact Heqck2]; eauto 3 with slow;[].
    exrepnd.
    apply (alphaeq_preserves_program  _ _ Heqck2) in Heqck0.
    apply @isprogram_lsubst_implies_ispbt in Heqck0.
    simpl in Heqck0.
    apply crary_5_8_aux2_exc in Hcv1; auto. allsimpl.
    exrepnd.
    rename e2'0 into e2''. exists e2''.
    dands; eauto 2 with slow.
    exists (j+j0).
    introv Hlt.
    dimp (Heqck3 k);[ omega |].
    dimp (Hcv3 (k-j) );[ omega |].
    assert ((k - (j + j0)) = (k - j - j0)) as XX by omega.
    rw XX.
    eapply approx_trans; eauto.
Qed.

Lemma weaker_crary_5_8_aux2_val_like {o} :
  forall lib k (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    compute_at_most_k_steps lib k (apply_bterm bt1 [(mk_fix f)])  = csuccess e2
    -> isprogram f
    -> isvalue_like f
    -> isprogram_bt bt1
    ->  {e2' : NTerm
          $ let bt2 := (bterm [nvarx] e2') in
            alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                $ forall k,
                    k >= j
                    -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                              (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  induction k as [| K Hind]; introv Hcv Hp Hvl Hpb.

  - allsimpl. exists e1. invertsn Hcv. dands; spc.
    exists 0. spc. arithsimpl. apply approx_refl.
    apply @isprogram_bt_implies; auto;[].
    prove_sub_range_sat. eauto 2 with slow.

  - simpl in Hcv.
    match type of Hcv with
    context [compute_at_most_k_steps ?lib ?K ?t] =>
      remember (compute_at_most_k_steps lib K t) as ck
    end.
    destruct ck as [cks | ?];[ | invertsn Hcv];[].
    symmetry in Heqck.
    applydup @computek_preserves_program in Heqck;
      [ | apply @isprogram_bt_implies; auto;[];
        prove_sub_range_sat; eauto 2 with slow; fail].
    apply Hind in Heqck; auto; [].
    allsimpl. exrepnd.
    eapply compute_step_alpha in Hcv;[| |exact Heqck2]; eauto 3 with slow;[].
    exrepnd.
    apply (alphaeq_preserves_program  _ _ Heqck2) in Heqck0.
    apply @isprogram_lsubst_implies_ispbt in Heqck0.
    simpl in Heqck0.
    apply crary_5_8_aux2_val_like in Hcv1; auto. allsimpl.
    exrepnd.
    rename e2'0 into e2''. exists e2''.
    dands; eauto 2 with slow.
    exists (j+j0).
    introv Hlt.
    dimp (Heqck3 k);[ omega |].
    dimp (Hcv3 (k-j) );[ omega |].
    assert ((k - (j + j0)) = (k - j - j0)) as XX by omega.
    rw XX.
    eapply approx_trans; eauto.
Qed.

Corollary weaker_crary_5_8 {o} : forall lib (f e1 e2 : @NTerm o),
let bt1:= bterm [nvarx] e1 in
computes_to_value lib (apply_bterm bt1 [(mk_fix f)]) e2
-> isvalue f (* this was only isprogram in Crary_5_8 *)
-> isprogram_bt bt1
->  {e2' : NTerm  $ disjoint (bound_vars e2') [nvarx]
          #let bt2 := (bterm [nvarx] e2') in
             alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
             # {j : nat $ forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
                            }}.
Proof.
  introv Hcv Hv Hbt.
  repnud Hcv.
  repnud Hcv0.
  exrepnd.
  simpl.
  apply weaker_crary_5_8_aux2 in Hcv1; allsimpl; exrepnd; auto.
  pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
  exrepnd.
  rename ntcv into e2a.
  exists e2a.
  apply disjoint_sym in Hfr1.
  dands; auto.
  - alpharw Hcv1. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
  - exists j. introv Hgt.
    apply Hcv2 in Hgt.
    simpl. apply (( fun l a b c d e => approx_alpha_rw_l_aux l a b c e d)  _ _ _ _ Hgt).
    clear Hgt Hcv2. unfold apply_bterm. simpl.
    apply lsubst_alpha_congr2; auto.
Qed.

Corollary weaker_crary_5_8_isp_can_or_exc {o} :
  forall lib (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    computes_to_value lib (apply_bterm bt1 [(mk_fix f)]) e2
    -> isp_can_or_exc f
    -> isprogram_bt bt1
    -> {e2' : NTerm
          $ disjoint (bound_vars e2') [nvarx]
          # let bt2 := bterm [nvarx] e2' in
            alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                 $ forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  introv Hcv Hv Hbt.
  destruct Hv as [isp isce].
  destruct isce as [isc|ise].
  - apply weaker_crary_5_8; sp; try (complete (rw @isvalue_iff; sp)).
  - repnud Hcv.
    repnud Hcv0.
    exrepnd.
    simpl.
    apply weaker_crary_5_8_aux2_exc in Hcv1; allsimpl; exrepnd; auto;
    try (complete (split; auto; right; auto)).
    pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
    exrepnd.
    rename ntcv into e2a.
    exists e2a.
    apply disjoint_sym in Hfr1.
    dands; auto.
    + alpharw Hcv1. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
    + exists j.
      introv Hgt.
      apply Hcv2 in Hgt.
      simpl. apply ((fun l a b c d e => approx_alpha_rw_l_aux l a b c e d)  _ _ _ _ Hgt).
      clear Hgt Hcv2. unfold apply_bterm. simpl.
      apply lsubst_alpha_congr2; auto.
Qed.

Corollary weaker_crary_5_8_val_like {o} :
  forall lib (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    computes_to_value lib (apply_bterm bt1 [(mk_fix f)]) e2
    -> isprogram f
    -> isvalue_like f
    -> isprogram_bt bt1
    -> {e2' : NTerm
          $ disjoint (bound_vars e2') [nvarx]
          # let bt2 := bterm [nvarx] e2' in
            alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                 $ forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  introv Hcv Hp Hvl Hbt.
  unfold isvalue_like in Hvl.
  repndors.
  - apply weaker_crary_5_8_isp_can_or_exc; sp.
    unfold isp_can_or_exc, is_can_or_exc; sp.
  - apply weaker_crary_5_8_isp_can_or_exc; sp.
    unfold isp_can_or_exc, is_can_or_exc; sp.
(*  - repnud Hcv.
    repnud Hcv0.
    exrepnd.
    simpl.
    apply weaker_crary_5_8_aux2_val_like in Hcv1; allsimpl; exrepnd; auto;
    try (complete (unfold isvalue_like; sp)).
    pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
    exrepnd.
    rename ntcv into e2a.
    exists e2a.
    apply disjoint_sym in Hfr1.
    dands; auto.
    + alpharw Hcv1. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
    + exists j.
      introv Hgt.
      apply Hcv2 in Hgt.
      simpl. apply ((fun l a b c d e => approx_alpha_rw_l_aux l a b c e d)  _ _ _ _ Hgt).
      clear Hgt Hcv2. unfold apply_bterm. simpl.
      apply lsubst_alpha_congr2; auto.*)
Qed.

Corollary weaker_crary_5_8_exc {o} :
  forall lib a (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    computes_to_exception lib a (apply_bterm bt1 [(mk_fix f)]) e2
    -> isvalue f (* this was only isprogram in Crary_5_8 *)
    -> isprogram_bt bt1
    -> {e2' : NTerm
         $ disjoint (bound_vars e2') [nvarx]
            # let bt2 := (bterm [nvarx] e2') in
              alpha_eq (mk_exception a e2) (apply_bterm bt2 [(mk_fix f)])
              # {j : nat
                  $ forall k,
                      k >= j
                      -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                                (apply_bterm bt1 [(fix_approx (k) f)])
       }}.
Proof.
  introv Hcv Hv Hbt.
  repnud Hcv.
  repnud Hcv.
  exrepnd.
  simpl.
  apply weaker_crary_5_8_aux2 in Hcv0; allsimpl; exrepnd; auto.
  pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
  exrepnd.
  rename ntcv into e2a.
  exists e2a.
  apply disjoint_sym in Hfr1.
  dands; auto.
  - alpharw Hcv0. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
  - exists j. introv Hgt.
    apply Hcv2 in Hgt.
    simpl. apply ((fun l a b c d e => approx_alpha_rw_l_aux l a b c e d) _ _ _ _ Hgt).
    clear Hgt Hcv2. unfold apply_bterm. simpl.
    apply lsubst_alpha_congr2; auto.
Qed.

Corollary weaker_crary_5_8_exc_isp_can_or_exc {o} :
  forall lib a (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    computes_to_exception lib a (apply_bterm bt1 [(mk_fix f)]) e2
    -> isp_can_or_exc f
    -> isprogram_bt bt1
    -> {e2' : NTerm
          $ disjoint (bound_vars e2') [nvarx]
          # let bt2 := bterm [nvarx] e2' in
            alpha_eq (mk_exception a e2) (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                 $ forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  introv Hcv Hv Hbt.
  destruct Hv as [isp isce].
  destruct isce as [isc|ise].

  apply weaker_crary_5_8_exc; sp; try (complete (rw @isvalue_iff; sp)).
  repnud Hcv.
  repnud Hcv.
  exrepnd.
  simpl.
  apply weaker_crary_5_8_aux2_exc in Hcv0; allsimpl; exrepnd; auto;
  try (complete (split; auto; right; auto)).
  pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
  exrepnd.
  rename ntcv into e2a.
  exists e2a.
  apply disjoint_sym in Hfr1.
  dands; auto.
  - alpharw Hcv0. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
  - exists j. introv Hgt.
    apply Hcv2 in Hgt.
    simpl. apply ((fun l a b c d e => approx_alpha_rw_l_aux l a b c e d) _ _ _ _ Hgt).
    clear Hgt Hcv2. unfold apply_bterm. simpl.
    apply lsubst_alpha_congr2; auto.
Qed.

Corollary weaker_crary_5_8_exc_val_like {o} :
  forall lib a (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    computes_to_exception lib a (apply_bterm bt1 [(mk_fix f)]) e2
    -> isprogram f
    -> isvalue_like f
    -> isprogram_bt bt1
    -> {e2' : NTerm
          $ disjoint (bound_vars e2') [nvarx]
          # let bt2 := bterm [nvarx] e2' in
            alpha_eq (mk_exception a e2) (apply_bterm bt2 [(mk_fix f)])
            # {j : nat
                 $ forall k,
                     k >= j
                     -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                               (apply_bterm bt1 [(fix_approx (k) f)])
        }}.
Proof.
  introv Hcv Hp Hvl Hbt.
  dorn Hvl.
  - apply weaker_crary_5_8_exc_isp_can_or_exc; auto.
    unfold isp_can_or_exc, is_can_or_exc; sp.
  - apply weaker_crary_5_8_exc_isp_can_or_exc; auto.
    unfold isp_can_or_exc, is_can_or_exc; sp.
(*  - repnud Hcv.
    repnud Hcv.
    exrepnd.
    simpl.
    apply weaker_crary_5_8_aux2_val_like in Hcv0; allsimpl; exrepnd; auto;
    try (complete (unfold isvalue_like; sp)).
    pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
    exrepnd.
    rename ntcv into e2a.
    exists e2a.
    apply disjoint_sym in Hfr1.
    dands; auto.
    + alpharw Hcv0. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
    + exists j.
      introv Hgt.
      apply Hcv2 in Hgt.
      simpl. apply ((fun l a b c d e => approx_alpha_rw_l_aux l a b c e d) _ _ _ _ Hgt).
      clear Hgt Hcv2. unfold apply_bterm. simpl.
      apply lsubst_alpha_congr2; auto.*)
Qed.

(* begin hide *)
Lemma fix_approx_congr {o} : forall lib n (a b : @NTerm o),
  approx lib a b
  -> approx lib (fix_approx n a) (fix_approx n b).
Proof.
  induction n as [| n Hind]; introv Hab.
  - simpl. apply bottom_approx_any.  repeat(decomp_progc); constructor; spc.
  - simpl. repeat(prove_approx); auto;
    apply approx_relates_only_progs in Hab; repnd;
    repeat(decomp_progc); eauto with slow.
Qed.


Lemma fix_cequiv_congr {o} : forall lib n (f fv : @NTerm o),
  cequiv lib f fv
  -> cequiv lib (fix_approx n f) (fix_approx n fv).
Proof.
  introv Hc.
  repnud Hc. repnd.
  split; apply fix_approx_congr; auto.
Qed.

(* end hide *)

(** %\noindent% Crary's constructive proofs of both the LUB
    property and compactness use his lemma 5.8. How
    do we deal with the fact that we only have
    that when the [f] in those theorems (shown above) is a value.
    Intuitively, both these properties are about [approx]
    and since it is a congruence and includes the [reduces_to]
    relation, we are free to replace [f] at any place
    with whatever it reduces.
    So, if [f] does reduce to a value (say [fv]), we
    we can replace [f] with [fv] everywhere and get away with
    just the weaker version of 5.8 which we have. The following 3 lemmas
    justify the legitimacy of that replacement.
    Recall that [cequiv a b] stands for [approx a b # approx b a].

 *)


Lemma reduces_to_subst_fix {o} : forall lib (f fv e : @NTerm o) v,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram_bt (bterm [v] e)
    -> cequiv lib (lsubst e [(v, mk_fix f)]) (lsubst e [(v, mk_fix fv)]).
Proof.
  introv Hred Hprf Hpr.
  applydup @reduces_to_preserves_program in Hred; auto.
  apply reduces_to_implies_cequiv in Hred; auto.
  apply cequiv_subst_congr; auto.
  - apply cequiv_mkfix; auto.
  - apply @isprogram_bt_implies; auto;[]. prove_sub_range_sat; eauto with slow.
Qed.

Lemma reduces_to_subst_fix_aprrox {o} : forall lib n f fv e v,
    @reduces_to o lib f fv
    -> isprogram f
    -> isprogram_bt (bterm [v] e)
    -> cequiv lib (lsubst e [(v, fix_approx n f)]) (lsubst e [(v, fix_approx n fv)]).
Proof.
  introv Hred Hprf Hpr.
  applydup @reduces_to_preserves_program in Hred; auto.
  apply reduces_to_implies_cequiv in Hred; auto.
  apply @isprogram_bt_implies with (lnt:= [fix_approx n f])in Hpr; auto;
    [| prove_sub_range_sat; eauto 2 with slow; fail].
  apply cequiv_subst_congr; auto.
  apply (fix_cequiv_congr lib n); auto.
Qed.

Lemma reduces_to_computes_to_value_rw {o} : forall lib f fv e v c lbt,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram (apply_bterm (bterm [v] e) [mk_fix f])
    -> computes_to_value lib (apply_bterm (bterm [v] e) [mk_fix f])
         (oterm (Can c) lbt)
    -> {lbtv : list (@BTerm o) $ computes_to_value lib (apply_bterm (bterm [v] e) [mk_fix fv])
         (oterm (Can c) lbtv)}.
Proof.
  introv Hred Hprf Hpr Hcv.
  duplicate Hred as Hc.
  applydup @isprogram_lsubst_implies_ispbt in Hpr; auto.
  simpl in Hpr0.
  eapply reduces_to_subst_fix in Hc; eauto.
  repnud Hc.
  clear Hc. rename Hc0 into Hap.
  apply approx_sqle in Hap.
  specialize (Hap (1)).
  invertsn Hap.
  repnud Hap. GC.
  apply Hap2 in Hcv.
  clear Hap2.
  parallel  lbtv Hcv. repnd. auto.
Qed.

(* begin hide *)



Lemma noncan_abs_lsubst_aux {p} :
  forall e vy (t1 t2 : @NTerm p),
    isnoncan t1
    -> isnoncan (subst_aux e vy t1)
    -> isabs t2
    -> isabs (subst_aux e vy t2) [+] isnoncan (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma noncan_abs_lsubst_aux2 {p} :
  forall e vy (t1 t2 : @NTerm p),
    isnoncan t1
    -> isabs (subst_aux e vy t1)
    -> isabs t2
    -> isabs (subst_aux e vy t2) [+] isnoncan (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma noncan_abs_lsubst_aux3 {p} :
  forall e vy (t1 t2 : @NTerm p),
    isabs t1
    -> isabs (subst_aux e vy t1)
    -> isnoncan t2
    -> isabs (subst_aux e vy t2) [+] isnoncan (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma noncan_abs_lsubst_aux4 {p} :
  forall e vy (t1 t2 : @NTerm p),
    isabs t1
    -> isnoncan (subst_aux e vy t1)
    -> isnoncan t2
    -> isabs (subst_aux e vy t2) [+] isnoncan (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma noncan_abs_lsubst_aux5 {p} :
  forall e vy (t1 t2 : @NTerm p),
    isabs t1
    -> isnoncan (subst_aux e vy t1)
    -> isabs t2
    -> isabs (subst_aux e vy t2) [+] isnoncan (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma noncan_abs_lsubst_aux6 {p} :
  forall e vy (t1 t2 : @NTerm p),
    isabs t1
    -> isabs (subst_aux e vy t1)
    -> isabs t2
    -> isabs (subst_aux e vy t2).
Proof.
  unfold subst_aux.
  introv H1n Hisv H2n.
  destruct e as [v| | oo llbt]; allsimpl; boolvar; auto.
Qed.

Lemma alpha_isabs {p} :
  forall t1 t2,
    @alpha_eq p t1 t2
    -> isabs t1
    -> isabs t2.
Proof.
  introns Hc.
  d_isabs Hc0.
  duplicate Hc as Hcc.
  invertsn Hc.
  constructor.
Qed.

Lemma alpha_isabs_isnoncan {p} :
  forall t1 t2,
    @alpha_eq p t1 t2
    -> isabs t1 [+] isnoncan t1
    -> isabs t2 [+] isnoncan t2.
Proof.
  introns Hc.
  dorn Hc0.
  left; eapply alpha_isabs; eauto.
  right; eapply alpha_noncan; eauto.
Qed.

Lemma noncan_abs_lsubst {p} :
  forall e vx (t1 t2 : @NTerm p),
    isnoncan t1
    -> isnoncan (subst e vx t1)
    -> isabs t2
    -> isabs (subst e vx t2) [+] isnoncan (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs_isnoncan _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_noncan _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux with (t1:=t1); eauto.
Qed.

Lemma noncan_abs_lsubst2 {p} :
  forall e vx (t1 t2 : @NTerm p),
    isnoncan t1
    -> isabs (subst e vx t1)
    -> isabs t2
    -> isabs (subst e vx t2) [+] isnoncan (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs_isnoncan _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_abs _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux2 with (t1:=t1); eauto.
Qed.

Lemma noncan_abs_lsubst3 {p} :
  forall e vx (t1 t2 : @NTerm p),
    isabs t1
    -> isabs (subst e vx t1)
    -> isnoncan t2
    -> isabs (subst e vx t2) [+] isnoncan (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs_isnoncan _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_abs _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux3 with (t1:=t1); eauto.
Qed.

Lemma noncan_abs_lsubst4 {p} :
  forall e vx (t1 t2 : @NTerm p),
    isabs t1
    -> isnoncan (subst e vx t1)
    -> isnoncan t2
    -> isabs (subst e vx t2) [+] isnoncan (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs_isnoncan _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_noncan _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux4 with (t1:=t1); eauto.
Qed.

Lemma noncan_abs_lsubst5 {p} :
  forall e vx (t1 t2 : @NTerm p),
    isabs t1
    -> isnoncan (subst e vx t1)
    -> isabs t2
    -> isabs (subst e vx t2) [+] isnoncan (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs_isnoncan _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_noncan _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux5 with (t1:=t1); eauto.
Qed.

Lemma noncan_abs_lsubst6 {p} :
  forall e vx (t1 t2 : @NTerm p),
    isabs t1
    -> isabs (subst e vx t1)
    -> isabs t2
    -> isabs (subst e vx t2).
Proof.
  unfold subst. introv H1nc H1snc H2nc.
  pose proof (change_bvars_alpha_wspec (free_vars t1 ++ free_vars t2) e) as Hfr.
  exrepnd. duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t2)])in Hfr0.
  apply (alpha_isabs _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,t1)])in Hal.
  apply (alpha_isabs _ _ Hal) in H1snc.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp  Hdd H1snc; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  change_to_lsubst_aux4; [| simpl; disjoint_reasoningv;fail ].
  eapply @noncan_abs_lsubst_aux6 with (t1:=t1); eauto.
Qed.

Lemma computes_in_1step_lsubst_abs {p} :
  forall lib e t1 t2 vy,
    computes_in_1step lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isnoncan t1
    -> isabs t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  apply computes_in_1step_noncan_or_abs in H1c.
  dorn H1c.
  - eapply @noncan_abs_lsubst in H1c; eauto.
  - eapply (noncan_abs_lsubst2 e vy t1 t2) in H1c; eauto.
Qed.

Lemma computes_in_1step_lsubst_abs2 {p} :
  forall lib e t1 t2 vy,
    computes_in_1step lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isabs t1
    -> isnoncan t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  apply computes_in_1step_noncan_or_abs in H1c.
  dorn H1c.
  - eapply (noncan_abs_lsubst4 e vy t1 t2) in H1c; eauto.
  - eapply (noncan_abs_lsubst3 e vy t1 t2) in H1c; eauto.
Qed.

Lemma computes_in_1step_lsubst_abs3 {p} :
  forall lib e t1 t2 vy,
    computes_in_1step lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isabs t1
    -> isabs t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  apply computes_in_1step_noncan_or_abs in H1c.
  dorn H1c.
  - eapply (noncan_abs_lsubst5 e vy t1 t2) in H1c; eauto.
  - eapply (noncan_abs_lsubst6 e vy t1 t2) in H1c; eauto.
Qed.

Lemma abs_not_value {p} :
  forall e : @NTerm p,
    isabs e
    -> isvalue e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
  inverts Hisv.
  allapply @iscan_implies; repndors; exrepnd; ginv.
Qed.

Lemma abs_not_exc {p} :
  forall e : @NTerm p,
    isabs e
    -> isexc e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
Qed.

Lemma abs_not_can {p} :
  forall e : @NTerm p,
    isabs e
    -> iscan e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
Qed.

Lemma abs_not_can_or_exc {p} :
  forall e : @NTerm p,
    isabs e
    -> is_can_or_exc e
    -> False.
Proof.
  introv Hisnc Hisv.
  dorn Hisv.
  eapply abs_not_can in Hisnc; eauto.
  eapply abs_not_exc in Hisnc; eauto.
Qed.

Lemma noncan_not_exc {p} :
  forall e : @NTerm p,
    isnoncan e
    -> isexc e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
Qed.

Lemma noncan_not_can {p} :
  forall e : @NTerm p,
    isnoncan e
    -> iscan e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
Qed.

Lemma noncan_not_can_or_exc {p} :
  forall e : @NTerm p,
    isnoncan e
    -> is_can_or_exc e
    -> False.
Proof.
  introv Hisnc Hisv.
  dorn Hisv.
  eapply noncan_not_can in Hisnc; eauto.
  eapply noncan_not_exc in Hisnc; eauto.
Qed.

Lemma computes_in_1step_alpha_lsubst {o} :
  forall lib (e t1 t3 : @NTerm o) (vy0 : NVar),
    computes_in_1step_alpha lib (lsubst e [(vy0, t1)]) (lsubst e [(vy0, t3)])
    -> isnoncan t1
    -> isnoncan t3
    -> isnoncan (lsubst e [(vy0, t3)])[+]isabs (lsubst e [(vy0, t3)]).
Proof.
  introv comp isn1 isn2.
  unfold computes_in_1step_alpha in comp; exrepnd.
  apply computes_in_1step_noncan_or_abs in comp1.
  eapply noncan_or_abs_lsubst; eauto.
Qed.

Lemma computes_in_1step_alpha_lsubst_abs {p} :
  forall lib e t1 t2 vy,
    computes_in_1step_alpha lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isnoncan t1
    -> isabs t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  unfold computes_in_1step_alpha in H1c; exrepnd.
  apply computes_in_1step_noncan_or_abs in H1c1.
  dorn H1c1.
  - eapply @noncan_abs_lsubst in H1c1; eauto.
  - eapply (noncan_abs_lsubst2 e vy t1 t2) in H1c1; eauto.
Qed.

Lemma computes_in_1step_alpha_lsubst_abs2 {p} :
  forall lib e t1 t2 vy,
    computes_in_1step_alpha lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isabs t1
    -> isnoncan t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  unfold computes_in_1step_alpha in H1c; exrepnd.
  apply computes_in_1step_noncan_or_abs in H1c1.
  dorn H1c1.
  - eapply (noncan_abs_lsubst4 e vy t1 t2) in H1c1; eauto.
  - eapply (noncan_abs_lsubst3 e vy t1 t2) in H1c1; eauto.
Qed.

Lemma computes_in_1step_alpha_lsubst_abs3 {p} :
  forall lib e t1 t2 vy,
    computes_in_1step_alpha lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
    -> isabs t1
    -> isabs t2
    -> isabs (lsubst e [(vy, t2)]) [+] isnoncan (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  unfold computes_in_1step_alpha in H1c; exrepnd.
  apply computes_in_1step_noncan_or_abs in H1c1.
  dorn H1c1.
  - eapply (noncan_abs_lsubst5 e vy t1 t2) in H1c1; eauto.
  - eapply (noncan_abs_lsubst6 e vy t1 t2) in H1c1; eauto.
Qed.

(* !!MOVE *)
Lemma isseq_implies {o} :
  forall (t : @NTerm o), isseq t -> {f : ntseq & t = sterm f}.
Proof.
  introv iss.
  destruct t; allsimpl; tcsp.
  eexists; eauto.
Qed.

(* !!MOVE *)
Lemma isseq_implies_iscan {o} :
  forall (t : @NTerm o), isseq t -> iscan t.
Proof.
  introv iss.
  apply isseq_implies in iss; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve isseq_implies_iscan : slow.

Lemma isseq_implies_isvalue_like {o} :
  forall (t : @NTerm o), isseq t -> isvalue_like t.
Proof.
  introv iss.
  eauto 3 with slow.
Qed.
Hint Resolve isseq_implies_isvalue_like : slow.

Lemma crary5_7_value {o} : forall lib k vx vy e ev no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e vx t in
vx <> vy
-> isvalue ev
-> computes_in_kstep_alpha lib k tl ev
-> isprogram t
-> isprogram tl
-> {evc : NTerm $ forall t', isprogram t'
      -> computes_in_kstep_alpha lib k (subst e vx t')
                                   (subst evc vx t')
         # isvalue (subst evc vx t')}
   [+]
   {tv : NTerm $ computes_to_val_like_in_max_k_steps lib t tv k}.
(* This last line used to be: computes_to_value_in_max_k_steps k t tv *)
Proof.
  induction k as [k Hind] using comp_ind_type; introv Hneq Hval Hck Htpr Htlpt.
  destruct k;[ invertsn Hck; left; exists e; intros; dands;[constructor|]; eauto 2 with slow |];
  [ apply alpha_eq_sym in Hck; apply (alpha_preserves_value _ _ Hck) in Hval;
    eapply isvalue_change_subst_noncan; eauto; fail |].

  duplicate Hck as Hckb.
  invertsna Hck Hcsk. duplicate Hcsk as H1csk.
  apply @crary5_7_alpha with (vy:=vy) in Hcsk; auto.
  dorn Hcsk;[| right].

  - exrepnd. dimp (Hcsk1 (oterm (NCan no) lbt)).
    applydup @computes_in_1step_alpha_program in H1csk as ispt2; auto;[].
    applydup @computes_in_1step_alpha_program in hyp as ispt3; auto;[].

    dup hyp as comp.
    eapply computes_in_1step_alpha_r in comp; try (exact H1csk); eauto 3 with slow.
    eapply computes_in_kstep_fun_l in comp; try (exact Hcsk0); eauto 3 with slow.

    apply Hind with (vy:=vy) in comp; auto;[].

    rename comp into Xind.
    remember (oterm (NCan no) lbt) as t.
    dorn Xind;[left| right];
    [exrepnd; exists evc; introv Hpt'; dimp (Xind0 t'); repnd;
       dands; spc; econstructor; eauto; fail|].
    exrepnd. exists tv; auto. dands; auto.
    repnud Xind0.
    apply no_change_after_val_like2 with (k1:=k); auto. unfolds_base. dands; auto.
    apply reduces_atmost_preserves_program in Xind1; auto.
  - exrepnd. clear Hind. clear H1csk Hcsk0.
    rename Hcsk1 into Hale.
    (* simplify to accumulate the context and only keep vy *)
    apply lsubst_alpha_congr2 with (sub:=[(vx, (oterm (NCan no) lbt))]) in Hale.
    allunfold @subst.
    match type of Hale with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
    simpl in YY.
    assert (prog_sub [(vx, oterm (NCan no) lbt)]) as Hpr by (prove_sub_range_sat; auto).
    rw (lsubst_lsubst_aux_prog_sub (@vterm o vx)) in YY; auto.
    simpl in YY. autorewrite with slow in YY.
    match type of YY with
    context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
    end.
    rewrite lsubst_app_swap in YY; simpl; auto; try (prove_sub_range_sat;auto);
      [| introv Hinc; invertsn Hinc; cpx; fail].
    simpl in YY.
    specialize (Hcsk2 (oterm (NCan no) lbt)).
    pose proof (fun td tdc => Hcsk2 td tdc Htpr) as Hcc. clear Hcsk2.
    clear Hale.
    apply alpha_eq_sym in YY. rw <- @simple_lsubst_cons2 in YY;[| (prove_sub_range_sat; auto; fail)].
    unfold subst in YY. remember (lsubst e1' [(vx, oterm (NCan no) lbt)]) as exc.
    assert ( forall td tdc : NTerm,
      isprogram td ->
      (computes_in_1step lib td tdc ->
      computes_in_1step_alpha lib (lsubst exc [(vy, td)])
        (lsubst exc [(vy, tdc)]))
     # (computes_step_to_error lib td ->
         computes_step_to_error lib (lsubst exc [ (vy, td)]))
      ) as Hccb by
      (introv Hptd; dands; introv  Hcsd; applydup Hcc in Hcsd; auto;
      repeat(rw <- (simple_lsubst_cons2 e1') in Hcsd0;[| (prove_sub_range_sat; auto; eauto with slow; fail)]);
      allunfold @subst; subst; auto).
    clear Hcc. rename Hccb into Hcc.
    apply alpha_eq_sym in YY.
    eapply computes_in_kstep_fun_l in Hckb; try (exact YY); eauto 3 with slow.
    eapply alphaeq_preserves_program in Htlpt; try (apply alpha_eq_sym; exact YY).
    assert (forall tt, isprogram tt -> isprogram (lsubst exc [(vy, tt)])) as Hapr by
      (introv Hprr; eapply prog_sub_change; eauto;try prove_sub_range_sat; fail).
    clear dependent e. clear dependent e1'.
    clear dependent vx.
    (* end of simplification *)
    remember (NCan no) as op.
    assert ({ab : opabs & op = NCan no [+] op = Abs ab})
      as opeq by (exists dum_opabs; left; auto).
    exrepnd; clear Heqop.
    generalize dependent no.
    generalize dependent ab.
    generalize dependent op.
    generalize dependent lbt.
    generalize dependent t'.
    induction k as [| k Hind]; introv H1pr Hccv Hcv H2pr opeq;
    dorn opeq; subst;
    try (applydup (noncan_tricot lib) in H1pr as Htri);
    try (applydup (noncan_tricot_abs lib) in H1pr as Htri);
    dorn Htri; exrepnd;
    try(invertsn Hccv;repnud Htri;exrepnd; rw Hccv in Htri; cpx; fail);[|idtac|idtac|].

    + unfold computes_to_val_like_in_max_k_steps.
      repndors;
        try (complete (eexists; dands; simpl; eauto 3 with slow; unfold isvalue_like; sp));
        [|].

      * provefalse.
        d_isnoncan Htri0. applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst in Htri3; auto.
        dorn Htri4.

        { inverts Hcv as Hcv Hdd. inverts Hdd.
          eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
          apply alpha_eq_sym in Htri3.
          apply alpha_noncan in Htri3; auto.
          apply noncan_not_value in Htri3; cpx; eauto 3 with slow. }

        { inverts Hcv as Hcv Hdd. inverts Hdd.
          eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
          apply alpha_eq_sym in Htri3. apply alpha_abs in Htri3; auto.
          apply abs_not_value in Htri3; cpx; eauto 3 with slow. }

      * provefalse.
        d_isabs Htri0.
        applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        dorn Htri3;
          [ apply abs_not_value in Htri3; cpx; eauto 3 with slow
          | apply noncan_not_value in Htri3; cpx; eauto 3 with slow
          ].

    + unfold computes_to_val_like_in_max_k_steps.

      repndors;
        try (complete (eexists; dands; simpl; eauto 3 with slow; unfold isvalue_like; sp));
        [|].

      * provefalse.
        d_isnoncan Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs2 in Htri3; auto.
        dorn Htri4.

        { inverts Hcv as Hcv Hdd. inverts Hdd.
          eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
          apply alpha_eq_sym in Htri3.
          apply alpha_abs in Htri3; auto.
          apply abs_not_value in Htri3; cpx; eauto 3 with slow. }

        { inverts Hcv as Hcv Hdd. inverts Hdd.
          eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
          apply alpha_eq_sym in Htri3.
          apply alpha_noncan in Htri3; auto.
          apply noncan_not_value in Htri3; cpx; eauto 3 with slow. }

      * provefalse.
        d_isabs Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs3 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        dorn Htri3;
          [ apply abs_not_value in Htri3; cpx; eauto 3 with slow
          | apply noncan_not_value in Htri3; cpx; eauto 3 with slow
          ].

    + repndors.

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; eauto 3 with slow.

      * d_isnoncan Htri0.
        duplicate Htri1 as H1step.
        apply c1step_nc in Htri1.
        apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.

        dorn H2tri; exrepnd;[|].

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
               unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; eauto 3 with slow.

      * d_isabs Htri0.
        duplicate Htri1 as H1step.
        apply c1step_nc in Htri1.
        apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (Abs tabs) lbt) as t.
          dorn H2tri0;
            [ exists v;
                dands; auto;
                apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
                repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
                repeat (unfolds_base; dands; auto); fail
                   | ].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; eauto 3 with slow.

    + repndors.

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; eauto 3 with slow.

      * d_isnoncan Htri0.
        duplicate Htri1 as H1step.
        apply c1step_ab in Htri1.
        apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [ exists v;
                dands; auto;
                apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
                repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
                repeat (unfolds_base; dands; auto); fail
                   | ].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind.
          apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; auto; unfold isvalue_like; complete auto.

      * d_isabs Htri0.
        duplicate Htri1 as H1step.
        apply c1step_ab in Htri1.
        apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (Abs tabs) lbt) as t.
          dorn H2tri0;
            [ exists v;
                dands; auto;
                apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
                repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
                repeat (unfolds_base; dands; auto); fail
                   | ].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * exists v.
        dands; auto.
        apply no_change_after_val_like2 with (k1:=1); auto; [|omega].
        unfolds_base; dands; eauto 3 with slow.
Qed.

Lemma alpha_eq_bterms_implies_length {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2
    -> length bs1 = length bs2.
Proof.
  introv aeq.
  unfold alpha_eq_bterms in aeq; sp.
Qed.

Lemma alpha_eq_preserves_has_name {o} :
  forall a (t u : @NTerm o),
    alpha_eq t u
    -> has_name a t
    -> has_name a u.
Proof.
  introv aeq hn.
  allunfold @has_name.
  destruct t as [v|f|op bs]; tcsp;[].
  dopid op as [can|ncan|exc|abs] Case; tcsp;[].
  destruct can; tcsp;[].
  boolvar; tcsp; subst; GC;[].
  apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst.
  boolvar; tcsp.
Qed.

Lemma alphaeq_preserves_isnexc {p} :
  forall lib a (t1 t2 : @NTerm p),
    nt_wf t1
    -> alpha_eq t1 t2
    -> isnexc lib a t1
    -> isnexc lib a t2.
Proof.
  introv wf aeq ise.
  destruct t1; try (complete (inversion ise)).
  destruct o; try (complete (inversion ise)).
  apply alpha_eq_oterm_implies_combine2 in aeq; exrepnd; subst.
  apply isnexc_implies in ise; exrepnd; ginv.
  allunfold @isnexc.
  applydup @alpha_eq_bterms_implies_length in aeq0; allsimpl.
  destruct bs'; allsimpl; cpx.
  allrw @alpha_eq_bterms_cons; repnd.
  destruct b as [l t].
  apply alphaeqbt_nilv in aeq2; exrepnd; ginv.
  unfold computes_to_name.
  pose proof (compute_to_value_alpha lib u nt2 v) as h.
  applydup @nt_wf_oterm_fst in wf.
  repeat (autodimp h hyp); exrepnd.
  exists t2'; dands; auto.
  eapply alpha_eq_preserves_has_name; eauto.
Qed.

Lemma alphaeq_preserves_ispnexc {p} :
  forall lib a (t1 t2 : @NTerm p),
    nt_wf t1
    -> alpha_eq t1 t2
    -> ispnexc lib a t1
    -> ispnexc lib a t2.
Proof.
  introv wf aeq ise.
  destruct ise as [isp ise].
  split.
  - eapply alphaeq_preserves_isnexc in aeq; eauto.
  - apply alphaeq_preserves_program in aeq; auto.
    apply aeq; auto.
Qed.

Lemma subst_nexc {p} :
  forall lib a e vx no lbt,
    isnexc lib a (subst_aux e vx (oterm (NCan no) lbt))
    -> {lbtc : list (@BTerm p) $ e = oterm Exc lbtc}.
Proof.
  unfold subst_aux. introv Hisv. destruct e as [v|f|oo llbt]; allsimpl;
  [revert Hisv; cases_if; simpl; introv Hisv; inverts Hisv|tcsp|];[].
  destruct oo; tcsp.
  boolvar; subst; tcsp.
  eexists; eauto.
Qed.

(*
Lemma isnexc_change_subst_noncan {p} :
  forall lib a e vx no lbt t,
    isnexc lib a (subst e vx (oterm (NCan no) lbt))
    -> @isprogram p t
    -> isnexc lib a (subst e vx t).
Proof.
  introv Hv Hp.
  pose proof (change_bvars_alpha_wspec (free_vars (oterm (NCan no) lbt)) e) as Hfr.
  exrepnd.
  duplicate Hfr0 as Hal.
  apply alpha_eq_sym in Hfr0.
  apply lsubst_alpha_congr2 with (sub:= [(vx,t)])in Hfr0.
  apply (alphaeq_preserves_isnexc _ _ _ _ Hfr0).
  apply lsubst_alpha_congr2 with (sub:= [(vx,(oterm (NCan no) lbt))])in Hal.
  apply (alphaeq_preserves_isnexc _ _ _ _ Hal) in Hv.
  clear dependent e.
  lsubst_lsubst_aux_eq_hyp Hdd Hv; [simpl ;repeat (simpl_sub5); disjoint_reasoningv| ].
  duplicate Hp. repnud Hp0.
  change_to_lsubst_aux4; [| simpl ;rw Hp1; disjoint_reasoningv;fail ].
  apply subst_nexc in Hv.
  exrepnd. subst.
  simpl; boolvar; tcsp.
Qed.

Lemma ispnexc_change_subst_noncan {p} :
  forall a e vx no lbt t,
    ispnexc a (subst e vx (oterm (NCan no) lbt))
    -> @isprogram p t
    -> ispnexc a (subst e vx t).
Proof.
  introv Hv Hp.
  destruct Hv as [ise isp].
  split.
  apply @isnexc_change_subst_noncan with (t := t) in ise; auto.
  eapply isprogram_change_subst_noncan; eauto.
Qed.
 *)

Lemma isnexc_implies_isexc {p} :
  forall lib a (t : @NTerm p), isnexc lib a t -> isexc t.
Proof.
  introv i.
  apply isnexc_implies in i; exrepnd; subst; auto.
Qed.
Hint Resolve isnexc_implies_isexc : slow.

Lemma ispnexc_implies_is_can_or_exc {p} :
  forall lib a (t : @NTerm p), ispnexc lib a t -> is_can_or_exc t.
Proof.
  introv i.
  destruct i as [isp ise].
  right; eauto with slow.
Qed.
Hint Resolve ispnexc_implies_is_can_or_exc : slow.
(* !!MOVE *)
Hint Resolve ispexc_implies_is_can_or_exc : slow.

Lemma crary5_7_exc {o} : forall lib k vx vy e ev no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e vx t in
vx <> vy
-> ispexc ev
-> computes_in_kstep_alpha lib k tl ev
-> isprogram t
-> isprogram tl
-> {evc : NTerm $ forall t', isprogram t'
      -> computes_in_kstep_alpha lib k (subst e vx t')
                                       (subst evc vx t')
         # ispexc (subst evc vx t')}
   [+]
   {tv : NTerm $ computes_to_val_like_in_max_k_steps lib t tv k}.
(* This last line used to be: computes_to_value_in_max_k_steps k t tv *)
Proof.
  induction k as [k Hind] using comp_ind_type; introv Hneq He Hck Htpr Htlpt.
  destruct k;[ invertsn Hck; left; exists e; intros; dands;[constructor|]; eauto 2 with slow |];
  [ apply alpha_eq_sym in Hck;
    apply (alphaeq_preserves_ispexc _ _ Hck) in He;
    eapply ispexc_change_subst_noncan; eauto; fail|].

  duplicate Hck as Hckb.
  invertsna Hck Hcsk. duplicate Hcsk as H1csk. apply  @crary5_7_alpha with (vy:=vy) in Hcsk; auto.

  applydup @computes_in_1step_alpha_program in H1csk as ispt2; auto;[].

  dorn Hcsk;[| right].

  - exrepnd.
    dimp (Hcsk1 (oterm (NCan no) lbt)).
    eapply computes_in_1step_alpha_r in hyp; try (exact H1csk); eauto 3 with slow;[].
    eapply computes_in_kstep_fun_l in Hcsk0; try (exact hyp); eauto 3 with slow;[].

    apply Hind with (vy:=vy) in Hcsk0; auto;
    [|
        eapply computes_in_1step_alpha_program in H1csk; eauto;
        apply (alphaeq_preserves_program _ _ hyp) in H1csk;
        eapply prog_sub_change; eauto;try prove_sub_range_sat].
    rename Hcsk0 into Xind.
    remember (oterm (NCan no) lbt) as t.
    dorn Xind;[left| right];
    [exrepnd; exists evc; introv Hpt'; dimp (Xind0 t'); repnd;
       dands; spc; econstructor; eauto; fail|].
    exrepnd. exists tv; auto. dands; auto. repnud Xind0.
    apply no_change_after_val_like2 with (k1:=k); auto. unfolds_base. dands; auto.
    apply reduces_atmost_preserves_program in Xind1; auto.

  - exrepnd. clear Hind. clear H1csk Hcsk0.
    rename Hcsk1 into Hale.
    (* simplify to accumulate the context and only keep vy *)
    apply lsubst_alpha_congr2 with (sub:=[(vx, (oterm (NCan no) lbt))]) in Hale.
    allunfold @subst.
    match type of Hale with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
    simpl in YY.
    assert (prog_sub [(vx, oterm (NCan no) lbt)]) as Hpr by (prove_sub_range_sat; auto).
    rw (lsubst_lsubst_aux_prog_sub (@vterm o vx)) in YY; auto.
    simpl in YY. autorewrite with slow in YY.
    match type of YY with
    context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
    end.
    rewrite lsubst_app_swap in YY; simpl; auto; try (prove_sub_range_sat;auto);
      [| introv Hinc; invertsn Hinc; cpx; fail].
    simpl in YY.
    specialize (Hcsk2 (oterm (NCan no) lbt)).
    pose proof (fun td tdc => Hcsk2 td tdc Htpr) as Hcc. clear Hcsk2.
    clear Hale.
    apply alpha_eq_sym in YY. rw <- @simple_lsubst_cons2 in YY;[| (prove_sub_range_sat; auto; fail)].
    unfold subst in YY. remember (lsubst e1' [(vx, oterm (NCan no) lbt)]) as exc.
    assert ( forall td tdc : NTerm,
      isprogram td ->
      (computes_in_1step lib td tdc ->
      computes_in_1step_alpha lib (lsubst exc [(vy, td)])
        (lsubst exc [(vy, tdc)]))
     # (computes_step_to_error lib td ->
         computes_step_to_error lib (lsubst exc [ (vy, td)]))
      ) as Hccb by
      (introv Hptd; dands; introv  Hcsd; applydup Hcc in Hcsd; auto;
      repeat(rw <- (simple_lsubst_cons2 e1') in Hcsd0;[| (prove_sub_range_sat; auto; eauto with slow; fail)]);
      allunfold @subst; subst; auto).
    clear Hcc. rename Hccb into Hcc.
    apply alpha_eq_sym in YY.
    eapply computes_in_kstep_fun_l in Hckb; try (exact YY); eauto 3 with slow;[].
    eapply alphaeq_preserves_program in Htlpt; try (apply alpha_eq_sym; exact YY); eauto 3 with slow;[].

    assert (forall tt, isprogram tt -> isprogram (lsubst exc [(vy, tt)])) as Hapr.
    { introv Hprr; eapply prog_sub_change; eauto;try prove_sub_range_sat. }

    clear dependent e. clear dependent e1'.
    clear dependent vx.
    (* end of simplification *)
    remember (NCan no) as op.
    assert ({ab : opabs & op = NCan no [+] op = Abs ab})
      as opeq by (exists dum_opabs; left; auto).
    exrepnd; clear Heqop.
    generalize dependent no.
    generalize dependent ab.
    generalize dependent op.
    generalize dependent lbt.
    generalize dependent t'.
    induction k as [| k Hind]; introv H1pr Hccv Hcv H2pr opeq;
    dorn opeq; subst;
    try (applydup (noncan_tricot lib) in H1pr as Htri);
    try (applydup (noncan_tricot_abs lib) in H1pr as Htri);
    dorn Htri; exrepnd;
    try(invertsn Hccv;repnud Htri;exrepnd; rw Hccv in Htri; cpx; fail);[|idtac|idtac|].

    + unfold computes_to_val_like_in_max_k_steps.

      repndors;
        try (complete (eexists; dands; simpl; eauto 3 with slow)).

      * provefalse.
        d_isnoncan Htri0. applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; eauto 3 with slow.
        }

        { apply alpha_isabs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; eauto 3 with slow.
        }

      * provefalse.
        d_isabs Htri0.
        applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct He.
        dorn Htri3;
          [ apply abs_not_exc in Htri3; cpx; eauto
          | apply noncan_not_exc in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_isexc with (t1 := ev); eauto with slow.

    + unfold computes_to_val_like_in_max_k_steps.

      repndors;
        try (complete (eexists; dands; simpl; eauto 3 with slow)).

      * provefalse.
        d_isnoncan Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs2 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_abs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; eauto 3 with slow.
        }

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; eauto 3 with slow.
        }

      * provefalse.
        d_isabs Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs3 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct He.
        dorn Htri3;
          [ apply abs_not_exc in Htri3; cpx; eauto
          | apply noncan_not_exc in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_isexc with (t1 := ev); eauto with slow.

    + repndors;
      try (complete (exists v; dands; auto;
                            apply no_change_after_val_like2 with (k1:=1);
                            auto; [|omega];
                            unfolds_base; dands; eauto 3 with slow));[|].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
               unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind  with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind  with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

    + repndors;
      try (complete (exists v; dands; auto;
                            apply no_change_after_val_like2 with (k1:=1);
                            auto; [|omega];
                            unfolds_base; dands; tcsp; eauto 3 with slow));[|].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
             repeat (unfolds_base; dands; auto); fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind  with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
               repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
               repeat (unfolds_base; dands; auto); fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind  with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }
Qed.

(*
Lemma crary5_7_mrk {o} : forall lib k vx vy e ev no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e vx t in
vx <> vy
-> ispmrk ev
-> computes_in_kstep_alpha lib k tl ev
-> isprogram t
-> isprogram tl
-> {evc : NTerm $ forall t', isprogram t'
      -> computes_in_kstep_alpha lib k (subst e vx t') (subst evc vx t')
         # ispmrk (subst evc vx t')}
   [+]
   {tv : NTerm $ computes_to_val_like_in_max_k_steps lib t tv k}.
(* This last line used to be: computes_to_value_in_max_k_steps k t tv *)
Proof.
  induction k as [k Hind] using comp_ind_type; introv Hneq He Hck Htpr Htlpt.
  destruct k;[ invertsn Hck; left; exists e; intros; dands;[constructor|]; eauto 2 with slow |];
  [ apply alpha_eq_sym in Hck;
    apply (alphaeq_preserves_ispmrk _ _ Hck) in He;
    eapply ispmrk_change_subst_noncan; eauto; fail|].

  duplicate Hck as Hckb.
  invertsna Hck Hcsk. duplicate Hcsk as H1csk. apply  @crary5_7_alpha with (vy:=vy) in Hcsk; auto.
  dorn Hcsk;[| right].

  - exrepnd. dimp (Hcsk1 (oterm (NCan no) lbt)).
    apply (computes_in_1step_alpha_r _ _ _ _ _ H1csk) in hyp; auto.
    apply (computes_in_kstep_fun_l _ _ _ _ _ hyp) in Hcsk0.
    apply Hind with (vy:=vy) in Hcsk0; auto;
    [|
        eapply computes_in_1step_alpha_program in H1csk; eauto;
        apply (alphaeq_preserves_program _ _ hyp) in H1csk;
        eapply prog_sub_change; eauto;try prove_sub_range_sat].
    rename Hcsk0 into Xind.
    remember (oterm (NCan no) lbt) as t.
    dorn Xind;[left| right];
    [exrepnd; exists evc; introv Hpt'; dimp (Xind0 t'); repnd;
       dands; spc; econstructor; eauto; fail|].
    exrepnd. exists tv; auto. dands; auto. repnud Xind0.
    apply no_change_after_val_like2 with (k1:=k); auto. unfolds_base. dands; auto.
    apply reduces_atmost_preserves_program in Xind1; auto.

  - exrepnd. clear Hind. clear H1csk Hcsk0.
    rename Hcsk1 into Hale.
    (* simplify to accumulate the context and only keep vy *)
    apply lsubst_alpha_congr2 with (sub:=[(vx, (oterm (NCan no) lbt))]) in Hale.
    allunfold @subst.
    match type of Hale with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
    simpl in YY.
    assert (prog_sub [(vx, oterm (NCan no) lbt)]) as Hpr by (prove_sub_range_sat; auto).
    rw (lsubst_lsubst_aux_prog_sub (@vterm o vx)) in YY; auto.
    simpl in YY. autorewrite with slow in YY.
    match type of YY with
    context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
    end.
    rewrite lsubst_app_swap in YY; simpl; auto; try (prove_sub_range_sat;auto);
      [| introv Hinc; invertsn Hinc; cpx; fail].
    simpl in YY.
    specialize (Hcsk2 (oterm (NCan no) lbt)).
    pose proof (fun td tdc => Hcsk2 td tdc Htpr) as Hcc. clear Hcsk2.
    clear Hale.
    apply alpha_eq_sym in YY. rw <- @simple_lsubst_cons2 in YY;[| (prove_sub_range_sat; auto; fail)].
    unfold subst in YY. remember (lsubst e1' [(vx, oterm (NCan no) lbt)]) as exc.
    assert ( forall td tdc : NTerm,
      isprogram td ->
      (computes_in_1step lib td tdc ->
      computes_in_1step lib (lsubst exc [(vy, td)])
        (lsubst exc [(vy, tdc)]))
     # (computes_step_to_error lib td ->
         computes_step_to_error lib (lsubst exc [ (vy, td)]))
      ) as Hccb by
      (introv Hptd; dands; introv  Hcsd; applydup Hcc in Hcsd; auto;
      repeat(rw <- (simple_lsubst_cons2 e1') in Hcsd0;[| (prove_sub_range_sat; auto; eauto with slow; fail)]);
      allunfold @subst; subst; auto).
    clear Hcc. rename Hccb into Hcc.
    apply alpha_eq_sym in YY.
    apply (computes_in_kstep_fun_l _ _ _ _ _ YY) in Hckb.
    apply (alphaeq_preserves_program _ _ YY) in Htlpt.
    assert (forall tt, isprogram tt -> isprogram (lsubst exc [(vy, tt)])) as Hapr by
      (introv Hprr; eapply prog_sub_change; eauto;try prove_sub_range_sat; fail).
    clear dependent e. clear dependent e1'.
    clear dependent vx.
    (* end of simplification *)
    remember (NCan no) as op.
    assert ({ab : opabs & op = NCan no [+] op = Abs ab})
      as opeq by (exists dum_opabs; left; auto).
    exrepnd; clear Heqop.
    generalize dependent no.
    generalize dependent ab.
    generalize dependent op.
    generalize dependent lbt.
    generalize dependent t'.
    induction k as [| k Hind]; introv H1pr H2pr Hccv Hcv opeq;
    dorn opeq; subst;
    try (applydup (noncan_tricot lib) in H1pr as Htri);
    try (applydup (noncan_tricot_abs lib) in H1pr as Htri);
    dorn Htri; exrepnd;
    try(invertsn Hccv;repnud Htri;exrepnd; rw Hccv in Htri; cpx; fail);[|idtac|idtac|].

    + unfold computes_to_val_like_in_max_k_steps.
      dorn Htri0;[eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|].
      dorn Htri0;[|dorn Htri0; [eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|]].
      * provefalse.
        d_isnoncan Htri0. applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_lsubst in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        apply computes_in_1step_to_alpha in Htri3.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri3; auto.
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_ispmrk in aeq; auto.
          apply noncan_not_ismrk in Htri3; sp.
          destruct aeq; auto. }

        { apply alpha_isabs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_ispmrk in aeq; auto.
          apply isabs_not_ismrk in Htri3; sp.
          destruct aeq; auto. }

      * dorn Htri0;[eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|].
        provefalse.
        d_isabs Htri0.
        applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_lsubst_abs in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        apply computes_in_1step_to_alpha in Htri3.
        apply (computes_in_1step_alpha_r _ _ _ _ _ Hcv) in Htri3; auto.
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct He.
        dorn Htri3;
          [ apply abs_not_mrk in Htri3; cpx; eauto
          | apply noncan_not_mrk in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_ismrk with (t1 := ev); eauto with slow.

    + unfold computes_to_val_like_in_max_k_steps.
      dorn Htri0;[eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|].
      dorn Htri0;[|dorn Htri0; [eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|]].
      * provefalse.
        d_isnoncan Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_lsubst_abs2 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        apply computes_in_1step_to_alpha in Htri3.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri3; auto.
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_abs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_ispmrk in aeq; auto.
          apply isabs_not_ismrk in Htri3; sp.
          destruct aeq; sp. }

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_ispmrk in aeq; auto.
          apply noncan_not_ismrk in Htri3; sp.
          destruct aeq; sp. }

      * dorn Htri0;[eexists; dands; simpl; eauto; unfold isvalue_like; complete auto|].
        provefalse.
        d_isabs Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_lsubst_abs3 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        apply computes_in_1step_to_alpha in Htri3.
        apply (computes_in_1step_alpha_r _ _ _ _ _ Hcv) in Htri3; auto.
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct He.
        dorn Htri3;
          [ apply abs_not_mrk in Htri3; cpx; eauto
          | apply noncan_not_mrk in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_ismrk with (t1 := ev); eauto with slow.

    + dorn Htri0;
      [exists v;
         dands; auto;
         apply no_change_after_val_like2 with (k1:=1);
         auto; [|omega];
         unfolds_base; dands; auto; unfold isvalue_like; complete auto
            | ].
      dorn Htri0;
        [
        | dorn Htri0;
          [ exists v;
              dands; auto;
              apply no_change_after_val_like2 with (k1:=1);
              auto; [|omega];
              unfolds_base; dands; auto; unfold isvalue_like; complete auto
                 |
          ]
        ].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        remember (oterm (NCan no) lbt) as t.
        dorn H2tri0;
          [exists v;
             dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                 |].
        (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        eapply Hind  with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
        exrepnd.
        exists tv. remember (S k) as sk. unfolds_base.
        repnud H2tri3. dands; auto;[].
        rw @reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

        clear Hind. apply Hcc in H2tri; auto.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        apply computes_step_to_error_no_further in H1stepb; auto. cpx.

      * dorn Htri0;
        [exists v;
           dands; auto;
           apply no_change_after_val_like2 with (k1:=1);
           auto; [|omega];
           unfolds_base; dands; auto; unfold isvalue_like; complete auto
              | ].
        d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        remember (oterm (NCan no) lbt) as t.
        dorn H2tri0;
          [exists v;
             dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                 |].
        (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        eapply Hind  with (ab := tabs) (no := NApply) in H2tri1; eauto.
        exrepnd.
        exists tv. remember (S k) as sk. unfolds_base.
        repnud H2tri3. dands; auto;[].
        rw @reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

        clear Hind. apply Hcc in H2tri; auto.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        apply computes_step_to_error_no_further in H1stepb; auto. cpx.

    + dorn Htri0;
      [exists v;
         dands; auto;
         apply no_change_after_val_like2 with (k1:=1);
         auto; [|omega];
         unfolds_base; dands; complete sp
            | ].
      dorn Htri0;
        [
        | dorn Htri0;
          [ exists v;
              dands; auto;
              apply no_change_after_val_like2 with (k1:=1);
              auto; [|omega];
              unfolds_base; dands; complete sp
                 |
          ]
        ].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        remember (oterm (NCan no) lbt) as t.
        dorn H2tri0;
          [exists v;
             dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
              repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
              repeat (unfolds_base; dands; auto); fail
                 |].
        (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        eapply Hind  with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
        exrepnd.
        exists tv. remember (S k) as sk. unfolds_base.
        repnud H2tri3. dands; auto;[].
        rw @reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

        clear Hind. apply Hcc in H2tri; auto.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        apply computes_step_to_error_no_further in H1stepb; auto. cpx.

      * dorn Htri0;
        [exists v;
           dands; auto;
           apply no_change_after_val_like2 with (k1:=1);
           auto; [|omega];
           unfolds_base; dands; complete sp
              | ].
        d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        remember (oterm (NCan no) lbt) as t.
        dorn H2tri0;
          [exists v;
             dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
              repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
              repeat (unfolds_base; dands; auto); fail
                 |].
        (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        eapply Hind  with (ab := tabs) (no := NApply) in H2tri1; eauto.
        exrepnd.
        exists tv. remember (S k) as sk. unfolds_base.
        repnud H2tri3. dands; auto;[].
        rw @reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.

        clear Hind. apply Hcc in H2tri; auto.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ _ Htri1) in H1stepb.
        apply computes_step_to_error_no_further in H1stepb; auto. cpx.
Qed.
 *)

Lemma alphaeq_preserves_is_can_or_exc {p} :
  forall t1 t2,
    @alpha_eq p t1 t2
    -> is_can_or_exc t1
    -> is_can_or_exc t2.
Proof.
  introv aeq ise.
  dorn ise.
  left; eapply alphaeq_preserves_iscan; eauto.
  right; eapply alphaeq_preserves_isexc; eauto.
Qed.

Lemma crary5_7_can_or_exc {o} : forall lib k vx vy e ev no lbt,
let t := @oterm o (NCan no) lbt in
let tl := subst e vx t in
vx <> vy
-> isp_can_or_exc ev
-> computes_in_kstep_alpha lib k tl ev
-> isprogram t
-> isprogram tl
-> {evc : NTerm $ forall t', isprogram t'
      -> computes_in_kstep_alpha lib k (subst e vx t')
                                   (subst evc vx t')
         # isp_can_or_exc (subst evc vx t')}
   [+]
   {tv : NTerm $ computes_to_val_like_in_max_k_steps lib t tv k}.
(* This last line used to be: computes_to_value_in_max_k_steps k t tv *)
Proof.
  induction k as [k Hind] using comp_ind_type; introv Hneq Hval Hck Htpr Htlpt.
  dup Hval as isp.
  destruct isp as [isp isce].
  destruct k;[ invertsn Hck; left; exists e; intros; dands;[constructor|]; eauto 2 with slow |];
  [ apply alpha_eq_sym in Hck;
    apply (alpha_preserves_isp_can_or_exc _ _ Hck) in Hval;
    eapply isp_can_or_exc_change_subst_noncan; eauto; fail|].

  duplicate Hck as Hckb.
  invertsna Hck Hcsk. duplicate Hcsk as H1csk. apply @crary5_7_alpha with (vy:=vy) in Hcsk; auto.

  applydup @computes_in_1step_alpha_program in H1csk as ispt2; auto;[].

  dorn Hcsk;[| right].

  - exrepnd. dimp (Hcsk1 (oterm (NCan no) lbt)).
    eapply computes_in_1step_alpha_r in hyp; try (exact H1csk); eauto 3 with slow;[].
    eapply computes_in_kstep_fun_l in Hcsk0; try (exact hyp); eauto 3 with slow;[].
    apply Hind with (vy:=vy) in Hcsk0; auto;
    [|
        eapply computes_in_1step_alpha_program in H1csk; eauto;
        apply (alphaeq_preserves_program _ _ hyp) in H1csk;
        eapply prog_sub_change; eauto;try prove_sub_range_sat].
    rename Hcsk0 into Xind.
    remember (oterm (NCan no) lbt) as t.
    dorn Xind;[left| right];
    [exrepnd; exists evc; introv Hpt'; dimp (Xind0 t'); repnd;
       dands; spc; econstructor; eauto; fail|].
    exrepnd. exists tv; auto. dands; auto. repnud Xind0.
    apply no_change_after_val_like2 with (k1:=k); auto. unfolds_base. dands; auto.
    apply reduces_atmost_preserves_program in Xind1; auto.

  - exrepnd. clear Hind. clear H1csk Hcsk0.
    rename Hcsk1 into Hale.
    (* simplify to accumulate the context and only keep vy *)
    apply lsubst_alpha_congr2 with (sub:=[(vx, (oterm (NCan no) lbt))]) in Hale.
    allunfold @subst.
    match type of Hale with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
    simpl in YY.
    assert (prog_sub [(vx, oterm (NCan no) lbt)]) as Hpr by (prove_sub_range_sat; auto).
    rw (lsubst_lsubst_aux_prog_sub (@vterm o vx)) in YY; auto.
    simpl in YY. autorewrite with slow in YY.
    match type of YY with
    context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
    end.
    rewrite lsubst_app_swap in YY; simpl; auto; try (prove_sub_range_sat;auto);
      [| introv Hinc; invertsn Hinc; cpx; fail].
    simpl in YY.
    specialize (Hcsk2 (oterm (NCan no) lbt)).
    pose proof (fun td tdc => Hcsk2 td tdc Htpr) as Hcc. clear Hcsk2.
    clear Hale.
    apply alpha_eq_sym in YY. rw <- @simple_lsubst_cons2 in YY;[| (prove_sub_range_sat; auto; fail)].
    unfold subst in YY. remember (lsubst e1' [(vx, oterm (NCan no) lbt)]) as exc.
    assert ( forall td tdc : NTerm,
      isprogram td ->
      (computes_in_1step lib td tdc ->
      computes_in_1step_alpha lib (lsubst exc [(vy, td)])
        (lsubst exc [(vy, tdc)]))
     # (computes_step_to_error lib td ->
         computes_step_to_error lib (lsubst exc [ (vy, td)]))
      ) as Hccb by
      (introv Hptd; dands; introv  Hcsd; applydup Hcc in Hcsd; auto;
      repeat(rw <- (simple_lsubst_cons2 e1') in Hcsd0;[| (prove_sub_range_sat; auto; eauto with slow; fail)]);
      allunfold @subst; subst; auto).
    clear Hcc. rename Hccb into Hcc.
    apply alpha_eq_sym in YY.
    eapply computes_in_kstep_fun_l in Hckb; try (exact YY); eauto 3 with slow;[].
    eapply alphaeq_preserves_program in Htlpt; try (apply alpha_eq_sym; exact YY); eauto 3 with slow;[].
    assert (forall tt, isprogram tt -> isprogram (lsubst exc [(vy, tt)])) as Hapr by
      (introv Hprr; eapply prog_sub_change; eauto;try prove_sub_range_sat; fail).
    clear dependent e. clear dependent e1'.
    clear dependent vx.
    (* end of simplification *)
    remember (NCan no) as op.
    assert ({ab : opabs & op = NCan no [+] op = Abs ab})
      as opeq by (exists dum_opabs; left; auto).
    exrepnd; clear Heqop.
    generalize dependent no.
    generalize dependent ab.
    generalize dependent op.
    generalize dependent lbt.
    generalize dependent t'.
    induction k as [| k Hind]; introv H1pr Hccv Hcv H2pr opeq;
    dorn opeq; subst;
    try (applydup (noncan_tricot lib) in H1pr as Htri);
    try (applydup (noncan_tricot_abs lib) in H1pr as Htri);
    dorn Htri; exrepnd;
    try(invertsn Hccv;repnud Htri;exrepnd; rw Hccv in Htri; cpx; fail);[|idtac|idtac|].

    + unfold computes_to_val_like_in_max_k_steps.

      repndors; try (complete (eexists; dands; simpl; eauto 3 with slow; sp));[|].

      * d_isnoncan Htri0. applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; auto.
          apply noncan_not_is_can_or_exc in Htri3; sp. }

        { apply alpha_isabs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; auto.
          apply isabs_not_is_can_or_exc in Htri3; sp. }

      * d_isabs Htri0.
        applydup @c1step_nc in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct Hval.
        dorn Htri3;
          [ apply abs_not_can_or_exc in Htri3; cpx; eauto
          | apply noncan_not_can_or_exc in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_is_can_or_exc with (t1 := ev); eauto with slow.

    + unfold computes_to_val_like_in_max_k_steps.

      repndors; try (complete (eexists; dands; simpl; eauto 3 with slow; sp));[|].

      * d_isnoncan Htri0. applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs2 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd as aeq.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow;[].
        apply alpha_eq_sym in Htri3.

        dorn Htri4.

        { apply alpha_isabs in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; auto.
          apply isabs_not_is_can_or_exc in Htri3; sp. }

        { apply alpha_noncan in Htri3; auto.
          apply alpha_eq_sym in aeq.
          apply alphaeq_preserves_is_can_or_exc in aeq; auto.
          apply noncan_not_is_can_or_exc in Htri3; sp. }

      * d_isabs Htri0.
        applydup @c1step_ab in Htri1.
        apply Hcc in Htri3; auto.
        applydup @computes_in_1step_alpha_lsubst_abs3 in Htri3; auto.
        inverts Hcv as Hcv Hdd. inverts Hdd.
        eapply computes_in_1step_alpha_r in Htri3; try (exact Hcv); eauto 3 with slow.
        apply alpha_eq_sym in Htri3.
        apply alpha_isabs_isnoncan in Htri3; auto.
        destruct Hval.
        dorn Htri3;
          [ apply abs_not_can_or_exc in Htri3; cpx; eauto
          | apply noncan_not_can_or_exc in Htri3; cpx; eauto
          ];
          apply alphaeq_preserves_is_can_or_exc with (t1 := ev); eauto with slow.

    + repndors;
      try (complete (exists v; dands; auto;
                            apply no_change_after_val_like2 with (k1:=1);
                            auto; [|omega];
                            unfolds_base; dands; eauto 3 with slow; sp));[|].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
               unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_nc in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
             dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             unfolds_base; dands; auto; simpl; unfolds_base; simpl; tcsp; rw H1step; auto; fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

    + repndors;
      try (complete (exists v; dands; auto;
                            apply no_change_after_val_like2 with (k1:=1);
                            auto; [|omega];
                            unfolds_base; dands; eauto 3 with slow; sp));[|].

      * d_isnoncan Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
             apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
             repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
             repeat (unfolds_base; dands; auto); fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_nc in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := dum_opabs) (no := vnc) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }

      * d_isabs Htri0. duplicate Htri1 as H1step.
        apply c1step_ab in Htri1. apply Hcc in Htri1; auto.
        applydup (noncan_tricot_abs lib) in Htri2 as H2tri.
        dorn H2tri; exrepnd.

        { remember (oterm (NCan no) lbt) as t.
          dorn H2tri0;
            [exists v;
               dands; auto;
               apply no_change_after_val_like2 with (k1:=2); auto;[| omega];
               repeat (rw @computes_to_val_like_in_max_k_steps_S; eexists; dands; eauto);
               repeat (unfolds_base; dands; auto); fail
                   |].
          (* get ready to apply the induction hyp *) apply c1step_ab in H2tri1.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          eapply Hind with (ab := tabs) (no := NApply) in H2tri1; eauto.
          exrepnd.
          exists tv. remember (S k) as sk. unfolds_base.
          repnud H2tri3. dands; auto;[].
          rw @reduces_in_atmost_k_steps_S.
          eexists; dands; eauto. }

        { clear Hind. apply Hcc in H2tri; auto.
          inverts Hcv as Hcv H1stepb.

          applydup@ computes_in_1step_alpha_program in Hcv; auto;[].

          eapply computes_in_1step_alpha_r in Htri1; try (exact Hcv); eauto 3 with slow;[].
          eapply computes_in_kstep_fun_l in H1stepb; try (exact Htri1); eauto 3 with slow;[].
          apply computes_step_to_error_no_further in H1stepb; auto. cpx. }
Qed.

Lemma crary5_7_value_aux {o} :
  forall lib k vx e ev no lbt,
    let t := @oterm o (NCan no) lbt in
    let tl := subst e vx t in
    isvalue ev
    -> computes_in_kstep_alpha lib k tl ev
    -> isprogram t
    -> isprogram tl
    -> {evc : NTerm
         $ forall t',
             isprogram t'
             -> computes_in_kstep_alpha lib k (subst e vx t') (subst evc vx t')
                # isvalue (subst evc vx t')}
       [+]
       {tv , e' : NTerm
         $ {k1 : nat
             $ k1 <= k
             # computes_to_val_or_exc_in_max_k_steps lib t tv k1
             # computes_in_kstep_alpha lib k1 tl (subst e' vx tv)
             # forall t',
                 isprogram t'
                 -> reduces_to lib t' tv
                 -> {k' : nat $ computes_in_kstep_alpha lib k' (subst e vx t') (subst e' vx tv)}}}.
(* This last line used to be: computes_to_value_in_max_k_steps k t tv *)
Proof.
  induction k as [k Hind] using comp_ind_type; introv Hval Hck Htpr Htlpt.
  destruct k;[ invertsn Hck; left; exists e; intros; dands;[constructor|]; eauto 2 with slow |];
  [ apply alpha_eq_sym in Hck; apply (alpha_preserves_value _ _ Hck) in Hval;
    eapply isvalue_change_subst_noncan; eauto; fail |].

  duplicate Hck as Hckb.
  invertsna Hck Hcsk.
  duplicate Hcsk as H1csk.

  pose proof (fresh_var_not_in [vx]) as Hneq.
  remember (fresh_var [vx]) as vy; clear Heqvy.
  rw in_single_iff in Hneq.

  apply @crary5_7_alpha with (vy:=vy) in Hcsk; auto.

  dorn Hcsk;[| right].

  - exrepnd. dimp (Hcsk1 (oterm (NCan no) lbt)).
    (*
    apply (computes_in_1step_alpha_r _ _ _ _ _ H1csk) in hyp; auto.
    apply (computes_in_kstep_fun_l _ _ _ _ _ hyp) in Hcsk0.
    apply Hind in Hcsk0; auto;
    [|
        eapply computes_in_1step_alpha_program in H1csk; eauto;
        apply (alphaeq_preserves_program _ _ hyp) in H1csk;
        eapply prog_sub_change; eauto;try prove_sub_range_sat].
    rename Hcsk0 into Xind.
    remember (oterm (NCan no) lbt) as t.
    dorn Xind;[left| right];
    [exrepnd; exists evc; introv Hpt'; dimp (Xind0 t'); repnd;
       dands; spc; econstructor; eauto; fail|].
    exrepnd.
    applydup @computes_to_val_or_exc_in_max_k_steps_preserves_program in Xind2; auto.
    exists tv e' (S k1); auto.
    dands; auto; try omega.

    + apply @no_change_after_val_or_exc2 with (k1:=k1); auto.

    + apply @ckacons with (t2 := subst e2' vx t); auto.

    + introv isp r.
      apply Xind0 in r; exrepnd; auto.
      exists (S k').
      apply @ckacons with (t2 := subst e2' vx t'); auto.

  - exrepnd.
    generalize (Hcsk2 (oterm (NCan no) lbt) (oterm (NCan no) lbt) t'
                      Htpr Htpr);
      intro h; destruct h as [h h']; clear h'; autodimp h hyp.
*)
Abort.
(*
    clear H1csk Hcsk0.
    rename Hcsk1 into Hale.
    (* simplify to accumulate the context and only keep vy *)
    apply lsubst_alpha_congr2 with (sub:=[(vx, (oterm (NCan no) lbt))]) in Hale.
    allunfold @subst.
    match type of Hale with
      alpha_eq ?l (lsubst (lsubst ?t ?subin) ?subout) =>
        pose proof (combine_sub_nest t subin subout) as YY;
        apply alpha_eq_trans with (nt1:=l )in YY; auto
      end.
    simpl in YY.
    assert (prog_sub [(vx, oterm (NCan no) lbt)]) as Hpr by (prove_sub_range_sat; auto).
    rw (lsubst_lsubst_aux_prog_sub (vterm vx)) in YY; auto.
    simpl in YY. autorewrite with slow in YY.
    match type of YY with
    context[[?s1,?s2]] => rewrite (cons_as_app _ s1 [s2]) in YY
    end.
    rewrite lsubst_app_swap in YY; simpl; auto; try (prove_sub_range_sat;auto);
      [| introv Hinc; invertsn Hinc; cpx; fail].
    simpl in YY.
    specialize (Hcsk2 (oterm (NCan no) lbt)).
    pose proof (fun td tdc => Hcsk2 td tdc Htpr) as Hcc. clear Hcsk2.
    clear Hale.
    apply alpha_eq_sym in YY. rw <- @simple_lsubst_cons2 in YY;[| (prove_sub_range_sat; auto; fail)].
    unfold @subst in YY. remember (lsubst e1' [(vx, oterm (NCan no) lbt)]) as exc.
    assert ( forall td tdc : NTerm,
      isprogram td ->
      (computes_in_1step td tdc ->
      computes_in_1step (lsubst exc [(vy, td)])
        (lsubst exc [(vy, tdc)]))
     # (computes_step_to_error td ->
         computes_step_to_error (lsubst exc [ (vy, td)]))
      ) as Hccb by
      (introv Hptd; dands; introv  Hcsd; applydup Hcc in Hcsd; auto;
      repeat(rw <- (simple_lsubst_cons2 e1') in Hcsd0;[| (prove_sub_range_sat; auto; eauto with slow; fail)]);
      allunfold @subst; subst; auto).
    clear Hcc. rename Hccb into Hcc.
    apply alpha_eq_sym in YY.
    apply (computes_in_kstep_fun_l _ _ _ _ YY) in Hckb.
    apply (alphaeq_preserves_program _ _ YY) in Htlpt.
    assert (forall tt, isprogram tt -> isprogram (lsubst exc [(vy, tt)])) as Hapr by
      (introv Hprr; eapply prog_sub_change; eauto;try prove_sub_range_sat; fail).
(*    clear dependent e.
    clear dependent e1'.
    clear dependent vx.*)
    (* end of simplification *)
    generalize dependent no.
    generalize dependent lbt. generalize dependent t'.
    induction k as [| k Hind]; introv H1pr H2pr Hccv Hcv;
    applydup noncan_tricot in H1pr as Htri;
    dorn Htri; exrepnd;
    try(invertsn Hccv;repnud Htri;exrepnd; rw Hccv in Htri; cpx; fail);[|].
    + unfold @computes_to_val_or_exc_in_max_k_steps.
      dorn Htri0;[eexists; dands; simpl; eauto; fail|].
      dorn Htri0;[|eexists; dands; simpl; eauto; fail].
      d_isnoncan Htri0. applydup c1step in Htri1.
      apply Hcc in Htri3; auto.
      applydup computes_in_1step_lsubst in Htri3; auto.
      inverts Hcv as Hcv Hdd. inverts Hdd.
      apply computes_in_1step_to_alpha in Htri3.
      apply (computes_in_1step_alpha_r  _ _ _ _ Hcv) in Htri3; auto.
      apply alpha_eq_sym in Htri3. apply alpha_noncan in Htri3; auto.
      apply noncan_not_value in Htri3; cpx; eauto with slow.
    + dorn Htri0;
      [exists v;
         dands; auto;
         apply no_change_after_val_or_exc2 with (k1:=1);
         auto; [|omega];
         unfolds_base; dands; auto; fail
            | ].
      dorn Htri0;
        [|exists v;
           dands; auto;
           apply no_change_after_val_or_exc2 with (k1:=1);
           auto; [|omega];
           unfolds_base; dands; auto; fail].
      d_isnoncan Htri0. duplicate Htri1 as H1step.
      apply c1step in Htri1. apply Hcc in Htri1; auto.
      applydup noncan_tricot in Htri2 as H2tri.
      dorn H2tri; exrepnd.
      * remember (oterm (NCan no) lbt) as t.
        dorn H2tri0;
          [exists v;
             dands; auto;
             apply no_change_after_val_or_exc2 with (k1:=2); auto;[| omega];
             unfolds_base; dands; auto; simpl; unfolds_base; simpl; rw H1step; auto; fail
                 |].
        (* get ready to apply the induction hyp *) apply c1step in H2tri1.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ Htri1) in H1stepb.
        apply Hind in H2tri1; auto.
        exrepnd.
        exists tv. remember (S k) as sk. unfolds_base.
        repnud H2tri3. dands; auto;[].
        rw reduces_in_atmost_k_steps_S.
        eexists; dands; eauto.
      * clear Hind. apply Hcc in H2tri; auto.
        inverts Hcv as Hcv H1stepb. apply computes_in_1step_to_alpha in Htri1.
        apply (computes_in_1step_alpha_r  _ _ _ _ Hcv) in Htri1; auto.
        apply (computes_in_kstep_fun_l _ _ _ _ Htri1) in H1stepb.
        apply computes_step_to_error_no_further in H1stepb; auto. cpx.
Qed.
*)

Lemma computes_in_kstep_alpha_value {o} :
  forall lib (e ev : @NTerm o),
  computes_to_value lib e ev
  -> {k : nat $ computes_in_kstep_alpha lib k e ev # isvalue ev}.
Proof.
  introv Hcv.
  repnud Hcv.
  repnud Hcv0.
  exrepnd.
  generalize dependent e.
  generalize dependent k.
  induction k; introv Hck.
  - exists 0. invertsn Hck. dands; auto. constructor. auto.
  - rw @reduces_in_atmost_k_steps_S in Hck; exrepnd.
    apply IHk in Hck0.
    exrepnd.
    symmetry in Hck1; apply compute_step_dicot in Hck1.
    dorn Hck1; exrepnd; subst;[exists k0 | exists (S k0)]; dands; auto.
    dands; eauto.
    econstructor; eauto.
    econstructor; dands; eauto.
Qed.

Lemma computes_in_kstep_alpha_exc {o} :
  forall lib a (e ev : @NTerm o),
  computes_to_exception lib a e ev
  -> {k : nat $ computes_in_kstep_alpha lib k e (mk_exception a ev)}.
Proof.
  introv Hcv.
  repnud Hcv.
  repnud Hcv; exrepnd.
  generalize dependent e.
  generalize dependent k.
  induction k; introv Hck.
  - exists 0. invertsn Hck. dands; auto. constructor. auto.
  - rw @reduces_in_atmost_k_steps_S in Hck; exrepnd.
    apply IHk in Hck0.
    exrepnd.
    symmetry in Hck1; apply compute_step_dicot in Hck1.
    dorn Hck1; exrepnd; subst;[exists k0 | exists (S k0)]; dands; auto.
    dands; eauto.
    econstructor; eauto.
    econstructor; dands; eauto.
Qed.


(* end hide *)

(** %\noindent% Since we have a constructive meta-theory here
    and Nuprl's language is turing complete, there is no way to
    determine if [f] computes to a value. So, unlike a classical
    logician, we cannot separately handle the cases when it
    converges to a value and the one where it doesn't.
    However, we have a weaker dichotomy that is sufficient
    for both the proofs (of Compactness and LUB theorems).
    Near the beginning of both these proofs,
    we will have a hypothesis of the form
    [computes_to_value  (apply_bterm bt [(mk_fix f)]) v]
    (recall the definitions of [approx] and [close_comput]).

    By using lemma 5.7 at each step of this computation, we can determine if
    the [f] was ever evaluated in this computation (second case of lemma 5.7).
    Our strengthening of 5.7
    lets us prove that if  [f] was evaluated even for 1 step in the above
    computation, it must have been evaluated to a value in
    order for the computation of the overall term to converge to value.
    This case corresponds to the first case in the disjunction in the 
    conclusion of the
    lemma [fix_value2] below.

    However, if the first case of lemma 5.7 holds for all these 
    steps of computation,
    then [(mk_fix f)] can be replaced with anything and we will
    still get the same behaviour. The predicate [dummy_context]
    below formalizes this property.
    [computes_to_alpha_value a b] asserts that
    [a] converges to a value that is alpha equal to [b].
*)

Definition dummy_context {o} lib (v : NVar) (e : @NTerm o) :=
  let bt := bterm [v] e in
     {vc : NTerm $ let btv := bterm [v] vc in
          forall t, isprogram t->
             computes_to_alpha_value lib
                (apply_bterm bt [t])
                (apply_bterm btv [t])}.

Lemma fix_value2 {o} : forall lib f v e, let bt := bterm [nvarx] e in
  @isprogram o f
  -> isprogram (apply_bterm bt [(mk_fix f)])
  -> computes_to_value lib (apply_bterm bt [(mk_fix f)]) v
  -> hasvalue lib f
     [+] raises_exception lib f
     [+] dummy_context lib nvarx e.
Proof.
  simpl. introv Hprf Hpa Hcv.
  apply computes_in_kstep_alpha_value in Hcv.
  exrepnd.
  unfold apply_bterm in Hcv1.
  simpl in Hcv1.
  apply crary5_7_value with (vy:=nvary) in Hcv1; auto; eauto 2 with slow;
  [| repeat (decomp_progc); auto].

  repndors; exrepnd.

  - right; right; unfolds_base.
    exists evc.
    introv Hpr.
    applydup Hcv2 in Hpr; repnd.
    allunfold @apply_bterm. allunfold @subst.
    allsimpl.

    eapply computes_in_kstep_alpha2; eauto.

    apply isprogram_implies_nt_wf in Hpa.
    allrw @nt_wf_lsubst_iff; repnd; dands; auto.
    introv i j; allsimpl; boolvar; ginv.
    pose proof (Hpa nvarx (mk_fix f)) as h; repeat (autodimp h hyp); eauto 3 with slow.

  - exrepnd.
    destruct k.

    + left; destruct Hcv2 as [c i].
      apply reduces_in_atmost_k_steps_0 in c; subst.
      dorn i; inversion i.

    + rename Hcv2 into Hcs.
      apply compute_decompose_aux in Hcs; [| repeat (decomp_progc); auto].
      repndors; exrepnd; ginv.
      applydup @reduces_atmost_preserves_program in Hcs3; auto.
      dorn Hcs1.
      * left; apply reduces_in_atmost_k_steps_implies_hasvalue in Hcs3; auto.
      * right; left; apply reduces_in_atmost_k_steps_implies_raises_exception in Hcs3; auto.
Qed.

(* !!MOVE to terms2. *)
Lemma ispexc_nexception {p} :
  forall a (e : @NTerm p),
    isprogram a
    -> isprogram e
    -> ispexc (mk_exception a e).
Proof.
  introv ispa ispe.
  split.
  constructor.
  apply isprogram_exception; auto.
Qed.
Hint Resolve ispexc_nexception : slow.

(*
(* !!MOVE to terms2. *)
Lemma ispnexc_nexception {p} :
  forall a (e : @NTerm p), isprogram e -> ispnexc a (mk_nexception a e).
Proof.
  introv isp.
  unfold ispnexc; simpl; boolvar; tcsp; dands; auto.
  apply isprogram_nexception; auto.
Qed.
Hint Resolve ispnexc_nexception : slow.

(* !!MOVE to substitution. *)
Lemma lsubst_mk_nexception {p} :
  forall a (e : @NTerm p) sub,
    lsubst (mk_nexception a e) sub = mk_nexception a (lsubst e sub).
Proof.
  introv.
  unfold lsubst, mk_exception; simpl.
  allrw app_nil_r.
  allrw @sub_filter_nil_r.
  destruct (dec_disjointv (bound_vars e) (flat_map free_vars (range sub))); auto.
  unfold var_ren; simpl.
  rw @lsubst_aux_nil; auto.
Qed.

(* !!MOVE to substitution. *)
Lemma subst_mk_nexception {p} :
  forall a (e : @NTerm p) v t,
    subst (mk_nexception a e) v t = mk_nexception a (subst e v t).
Proof.
  introv.
  unfold subst.
  apply lsubst_mk_nexception.
Qed.

Lemma ispnexc_subst_ax_implies_exc {p} :
  forall a (t : @NTerm p) x,
    ispnexc a (subst t x mk_axiom)
    -> {e : @NTerm p & t = mk_nexception a e}.
Proof.
  introv.
  unfold subst.
  change_to_lsubst_aux4; simpl; auto.
  destruct t.
  - simpl; boolvar; intro k;
    destruct k as [ise isp]; inversion ise.
  - destruct o; simpl; intro k;
    destruct k as [ise isp]; try (complete (inversion ise)).
    apply isprogram_exception_implies in isp; exrepnd.
    repeat (destruct l; cpx).
    repeat (destruct b; cpx).
    repeat (destruct l; allsimpl; cpx).
    boolvar; subst; tcsp.
    exists n; sp.
Qed.

Definition raises_nexception {p} lib a (t : @NTerm p) :=
  {e : NTerm & computes_to_exception lib a t e}.
 *)

Lemma computes_in_kstep_fun_r {o} :
  forall lib (k : nat) (t1 t2 t3 : @NTerm o),
    alpha_eq t2 t3
    -> computes_in_kstep_alpha lib k t1 t2
    -> computes_in_kstep_alpha lib k t1 t3.
Proof.
  induction k; introv aeq comp.
  - inversion comp as [? ? ? aeq'|]; subst; clear comp.
    constructor; eauto with slow.
  - inversion comp as [|? ? ? ? ? comp1 comp2]; subst; clear comp.
    eapply IHk in comp2;[|eauto].
    econstructor; eauto.
Qed.

Definition dummy_context_exc {o} lib (v : NVar) (e : @NTerm o) :=
  let bt := bterm [v] e in
  {a : NTerm & {vc : NTerm
   & let btv := bterm [v] vc in
     let ba  := bterm [v] a in
     forall t,
       isprogram t
       -> computes_to_alpha_exception
            lib
            (apply_bterm ba [t])
            (apply_bterm bt [t])
            (apply_bterm btv [t])}}.

Lemma fix_value2_exc {o} : forall lib a f v  e, let bt := bterm [nvarx] e in
  @isprogram o f
  -> isprogram (apply_bterm bt [(mk_fix f)])
  -> computes_to_exception lib a (apply_bterm bt [(mk_fix f)]) v
  -> hasvalue lib f
     [+] raises_exception lib f
     [+] dummy_context_exc lib nvarx e.
Proof.
  simpl. introv Hprf Hpa Hcv.
  apply computes_in_kstep_alpha_exc in Hcv.
  exrepnd.
  unfold apply_bterm in Hcv0.
  simpl in Hcv0.
  applydup @computes_in_kstep_alpha_preserves_isprogram in Hcv0; auto.
  rw @isprogram_exception_iff in Hcv1; repnd.
  dup Hcv0 as comp.
  apply (crary5_7_exc _ _ _ nvary) in Hcv0; auto; eauto 3 with slow;
  [| repeat (decomp_progc); auto].

  repndors.

  - right; right; unfolds_base. exrepnd.
    generalize (Hcv3 mk_axiom); intro h; autodimp h hyp;
    destruct h as [h' h]; clear h'.
    apply ispexc_subst_ax_implies_exc in h; exrepnd; subst.
    exists a0 e0.
    introv Hpr.
    applydup Hcv3 in Hpr; repnd.
    pose proof (alpha_eq_mk_exception_lsubst a0 e0 [(nvarx,t)]) as aeq.
    allunfold @apply_bterm; allunfold @subst; allsimpl.
    eapply computes_in_kstep_fun_r in Hpr1;[|exact aeq].
    eapply computes_in_kstep_alpha_implies_exc; eauto.

    apply isprogram_implies_nt_wf in Hpa.
    allrw @nt_wf_lsubst_iff; repnd; dands; auto.
    introv i j; allsimpl; boolvar; ginv.
    pose proof (Hpa nvarx (mk_fix f)) as h; repeat (autodimp h hyp); eauto 3 with slow.

  - exrepnd.
    destruct k.

    + left; destruct Hcv3 as [c i].
      apply reduces_in_atmost_k_steps_0 in c; subst.
      dorn i; inversion i.

    + rename Hcv3 into Hcs.
      apply compute_decompose_aux in Hcs; [| repeat (decomp_progc); auto].
      repndors; exrepnd; ginv.
      invertsn Hcs3.
      applydup @reduces_atmost_preserves_program in Hcs3; auto.
      dorn Hcs1.
      * left; apply reduces_in_atmost_k_steps_implies_hasvalue in Hcs3; auto.
      * right; left.
        apply reduces_in_atmost_k_steps_implies_raises_exception in Hcs3; auto.
Qed.

(*
Lemma computes_in_kstep_alpha_mrk {o} :
  forall lib (e : @NTerm o) m,
  computes_to_marker lib e m
  -> {k : nat $ computes_in_kstep_alpha lib k e (mk_marker m)}.
Proof.
  introv Hcv.
  repnud Hcv.
  repnud Hcv; exrepnd.
  generalize dependent e.
  generalize dependent k.
  induction k; introv Hck.
  - exists 0. invertsn Hck. dands; auto. constructor. auto.
  - rw @reduces_in_atmost_k_steps_S in Hck; exrepnd.
    apply IHk in Hck0.
    exrepnd.
    symmetry in Hck1; apply compute_step_dicot in Hck1.
    dorn Hck1; exrepnd; subst;[exists k0 | exists (S k0)]; dands; auto.
    dands; eauto.
    econstructor; eauto.
    econstructor; dands; eauto.
Qed.

Definition dummy_context_mrk {o} lib (v : NVar) (e : @NTerm o) :=
  let bt := bterm [v] e in
  {m : marker
   $ forall t,
       isprogram t
       -> computes_to_marker lib (apply_bterm bt [t]) m}.

Lemma fix_value2_mrk {o} :
  forall lib f v e,
    let bt := bterm [nvarx] e in
    @isprogram o f
    -> isprogram (apply_bterm bt [(mk_fix f)])
    -> computes_to_marker lib (apply_bterm bt [(mk_fix f)]) v
    -> hasvalue lib f
       [+] raises_exception lib f
       [+] dummy_context_mrk lib nvarx e.
Proof.
  simpl. introv Hprf Hpa Hcv.
  apply computes_in_kstep_alpha_mrk in Hcv.
  exrepnd.
  unfold apply_bterm in Hcv0.
  simpl in Hcv0.
  applydup @computes_in_kstep_alpha_preserves_isprogram in Hcv0; auto.
  applydup @isprogram_exception_iff in Hcv1.
  apply crary5_7_mrk with (vy:=nvary) in Hcv0; auto; eauto 2 with slow;
  [| repeat (decomp_progc); auto].
  dorn Hcv0.

  - right; right; unfolds_base. exrepnd.
    generalize (Hcv3 mk_axiom); intro h; autodimp h hyp;
    destruct h as [h' h]; clear h'.
    apply ispmrk_subst_ax_implies_mrk in h; exrepnd; subst.
    exists m.
    introv Hpr.
    apply Hcv3 in Hpr; repnd.
    allrw @subst_mk_marker.
    repnd. allunfold @apply_bterm. allunfold @subst.
    allsimpl.
    eapply computes_in_kstep_alpha_implies_mrk; eauto.

  - exrepnd.
    destruct k.

    + left; destruct Hcv3 as [c i].
      apply reduces_in_atmost_k_steps_0 in c; subst.
      dorn i;[|dorn i]; inversion i.

    + rename Hcv3 into Hcs.
      apply compute_decompose_aux in Hcs; [| repeat (decomp_progc); auto].
      exrepnd.
      invertsn Hcs2.
      applydup @reduces_atmost_preserves_program in Hcs3; auto.
      dorn Hcs1.
      * left; apply reduces_in_atmost_k_steps_implies_hasvalue in Hcs3; auto.
      * right; left; apply reduces_in_atmost_k_steps_implies_raises_exception in Hcs3; auto.
Qed.
*)

(** %\noindent% The following lemma gives us something like Crary's 5.8
    (with [j]=0) when the second case of [fix_value2] above holds.
 *)

Lemma dummy_context_crary_5_8_aux {o} : forall lib (f e1 e2 : @NTerm o),
  let bt1:= bterm [nvarx] e1 in
  dummy_context lib nvarx e1
  -> isprogram f
  -> isprogram_bt bt1
  -> computes_to_value lib (apply_bterm bt1 [(mk_fix f)]) e2
  ->  {e2' : NTerm  $
              let bt2 := (bterm [nvarx] e2') in
                 alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
                 # forall k, approx lib (apply_bterm bt2 [(fix_approx k f)])
                                         (apply_bterm bt1 [(fix_approx k f)])
                                      }.
Proof.
  introv Hdum Hp Hpb Hcv. repnud Hdum. exrepnd.
  exists vc. simpl. dands.
  - dimp (Hdum0 (mk_fix f));[eauto with slow; fail |]. invertsn hyp.
    repnd. allunfold @apply_bterm. allunfold @subst.
    allsimpl. apply (computes_to_value_eq _ _ _ _ Hcv) in hyp0. subst. auto.
  - dands; auto. intros.
    dimp (Hdum0 (fix_approx k f));[ eauto 2 with slow |].
    invertsn hyp.
    repnd.
    invertsna hyp0 Hcc.
    unfold apply_bterm.
    simpl. allunfold @subst.
    apply (approx_alpha_rw_l _ _ _ _ hyp).
    apply reduces_to_implies_approx_eauto;
    [fold_applybt;apply @isprogram_bt_implies; spc; 
        try(in_reasoning); subst; spc; eauto 2 with slow|].
    allunfold @apply_bterm. allsimpl. auto.
Qed.

Corollary dummy_context_crary_5_8 {o} : forall lib (f e1 e2 : @NTerm o),
let bt1:= bterm [nvarx] e1 in 
dummy_context lib nvarx e1
-> isprogram f 
-> isprogram_bt bt1
-> computes_to_value lib (apply_bterm bt1 [(mk_fix f)]) e2
->  {e2' : NTerm  $ disjoint (bound_vars e2') [nvarx]
        # let bt2 := (bterm [nvarx] e2') in 
           alpha_eq e2 (apply_bterm bt2 [(mk_fix f)])
           # {j : nat $ forall k,
                   k >= j
                   -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                             (apply_bterm bt1 [(fix_approx (k) f)])
                          }}.
Proof.
  introns XX.
  apply dummy_context_crary_5_8_aux in XX2; auto.
  exrepnd.
  allsimpl.
  pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
  exrepnd.
  rename ntcv into e2a.
  exists e2a.
  apply disjoint_sym in Hfr1.
  dands; auto.
  - alpharw XX2. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
  - exists 0. introv Hgt. clear Hgt.
    simpl. arithsimpl. allunfold @apply_bterm. allsimpl.
    apply lsubst_alpha_congr2 with (sub:=[(nvarx, fix_approx k f)]) in Hfr0.
    apply (approx_alpha_rw_l_aux _ _ _ _ Hfr0).
    auto.
Qed.


Lemma dummy_context_crary_5_8_aux_exc {o} :
  forall lib a (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    dummy_context_exc lib nvarx e1
    -> isprogram f
    -> isprogram_bt bt1
    -> computes_to_exception lib a (apply_bterm bt1 [(mk_fix f)]) e2
    -> {e2' : NTerm
          $ let bt2 := (bterm [nvarx] e2') in
            alpha_eq (mk_exception a e2) (apply_bterm bt2 [(mk_fix f)])
            # forall k, approx lib (apply_bterm bt2 [(fix_approx k f)])
                               (apply_bterm bt1 [(fix_approx k f)])
       }.
Proof.
  introv Hdum Hp Hpb Hcv.
  repnud Hdum.
  exrepnd.
  exists (mk_exception a0 vc).
  simpl. dands.
  - dimp (Hdum1 (mk_fix f));[eauto with slow; fail |]. invertsn hyp.
    exrepnd. allunfold @apply_bterm; allsimpl.
    apply (computes_to_exception_eq _ _ _ _ _ _ Hcv) in hyp1; repnd; subst.
    eapply alpha_eq_trans;[|apply alpha_eq_sym; apply alpha_eq_mk_exception_lsubst].
    apply implies_alphaeq_exception; auto.
  - dands; auto. intros.
    dimp (Hdum1 (fix_approx k f));[ eauto 2 with slow |].
    invertsn hyp.
    exrepnd.
    invertsna hyp1 Hcc.
    unfold apply_bterm.
    allunfold @subst; allunfold @apply_bterm; allsimpl.
    eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym; apply alpha_eq_mk_exception_lsubst|].
    eapply approx_alpha_rw_l_aux;[apply implies_alphaeq_exception;[exact hyp2|exact hyp0] |].
    apply reduces_to_implies_approx_eauto;
    [fold_applybt;apply @isprogram_bt_implies; spc;
        try(in_reasoning); subst; spc; eauto 2 with slow|].
    allunfold @apply_bterm. allsimpl. auto.
    exists x0; auto.
Qed.

Corollary dummy_context_crary_5_8_exc {o} :
  forall lib a (f e1 e2 : @NTerm o),
    let bt1:= bterm [nvarx] e1 in
    dummy_context_exc lib nvarx e1
    -> isprogram f
    -> isprogram_bt bt1
    -> computes_to_exception lib a (apply_bterm bt1 [(mk_fix f)]) e2
    -> {e2' : NTerm
         $ disjoint (bound_vars e2') [nvarx]
         # let bt2 := (bterm [nvarx] e2') in
           alpha_eq (mk_exception a e2) (apply_bterm bt2 [(mk_fix f)])
           # {j : nat
               $ forall k,
                   k >= j
                   -> approx lib (apply_bterm bt2 [(fix_approx (k-j) f)])
                             (apply_bterm bt1 [(fix_approx (k) f)])
       }}.
Proof.
  introns XX.
  apply dummy_context_crary_5_8_aux_exc in XX2; auto.
  exrepnd.
  allsimpl.
  pose proof (change_bvars_alpha_wspec [nvarx] e2') as Hfr.
  exrepnd.
  rename ntcv into e2a.
  exists e2a.
  apply disjoint_sym in Hfr1.
  dands; auto.
  - alpharw XX2. unfold apply_bterm. simpl. apply lsubst_alpha_congr2; auto.
  - exists 0. introv Hgt. clear Hgt.
    simpl. arithsimpl. allunfold @apply_bterm. allsimpl.
    apply lsubst_alpha_congr2 with (sub:=[(nvarx, fix_approx k f)]) in Hfr0.
    apply (approx_alpha_rw_l_aux _ _ _ _ Hfr0).
    auto.
Qed.

(*
Lemma dummy_context_crary_5_8_mrk {o} :
  forall lib (f e1 : @NTerm o) m,
    let bt1:= bterm [nvarx] e1 in
    dummy_context_mrk lib nvarx e1
    -> isprogram f
    -> isprogram_bt bt1
    -> computes_to_marker lib (apply_bterm bt1 [(mk_fix f)]) m
    -> forall k, approx lib (mk_marker m) (apply_bterm bt1 [(fix_approx k f)]).
Proof.
  introv Hdum Hp Hpb Hcv; introv; repnud Hdum; exrepnd.
  dimp (Hdum0 (fix_approx k f));[ eauto 2 with slow |].
  allunfold @apply_bterm; allsimpl.
  pose proof (Hdum0 (mk_fix f)) as h.
  autodimp h hh;[apply isprogram_fix; auto|].
  pose proof (reduces_to_eq_val_like
                lib (lsubst e1 [(nvarx, mk_fix f)]) (mk_marker m) (mk_marker m0)) as e.
  repeat (autodimp e hh);
    try (complete (unfold isvalue_like; right; right; sp)).
  inversion e; subst; GC.
  apply approx_mk_marker_iff; auto.
  fold_applybt.
  apply @isprogram_bt_implies; tcsp.
  introv i; allsimpl; dorn i; tcsp; subst.
  eauto with slow.
Qed.
 *)

(* begin hide *)



Lemma apply_bterm_fix_program_rw {o} :
  forall lib (f fv e : @NTerm o),
   reduces_to lib f fv
   -> isprogram f
   -> isprogram (apply_bterm (bterm [nvarx] e) [mk_fix f])
   -> isprogram (apply_bterm (bterm [nvarx] e) [mk_fix fv]).
Proof.
  unfold apply_bterm. introv Hp Hred Hap; allsimpl.
  eapply subst_change_prog with (ts := mk_fix f); eauto with slow.
Qed.




Lemma cequiv_approx_ub_rw {o} :
  forall lib (f fv e t : @NTerm o),
   cequiv lib f fv
   -> is_approx_ub lib (fun n => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t
   -> is_approx_ub lib (fun n => apply_bterm (bterm [nvarx] e) [fix_approx n fv]) t.
Proof.
  unfold apply_bterm. simpl. introv  Hc Hub. unfolds_base. intro n.
  specialize (Hub n). allsimpl.
  apply (fix_cequiv_congr _ n) in Hc.
  applydup @approx_relates_only_progs in Hub.
  repnd.
  apply @cequiv_subst_congr with (e:=e) (v:=nvarx) in Hc; auto.
  repnud Hc.
  eauto with slow.
Qed.

Lemma sqlen_rel_rw {o} :
  forall lib n (f fv e : @NTerm o) v c lbt,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram (apply_bterm (bterm [v] e) [mk_fix f])
    -> computes_to_value lib (apply_bterm (bterm [v] e) [mk_fix f])
         (oterm (Can c) lbt)
    -> {lbtv : list (@BTerm o)
        $ computes_to_value lib (apply_bterm (bterm [v] e) [mk_fix fv]) (oterm (Can c) lbtv)
        # forall lbtr,
            lblift (olift (sqle_n lib n)) lbtv lbtr
            -> lblift (olift (sqle_n lib n)) lbt lbtr }.
Proof.
  introv Hred Hprf Hpr Hcv.
  duplicate Hred as Hc.
  applydup @isprogram_lsubst_implies_ispbt in Hpr; auto.
  simpl in Hpr0.
  eapply reduces_to_subst_fix in Hc; eauto.
  repnud Hc.
  clear Hc. rename Hc0 into Hap.
  apply approx_sqle in Hap. specialize (Hap (S n)). invertsn Hap.
  repnud Hap. GC.
  apply Hap2 in Hcv.
  clear Hap2.
  parallel  lbtv Hcv. repnd.
  dands; auto;[].
  introv Hrel.
  eapply (trans_rel_olift_sqlen) ; eauto.
Qed.

Lemma sqlen_rel_rw_seq {o} :
  forall lib k (f fv e : @NTerm o) v s,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram (apply_bterm (bterm [v] e) [mk_fix f])
    -> computes_to_seq lib (apply_bterm (bterm [v] e) [mk_fix f]) s
    -> {s' : ntseq
        $ computes_to_seq lib (apply_bterm (bterm [v] e) [mk_fix fv]) s'
        # (forall n, sqle_n lib k (s n) (s' n)) }.
Proof.
  introv Hred Hprf Hpr Hcv.
  duplicate Hred as Hc.
  applydup @isprogram_lsubst_implies_ispbt in Hpr; auto.
  simpl in Hpr0.
  eapply reduces_to_subst_fix in Hc; eauto.
  repnud Hc.
  clear Hc.
  rename Hc0 into Hap.
  apply approx_sqle in Hap.
  specialize (Hap (S k)).
  invertsn Hap.
  repnud Hap; GC.
  apply Hap4 in Hcv; exrepnd.
  clear Hap2 Hap3 Hap4.
  unfold apply_bterm; simpl.
  exists f'; dands; auto.
Qed.

Lemma sqlen_rel_rw_exc {o} :
  forall lib a n f fv e v t,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram (apply_bterm (bterm [v] t) [mk_fix f])
    -> computes_to_exception lib a (apply_bterm (bterm [v] t) [mk_fix f]) e
    -> {a' : NTerm & {e' : @NTerm o
         $ computes_to_exception lib a' (apply_bterm (bterm [v] t) [mk_fix fv]) e'
         # (forall e'', sqle_n lib n e' e'' -> sqle_n lib n e e'')
         # (forall a'', sqle_n lib n a' a'' -> sqle_n lib n a a'')}}.
Proof.
  introv Hred Hprf Hpr Hcv.
  duplicate Hred as Hc.
  applydup @isprogram_lsubst_implies_ispbt in Hpr; auto.
  simpl in Hpr0.
  eapply reduces_to_subst_fix in Hc; eauto.
  repnud Hc.
  clear Hc. rename Hc0 into Hap.
  apply approx_sqle in Hap. specialize (Hap (S n)). invertsn Hap.
  repnud Hap. GC.
  apply Hap3 in Hcv.
  parallel a' Hcv.
  parallel e' Hcv.
  repnd.
  dands; auto;[|].
  - introv Hrel; eapply sqlen_n_trans; eauto.
  - introv Hrel; eapply sqlen_n_trans; eauto.
Qed.

(*
Lemma computes_to_marker_apply_bterm_fix {o} :
  forall lib f fv v (t : @NTerm o) m,
    reduces_to lib f fv
    -> isprogram f
    -> isprogram (apply_bterm (bterm [v] t) [mk_fix f])
    -> computes_to_marker lib (apply_bterm (bterm [v] t) [mk_fix f]) m
    -> computes_to_marker lib (apply_bterm (bterm [v] t) [mk_fix fv]) m.
Proof.
  introv Hred Hprf Hpr Hcv.
  duplicate Hred as Hc.
  applydup @isprogram_lsubst_implies_ispbt in Hpr; auto.
  simpl in Hpr0.
  eapply reduces_to_subst_fix in Hc; eauto.
  repnud Hc; clear Hc.
  allunfold @apply_bterm; allsimpl.
  inversion Hc0 as [c].
  unfold close_comput in c; repnd.
  unfold close_compute_mrk in c.
  apply c in Hcv; auto.
Qed.
 *)

Ltac arithsimpl2 := let XX:= fresh "XX" in  repeat match goal with
[ |- context [?n-0]] => assert (n-0 = n) as XX by omega; rw XX; clear XX
|[ |- context [?n-?n]] => assert (n-n = 0) as XX by omega; rw XX; clear XX
|[ H:  context [?n-0] |- _ ] => assert (n-0 = n) as XX by omega; rewrite XX in H; clear XX
|[ H: context [?n-?n] |- _ ] => assert (n-n = 0) as XX by omega; rewrite XX in H; clear XX
end.

Lemma compactness_really_aux {o} :
  forall lib (e fv : @NTerm o),
    isprogram fv
    -> isprogram_bt (bterm [nvarx] e)
    -> forall (e2' : NTerm),
         disjoint (bound_vars e2') [nvarx]
         -> iscan (apply_bterm (bterm [nvarx] e2') [mk_fix fv])
         -> forall j : nat,
              (forall k : nat,
                 k >= j ->
                 approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx (k - j) fv])
                             (apply_bterm (bterm [nvarx] e) [fix_approx k fv]))
              -> {n : nat $ hasvalue lib (apply_bterm (bterm [nvarx] e) [fix_approx n fv]) }.
Proof.
  intros lib e fv Hcv0 Hprtb e2' Hcvb1 Hcvb2 j Hcvb3.
  exists j.
  dimp (Hcvb3 j).
  arithsimpl2.
  clear Hcvb3. allunfold @apply_bterm. allsimpl.
  applydup @approx_relates_only_progs in hyp as Hpr.
  repnd.
  apply @isprogram_lsubst_implies_ispbt in Hpr0. allsimpl.
  apply @isprogram_bt_implies with (lnt:= [mk_fix fv])in Hpr0; auto;
  [|  prove_sub_range_sat; eauto with slow].
  allunfold @apply_bterm.
  allsimpl.

  apply isv_can in Hcvb2; auto.
  apply @isvalue_change_subst_noncan with (t:=@mk_bottom o) in Hcvb2; auto.
  allunfold @subst.
  eapply hasvalue_approx; eauto.
  eexists; eauto with slow.
Qed.

Ltac destruct_all_exists := exrepnd.

Lemma fix_approx_exc {o} :
  forall lib a n (f e : @NTerm o),
    n > 0
    -> computes_to_exception lib a f e
    -> computes_to_exception lib a (fix_approx n f) e.
Proof.
  introv g comp.
  destruct n; try (complete omega).
  simpl.
  allunfold @computes_to_exception.
  allunfold @reduces_to; exrepnd.
  generalize (reduces_in_atmost_k_steps_apply _ k f (mk_exception a e) (fix_approx n f) comp0).
  intro h; exrepnd.
  exists (S k1).
  rw @reduces_in_atmost_k_steps_S2.
  exists (mk_apply (mk_exception a e) (fix_approx n f)); dands; auto.
Qed.

Lemma subst_computes_to_exception {o} :
  forall lib en t x a b e,
    @isprogram o a
    -> isprogram b
    -> computes_to_exception lib en a e
    -> computes_to_exception lib en b e
    -> hasvalue lib (subst t x a)
    -> hasvalue lib (subst t x b).
Proof.
  unfold hasvalue, computes_to_value, reduces_to.
  introv ispa ispb cea ceb comp; exrepnd.
  apply reduces_in_atmost_k_steps_implies_computes_in_kstep in comp2; exrepnd.
  clear dependent k; rename k1 into k.
  revert dependent a.
  revert dependent b.
  revert dependent t'.
  revert t x e.
  induction k; introv isv ispb ceb ispa cea r.

  - rw @computes_in_kstep_0 in r; subst.
    applydup @isvalue_subst in isv; auto; repnd.
    destruct isv0 as [isv0|isv0].

    + exists (subst t x b); dands.

      exists 0.
      apply reduces_in_atmost_k_steps_0; auto.
      apply isvalue_subst; auto.
      apply isvalue_subst in isv; auto; repnd.
      dands.
      apply subst_change_prog with (ts := a); auto.
      destruct isv as [isv|isv]; auto.

    + repnd; subst.
      apply isvalue_implies in isv0; repnd.
      eapply iscancan_doesnt_raise_an_exception in cea; sp.

  - rw @computes_in_kstep_S in r; exrepnd.

    pose proof (fresh_var_not_in [x]) as Hneq.
    remember (fresh_var [x]) as y; clear Heqy.
    rw in_single_iff in Hneq.

    generalize (crary5_7_alpha lib x y t u).

(* XXXXXXXXXXXXXXX *)

Abort.

Hint Resolve alphaeq_preserves_iscan : slow.

(* end hide *)

(** %\noindent% Finally, we have enough lemmas to prove
    the compactness theorem. Crary shows a classical
    proof that uses the LUB property. He also gives
    enough hints to derive a constructive proof that
    he thinks is less elegant. Here is a less elegant, but
    constructive proof that is better suited for
    a constructive meta-theory like the predicative fragment of Coq.

 *)

Lemma isp_can_or_exc_nexception {p} :
  forall a (e : @NTerm p),
    isprogram a
    -> isprogram e
    -> isp_can_or_exc (mk_exception a e).
Proof.
  introv ispa ispe.
  split; auto.
  apply isprogram_exception; auto.
  right; sp.
Qed.
Hint Resolve isp_can_or_exc_nexception : slow.

(* begin show *)
Theorem fix_compactness {o} : forall lib f e,
  let tf := @apply_bterm o (bterm [nvarx] e) [mk_fix f] in
  isprogram f
  -> isprogram tf
  -> hasvalue lib tf
  -> {n : nat $ let tfa :=
        (apply_bterm (bterm [nvarx] e) [fix_approx n f]) in
          hasvalue lib tfa}.
Proof.
  simpl. intros lib f e Hpf Hprt Hcv.
  unfold hasvalue in Hcv.
  destruct_all_exists. rename Hcv0 into Hcv.
  rename t' into vv.

(* end show *)

(** %\noindent% After some straightforward intial steps,
     here is the proof state:

[[
1 subgoals
f : NTerm
e : NTerm
Hpf : isprogram f
Hprt : isprogram (apply_bterm (bterm [nvarx] e) [mk_fix f])
vv : NTerm
Hcv : apply_bterm (bterm [nvarx] e) [mk_fix f] =v> vv
______________________________________(1/1)
{n : nat $ hasvalue (apply_bterm (bterm [nvarx] e) [fix_approx n f])}
]]

%\noindent% Now apply [fix_value2] to get the dichotomy in its conclusion.

  - In the left case, we get that [f] reduces to a value [fv].
    In this case, we replace [f] by [fv] everywhere using
    the lemmas [reduces_to_subst_fix], [reduces_to_subst_fix_approx] and
    [reduces_to_computes_to_value_rw]
    above. Then we can apply [weaker_crary_5_8] to [Hcv].
    The remaining proof is same even for the other case.
    So, for uniformity of both cases, we then rename [fv] into [f] and
    also rename the replacement for [vv] in [Hcv] into [vv].

  - In the right case, we get [Hdum : dummy_context e].
    then we can apply [dummy_context_crary_5_8] to get to a proof state
    which is virtually same as that of the previous case.

  %\noindent% In both cases, we have that there is some [e2'] such that
  [vv] is alpha equal to [(apply_bterm (bterm [nvarx] e2') [mk_fix f])].
  Note that [e2'] must be of the form [oterm [Can _] _].
  If it were a variable, or of the form [oterm [NCan _] _],
  we wont get a value(something of the form [oterm [Can _] _]) when
  substituting [nvarx] by [mk_fix f].

  %\noindent% We also have that there is a [j] such that
[[
forall k : nat,
      k >= j ->
      approx (apply_bterm (bterm [nvarx] e2') [fix_approx (k - j) f])
        (apply_bterm (bterm [nvarx] e) [fix_approx k f])
]]
  %\noindent% We then instantiate above with [k:=j]. to get:
[[
  approx (apply_bterm (bterm [nvarx] e2') [mk_bottom])
        (apply_bterm (bterm [nvarx] e) [fix_approx j f])]
]]
  %\noindent% Then LHS argument of approx in above
  must be a value because of what we mentioned above.
  So, by the lemma [hasvalue_approx] of the previous section,
  we have that the RHS argument of [approx] in above also is a value.
  Now, we instantiate our goal with [n:=j] to finish the proof.
*)

  duplicate Hcv as Hcvb.
  apply fix_value2 in Hcv; auto;[].
  duplicate Hprt as Hprtb0.
  apply @isprogram_lsubst_implies_ispbt in Hprtb0.
  dorn Hcv;[|dorn Hcv].
  - repnud Hcv; exrepnd.
    repnud Hcv0; exrepnd.
    duplicate Hprt as Hprtb.
    rename Hcv1 into Hred.
    apply (apply_bterm_fix_program_rw _ _ _ _ Hred) in Hprt; auto.
    assert (isprogram t') as Hpfv by eauto with slow.
    duplicate Hcvb. inverts Hcvb0 as XX99 Hvv. clear XX99.
    invertsn Hvv.
    allapply @iscan_implies; repndors; exrepnd; subst.

    { apply (sqlen_rel_rw _ 1 _ _ _ _ _ _ Hred) in Hcvb; auto.
      exrepnd.
      clear Hcvb0.  allsimpl.
      apply weaker_crary_5_8 in Hcvb1; auto.
      duplicate Hred.
      apply @reduces_to_subst_fix with (e:=e) (v:=nvarx) in Hred0; auto.
      repnud Hred0. allsimpl. exrepnd.
      pattern f.
      match goal with
          [ |- context ff [f] ] => let xx:= (context ff [t']) in assert(xx) as ZZZ;
                                     allsimpl
      end.

      + clear dependent f. clear Hprt Hcv0 Hvv.
        eapply compactness_really_aux; eauto 3 with slow.

      + parallel m trs. exrepnd. allunfold @apply_bterm. allsimpl.
        apply (reduces_to_subst_fix_aprrox _ m _ _ e nvarx) in Hred; auto.
        repnud Hred;
          eapply hasvalue_approx; eauto with slow. }

    { allunfold @computes_to_value; repnd.
      eapply (sqlen_rel_rw_seq _ 1) in Hcvb0; try (exact Hred); auto; exrepnd.
      clear Hcvb1.

      pose proof (weaker_crary_5_8 lib t' e (sterm s')) as h; simpl in h.
      repeat (autodimp h hyp).
      { unfold computes_to_value; dands; eauto 3 with slow. }
      exrepnd.

      destruct e2' as [v2|s2|op2 bs2];
        unfold apply_bterm in h2; allsimpl;
        try (complete (unfold lsubst in h2; allsimpl; boolvar; inversion h2));[].
      autorewrite with slow in *.
      clear h1.
      inversion h2 as [|? ? aeq|]; subst; clear h2.

      duplicate Hred.
      apply @reduces_to_subst_fix with (e:=e) (v:=nvarx) in Hred0; auto.
      repnud Hred0; allsimpl.
      clear Hred1.
      inversion Hred0 as [cl]; clear Hred0.
      unfold close_comput in cl; repnd; GC.
      clear cl2 cl3.
      apply cl4 in Hcvb0; clear cl4; exrepnd.

      pattern f.
      match goal with
          [ |- context ff [f] ] => let xx:= (context ff [t']) in assert(xx) as ZZZ;
                                     allsimpl
      end.

      + clear dependent f.
        eapply compactness_really_aux; eauto; simpl; eauto.

      + parallel m trs. exrepnd. allunfold @apply_bterm. allsimpl.
        apply (reduces_to_subst_fix_aprrox _ m _ _ e nvarx) in Hred; auto.
        repnud Hred;
          eapply hasvalue_approx; eauto with slow.
    }

  - unfold raises_exception in Hcv; exrepnd.
    unfold computes_to_exception in Hcv1.
    rename Hcv1 into Hred.
    duplicate Hprt as Hprtb.
    apply (apply_bterm_fix_program_rw _ _ _ _ Hred) in Hprt; auto.
    assert (isprogram (mk_exception a e0)) as Hpfv by eauto with slow.
    duplicate Hcvb. inverts Hcvb0 as XX99 Hvv. clear XX99.
    invertsn Hvv.
    allapply @iscan_implies; repndors; exrepnd; subst;[|].

    { eapply (sqlen_rel_rw lib 1) in Hcvb; try (exact Hred); auto.
      exrepnd.
      clear Hcvb0. allsimpl.
      apply weaker_crary_5_8_isp_can_or_exc in Hcvb1; auto;
      try (complete (split; auto; right; constructor; sp));
      eauto 3 with slow;[].
      duplicate Hred.
      apply @reduces_to_subst_fix with (e:=e) (v:=nvarx) in Hred0; auto.
      repnud Hred0. allsimpl. exrepnd.
      pattern f.
      match goal with
          [ |- context ff [f] ] =>
          let xx:= (context ff [mk_exception a e0]) in
          assert(xx) as ZZZ;
            allsimpl
      end.

      + clear dependent f.
        eapply compactness_really_aux; eauto 3 with slow.

      + parallel m trs. exrepnd. allunfold @apply_bterm. allsimpl.
        apply (reduces_to_subst_fix_aprrox _ m _ _ e nvarx) in Hred; auto.
        repnud Hred;
          eapply hasvalue_approx; eauto with slow. }

    { allunfold @computes_to_value; repnd.
      eapply (sqlen_rel_rw_seq _ 1) in Hcvb0; try (exact Hred); auto; exrepnd.
      clear Hcvb1.

      pose proof (weaker_crary_5_8_isp_can_or_exc lib (mk_exception a e0) e (sterm s')) as h; simpl in h.
      repeat (autodimp h hyp);
      try (complete (split; auto; right; constructor; sp)).
      { unfold computes_to_value; dands; eauto 3 with slow. }
      exrepnd.

      destruct e2' as [v2|s2|op2 bs2];
        unfold apply_bterm in h2; allsimpl;
        try (complete (unfold lsubst in h2; allsimpl; boolvar; inversion h2));[].
      autorewrite with slow in *.
      clear h1.
      inversion h2 as [|? ? aeq|]; subst; clear h2.

      duplicate Hred.
      apply @reduces_to_subst_fix with (e:=e) (v:=nvarx) in Hred0; auto.
      repnud Hred0; allsimpl.
      clear Hred1.
      inversion Hred0 as [cl]; clear Hred0.
      unfold close_comput in cl; repnd; GC.
      clear cl2 cl3.
      apply cl4 in Hcvb0; clear cl4; exrepnd.

      pattern f.
      match goal with
          [ |- context ff [f] ] =>
          let xx:= (context ff [mk_exception a e0]) in
          assert(xx) as ZZZ;
            allsimpl
      end.

      + clear dependent f.
        eapply compactness_really_aux; eauto; simpl; eauto.

      + parallel m trs. exrepnd. allunfold @apply_bterm. allsimpl.
        apply (reduces_to_subst_fix_aprrox _ m _ _ e nvarx) in Hred; auto.
        repnud Hred;
          eapply hasvalue_approx; eauto with slow.
    }

  - exrepnd.
    eapply @dummy_context_crary_5_8 with (f:=f) in Hcv; auto; eauto 2 with slow.
    allsimpl. exrepnd. duplicate Hcvb.
    invertsna Hcvb0 Hvv.
    invertsn Hvv0.
    eapply compactness_really_aux; eauto 3 with slow.
Qed.

(* begin hide *)

(* !! MOVE to substitution.v .. need to move the slow rewrite db too*)
Lemma apply_bterm_var {o} : forall v t,
  @apply_bterm o (bterm [v] (vterm v)) [t] = t.
Proof.
  intros. unfold apply_bterm. simpl.
  change_to_lsubst_aux4; [| simpl; spcl; disjoint_reasoning; fail].
  simpl. autorewrite with slow. auto.
Qed.



(* end hide *)
Corollary fix_compactness_no_context {o} : forall lib f,
  @isprogram o f
  -> hasvalue lib (mk_fix f)
  -> {n : nat $ hasvalue lib (fix_approx n f)}.
Proof.
  introv Hpr Hv.
  apply (fix_compactness lib _ (vterm nvarx) ) in Hpr; auto;
  allrw @apply_bterm_var; auto.
  eauto 2 with slow.
Qed.

(*
(* !!MOVE *)
Lemma hasvalue_apseq {o} :
  forall lib s (t : @NTerm o),
    hasvalue lib (mk_apseq s t)
    -> {n : nat & computes_to_value lib t (mk_nat n) }.
Proof.
  introv hv.
  unfold hasvalue, computes_to_value, reduces_to in hv; exrepnd.
  revert dependent t.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion hv0; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [v1|f|op bs]; allsimpl; ginv.
    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.

    + Case "Can".
      clear IHk.
      apply compute_step_apseq_success in comp1; repndors; exrepnd; subst; fold_terms; ginv.
      apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow.

    + remember (compute_step lib (oterm (NCan ncan) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      apply IHk in comp0; auto; repndors; exrepnd.
      exists n0; dands; auto.
      allunfold @computes_to_value; repnd; dands; auto.
      eapply reduces_to_if_split2; eauto.

    + apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      inversion hv0; allsimpl; tcsp.

    + remember (compute_step lib (oterm (Abs abs) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      apply IHk in comp0; auto; repndors; exrepnd.
      exists n0; dands; auto.
      allunfold @computes_to_value; repnd; dands; auto.
      eapply reduces_to_if_split2; eauto.
Qed.
*)

Hint Resolve isprogram_fix : slow.

Corollary fix_compactness_apply {o} : forall lib f G,
  @isprogram o f
  -> isprogram G
  -> hasvalue lib (mk_apply G (mk_fix f))
  -> {n : nat $ hasvalue lib (mk_apply G (fix_approx n f))}.
Proof.
  introv Hpf Hpg Hv.

  pose proof (fix_compactness lib f (mk_apply G (mk_var nvarx))) as q.
  simpl in q.
  unfold apply_bterm in q; allsimpl.
  rw @cl_lsubst_lsubst_aux in q; allsimpl; eauto 4 with slow;[].
  fold_terms.
  rw (lsubst_aux_trivial_cl2 G) in q; eauto 4 with slow;[].
  autorewrite with var in *.
  repeat (autodimp q hyp).
  { apply isprogram_apply; eauto 4 with slow. }
  exrepnd.
  unfold apply_bterm in q0; allsimpl.
  rw @cl_lsubst_lsubst_aux in q0; allsimpl; eauto 4 with slow;[].
  autorewrite with var in *.
  fold_terms.
  rw (lsubst_aux_trivial_cl2 G) in q0; eauto 4 with slow.
Qed.

(* begin hide *)

Lemma crary_5_9_really_aux {o} :
  forall lib (mm : nat),
  (forall f t e : @NTerm o,
   isprogram f ->
   is_approx_ub lib (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f])
     t -> sqle_n lib mm (apply_bterm (bterm [nvarx] e) [mk_fix f]) t) ->
  forall t e : NTerm,
  isprogram t ->
  isprogram_bt (bterm [nvarx] e) ->
  forall (c0 : CanonicalOp) (eclbt : list BTerm) (f : NTerm),
  isprogram f ->
  isprogram (apply_bterm (bterm [nvarx] e) [mk_fix f]) ->
  computes_to_value lib (apply_bterm (bterm [nvarx] e) [mk_fix f])
    (oterm (Can c0) eclbt) ->
  is_approx_ub lib (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f])
    t ->
  forall e2' : NTerm,
  disjoint (bound_vars e2') [nvarx] ->
  alpha_eq (oterm (Can c0) eclbt) (apply_bterm (bterm [nvarx] e2') [mk_fix f]) ->
  forall j : nat,
  (forall k : nat,
   k >= j ->
   approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx (k - j) f])
     (apply_bterm (bterm [nvarx] e) [fix_approx k f])) ->
  {tr_subterms : list (@BTerm o) $
  computes_to_value lib t (oterm (Can c0) tr_subterms)
  # lblift (olift (sqle_n lib mm)) eclbt tr_subterms}.
Proof.
    intros lib mm IHmm t e XX Hispbt c0 eclbt f Hp XX0 Hcvb Hub1 e2' Hcv1 Hcv2 j Hcv3.
    rename Hcv3 into Hapa.
    assert (forall i:nat, approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx i f]) t)  as CC by
     (intro i;dimp ( Hapa (i+j));[omega|];assert (i+j-j = i) as ZZ by omega;rw ZZ in hyp;
        eapply approx_trans; eauto).
    clear Hub1 Hapa.
    rename Hcv1 into Hdis.
    duplicate Hcv2 as Halb. invertsna Hcv2 Hal.
    unfold apply_bterm in Hal1. simpl in Hal1.
    rw @lsubst_lsubst_aux_prog_sub in Hal1;
      [| subst;try prove_sub_range_sat; eauto with slow].
    destruct e2' as [| | ecao ecalbt]; simpl in Hal1;
    [ revert Hal1; cases_if; intro Hal1; invertsn Hal1; fail|ginv;fail| ].
    invertsn Hal1.
    pose proof (CC 0) as H0a.
    unfold apply_bterm in H0a.
    remember 0 as n0 (*to prevent computation that confuses eauto *). simpl in H0a.
    rw @lsubst_lsubst_aux_prog_sub in H0a;
      [|try prove_sub_range_sat;eauto with slow].
    subst n0.
    apply approx_sqle in H0a. simpl in H0a. specialize  (H0a (S mm)).
    invertsn H0a.
    repnud H0a.
    repnud H0a2.
    match type of H0a2 with
    context [ computes_to_value ?lib (oterm (Can ?cc) ?llbt) _] =>
      dimp (H0a2 cc llbt);[apply computes_to_value_isvalue_refl;auto;fail |]
    end.
    parallel tclbt hyp.
    repnd.
    dands;sp.
    repnud hyp.
    repeat(simpl_list).
    apply le_lblift2 with (R1:= (olift (sqle_n lib mm)));
      [apply le_olift;unfolds_base; auto |].
    unfolds_base.
    dands;[congruence |].
    introv Hlt. duplicate Hlt as Hltb.
    dimp (hyp n); [omega|].
    rename hyp2 into H0rel.
    dimp ((selectbt_in2 n eclbt));[]. rename hyp into Hbsec.
    exrepnd.
    destruct bt as [ecnlv ecnnt].
    dimp ((selectbt_in2 n tclbt));[omega|]. rename hyp into Hbstc.
    exrepnd.
    destruct bt as [tcnlv tcnnt].
    dimp ((selectbt_in2 n  ecalbt));[omega|]. rename hyp into He2bt'.
    exrepnd. destruct bt as [ecanlv ecannt].
    pose proof (fresh_vars (length ecnlv) (all_vars ecnnt ++ all_vars tcnnt
      ++ ecanlv ++[nvarx] ++ all_vars  ecannt ++ bound_vars f)) as Hf.
    exrepnd.
    exists lvn.
    exists (lsubst ecnnt (var_ren ecnlv lvn)).
    exists (lsubst tcnnt (var_ren tcnlv lvn)).
    rw @selectbt_map in H0rel; [| omega].
    repeat(rwselectbt).
    apply blift_numbvars in H0rel.
    unfold num_bvars in H0rel. simpl in H0rel.
    apply Hal0 in Hlt.
     rename Hlt into Hall.
    rw @selectbt_map in Hall; try congruence. repeat(rwselectbt). simpl in Hall.
    rw memvar_dmemvar in Hall.
    disjoint_flat3. show_hyps.
    simpl in He2bt'1.
    revert  Hall. cases_ifd Hd; [disjoint_reasoningv;spc; fail|]; introv Hall.

    clear Hdf. apply alphabt_change_var with (lv:=lvn) in Hall; auto;
      [| disjoint_reasoningv; try(disjoint_lsubst);simpl;simpl_vlist;
          try(rewrite (fst Hp));disjoint_reasoningv;fail].
    repnd.
    dands;spc; try(apply btchange_alpha; auto); try congruence;
    try match goal with [|- disjoint _ _ ] => disjoint_reasoningv end.
    unfolds_base.
    Hint Resolve wf_sub_vars : slow.
    progress repeat match goal with
     [H: computes_to_value ?lib _ (oterm _ ?lbt) |- _ ] => let Hwf := fresh H "wf" in
          let Hwf1 := fresh Hwf "1" in
          let Hwf2 := fresh Hwf "1" in
          pose proof (computes_to_value_wf4 lib _ _ H) as Hwf; hide_hyp H;
          inverts Hwf as Hwf1 Hwf2; clear Hwf2;
          match goal with
          [ HH : LIn _ lbt |- _ ] => pose proof (Hwf1 _ HH) as Hwf2; invertsn Hwf2
          end
    end.
    show_hyps.
    dands; try(apply lsubst_wf_iff;[eauto with slow| auto]);[].
    introv Hwf H1p H2p.
    rw <- @lsubst_lsubst_aux_prog_sub in Hall0;
      [| try prove_sub_range_sat; eauto with slow; fail].
    pose proof (lsubst_trim2_alpha1 _ _ _ H1p H2p) as Xtrim. simpl in Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwf H1p H2p) as Xprog.
    allsimpl.
    match type of Xprog with
    prog_sub ?s => remember s as subp
    end.
    repnd. rename Xtrim into Xtrimt.
    rename Xtrim0 into Xtrime.

    pose proof (crary_5_9_aux ecannt nvarx ecanlv lvn subp) as Xa.
    remember (sub_filter subp [nvarx]) as subf.

    apply @lsubst_alpha_congr2 with (sub:=subp) in Hall0.
    rwg Xtrime.
    rwg Hall0.
    dimp (Xa (mk_fix f)); auto; try congruence; eauto 2 with slow;
    [| disjoint_reasoningv; fail].
    rwg hyp. clear hyp.
    apply IHmm; auto.
    unfolds_base.
    intro m.
    specialize (CC m). unfold apply_bterm in CC.
    simpl in CC.
    rewrite  lsubst_lsubst_aux_prog_sub in CC;[| prove_sub_range_sat; eauto with slow;fail].
    simpl in CC.
    duplicate CC as Happ.
    clear CC. (* just to move it to the top*)
    repnud Happ. invertsn Happ. repnud Happ.
    repnud Happ2.
    match type of Happ2 with
    context [ computes_to_value ?lib (oterm (Can ?cc) ?llbt) _] =>
      dimp (Happ2 cc llbt);[apply computes_to_value_isvalue_refl;auto;fail |]
    end.
    clear Happ. rename hyp into Hapm. exrepnd.
    match goal with
    [ H1: computes_to_value ?lib t _, H2: computes_to_value ?lib t _ |- _ ] =>
      pose proof (computes_to_value_eq lib t _ _ H1 H2) as Heq; symmetry in Heq; invertsn Heq
    end.
    apply clearbot_relbt in Hapm0.
    repnud Hapm0. (repeat simpl_list). GC.
    dimp (Hapm0 n);[ omega |]. rename hyp into Hbrel. clear Hapm0.
    rw @selectbt_map in Hbrel;[| congruence].
    repeat(rwselectbt).
    simpl in Hbrel.
    rw memvar_dmemvar in Hbrel.
    assert (isprogram (fix_approx m f) ) by eauto with slow.
    revert  Hbrel. cases_ifd Hd; [disjoint_reasoningv;spc; fail|]; introv Hbrel.
    apply @approxbtd_change3 with (lvn:=lvn) in Hbrel; unfold num_bvars;
      simpl; auto; try congruence;
    [| apply disjoint_app_r; split;
        apply disjoint_sym; apply disjoint_remove_nvars2;
        disjoint_reasoningv; disjoint_lsubst;simpl; simpl_vlist;
        repeat(simpl_sub); disjoint_reasoningv].
    simpl in Hbrel.
    unfold apply_bterm in Hbrel. simpl in Hbrel.
    allrw (@fold_var_ren).
    rewrite  <- lsubst_lsubst_aux_prog_sub in Hbrel;[| prove_sub_range_sat; eauto with slow;fail].
    unfold approx_open in Hbrel; repnud Hbrel.
    applydup @prog_sub_implies_wf in Xprog.
    dimp (Hbrel subp); eauto 3 with slow.
    * apply (approx_alpha_rw_r _ _ _ _ Xtrimt).
      match goal with
      [ H: approx ?lib ?l1 ?r |- approx ?lib ?l2 ?r] => assert (alpha_eq l2 l1) as X89;
        [|apply (approx_alpha_rw_l lib _ _ _ X89);auto]
       end.
      clear hyp Hbrel Hbrel0 Hbrel1 Happ0 Hdf.
      unfold apply_bterm. simpl. apply alpha_eq_sym.
      apply Xa;auto;try congruence; eauto 3 with slow;[].
      disjoint_reasoningv.
    * clear Xa  Hbrel. rw (alphaeq_preserves_program _ _ Xtrime) in  H1p.
      rw (alphaeq_preserves_program _ _ Hall0) in  H1p.
      apply @lsubst_wf_iff with (sub:=subp) in Hbrel0; auto.
      split; auto.
      unfolds_base. repnud H1p. clear H1p. repnud H1p0.
      apply (eqvars_nil _ _  H1p0).  clear H1p0.
      apply eq_vars_prog_sub_same_dom; auto.
      apply eq_vars_same_sub; auto.
      apply eq_vars_prog_sub_same_dom; auto; try prove_sub_range_sat; eauto 2 with slow.
Qed.

Lemma crary_5_9_really_aux_exc {o} : forall lib (mm : nat),
  (forall f t e : @NTerm o,
    isprogram f ->
    is_approx_ub lib
      (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t ->
    sqle_n lib mm (apply_bterm (bterm [nvarx] e) [mk_fix f]) t) ->
   forall t e : NTerm,
   isprogram t ->
   isprogram_bt (bterm [nvarx] e) ->
   forall a' e' f : NTerm,
   isprogram f ->
   isprogram (apply_bterm (bterm [nvarx] e) [mk_fix f]) ->
   (apply_bterm (bterm [nvarx] e) [mk_fix f] =e>( a', lib)e') ->
   is_approx_ub lib
     (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t ->
   forall e2' : NTerm,
   disjoint (bound_vars e2') [nvarx] ->
   alpha_eq (mk_exception a' e') (apply_bterm (bterm [nvarx] e2') [mk_fix f]) ->
   forall j : nat,
   (forall k : nat,
    k >= j ->
    approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx (k - j) f])
      (apply_bterm (bterm [nvarx] e) [fix_approx k f])) ->
   {a'0, e'0 : NTerm $
   (t =e>( a'0, lib)e'0) # sqle_n lib mm a' a'0 # sqle_n lib mm e' e'0}.
Proof.
    intros lib mm IHmm t e XX Hispbt a e' f Hp XX0 Hcvb Hub1 e2' Hcv1 Hcv2 j Hapa.
    assert (forall i:nat,
              approx lib (apply_bterm (bterm [nvarx] e2')
                                      [fix_approx i f]) t)
      as CC
        by
          (intro i;
           dimp ( Hapa (i+j));[omega|];
           assert (i+j-j = i) as ZZ by omega;
           rw ZZ in hyp;
           eapply approx_trans; eauto).
    clear Hub1 Hapa.
    rename Hcv1 into Hdis.
    duplicate Hcv2 as Halb. invertsna Hcv2 Hal.
    unfold apply_bterm in Hal1. simpl in Hal1.
    repeat (destruct lbt2; simpl in Hal; cpx); GC; allsimpl.
    rw @lsubst_lsubst_aux_prog_sub in Hal1;
      [| subst;try prove_sub_range_sat; eauto with slow].
    destruct e2' as [| | ecao ecalbt]; simpl in Hal1;
      [ revert Hal1; cases_if; intro Hal1; invertsn Hal1; fail|ginv; fail | ].
    invertsn Hal1.
    repeat (destruct ecalbt; allsimpl; cpx).
    pose proof (CC 0) as H0a.
    unfold apply_bterm in H0a.
    remember 0 as n0 (*to prevent computation that confuses eauto *). simpl in H0a.
    rw @lsubst_lsubst_aux_prog_sub in H0a;
      [|try prove_sub_range_sat;eauto with slow].
    subst n0.
    apply approx_sqle in H0a. simpl in H0a. specialize  (H0a (S mm)).
    invertsn H0a.
    repnud H0a.
    applydup @isprogram_exception_implies in H0a0; exrepnd; cpx;[].
    destruct b1; destruct b; allsimpl; ginv; allsimpl.
    allrw @fold_nobnd; allrw @fold_exception.
    repnud H0a3.
    match type of H0a3 with
      | context [ computes_to_exception _ _ (mk_exception ?a ?x) _ ] =>
        dimp (H0a3 a x) ;[apply computes_to_exception_refl;auto;fail |]
    end.
    exrepnd.
    pose proof (Hal0 0) as h; autodimp h hh.
    unfold selectbt in h; simpl in h.
    apply alphaeqbt_nilv2 in h.
    pose proof (Hal0 1) as q; autodimp q hh.
    unfold selectbt in h; simpl in h.
    apply alphaeqbt_nilv2 in q.
    allrw app_nil_r.
    allrw disjoint_singleton_r; allrw in_app_iff; allrw not_over_or; repnd.
    rw <- @lsubst_lsubst_aux in h;
      [|simpl; allrw app_nil_r; rw (fst Hp); rw remove_nvars_nil_l; auto;fail].
    rw <- @lsubst_lsubst_aux in q;
      [|simpl; allrw app_nil_r; rw (fst Hp); rw remove_nvars_nil_l; auto;fail].
    eexists; eexists; dands; eauto.
    - rwg h; clear h.
      apply IHmm; auto.
      unfolds_base.
      intro m.
      specialize (CC m).
      unfold apply_bterm in CC.
      simpl in CC.
      eapply approx_alpha_rw_l_aux in CC;[|apply alpha_eq_mk_exception_lsubst];[].
      apply approx_exception in CC; exrepnd.
      apply approx_trans with (b := x); auto.
      apply (computes_to_exception_eq lib a' x) with (e1 := e'0) in CC0; auto; repnd; subst;[].
      apply approx_refl; auto.
      apply preserve_program_exc2 in hyp0; sp.
    - rwg q; clear q.
      apply IHmm; auto.
      unfolds_base.
      intro m.
      specialize (CC m).
      unfold apply_bterm in CC.
      simpl in CC.
      eapply approx_alpha_rw_l_aux in CC;[|apply alpha_eq_mk_exception_lsubst];[].
      apply approx_exception in CC; exrepnd.
      apply approx_trans with (b := c); auto.
      apply (computes_to_exception_eq lib a' x) with (e1 := e'0) in CC0; auto; repnd; subst;[].
      apply approx_refl; auto.
      apply preserve_program_exc2 in hyp0; sp.
Qed.

(*
(* !! MOVE *)
Lemma lsubst_mk_marker {o} :
  forall (sub : @Sub o) m,
    lsubst (mk_marker m) sub = mk_marker m.
Proof.
  introv.
  unfold lsubst; simpl; auto.
Qed.

Corollary weaker_crary_5_8_mrk {o} :
  forall lib (f e1 : @NTerm o) m,
    let bt1:= bterm [nvarx] e1 in
    computes_to_marker lib (apply_bterm bt1 [(mk_fix f)]) m
    -> isprogram f
    -> isvalue_like f
    -> isprogram_bt bt1
    -> {j : nat $ forall k, k >= j -> approx lib (mk_marker m) (apply_bterm bt1 [(fix_approx k f)])}.
Proof.
  introv Hcv Hp Hvl Hbt.
  repnud Hcv.
  repnud Hcv.
  exrepnd.
  simpl.
  apply weaker_crary_5_8_aux2_val_like in Hcv0; allsimpl; exrepnd; auto.
  apply alpha_eq_marker in Hcv0.
  unfold apply_bterm in Hcv0; allsimpl.
  unfold lsubst in Hcv0; allsimpl; allrw app_nil_r; allrw remove_nvars_nil_l.
  destruct Hp as [cl wf]; rw cl in Hcv0.
  boolvar; try (complete (provefalse; sp)).
  destruct e2' as [|op bs]; allsimpl; boolvar; ginv.
  destruct op; ginv.
  inversion Hcv0; subst.
  destruct bs; allsimpl; cpx; fold_terms; GC.
  exists j; introv x.
  pose proof (Hcv2 k x) as h.
  allunfold @apply_bterm; allsimpl.
  allrw @lsubst_mk_marker; auto.
Qed.
 *)

Lemma crary_5_9_really_aux_seq {o} :
  forall lib (mm : nat),
    (forall f t e : @NTerm o,
       isprogram f ->
       is_approx_ub lib (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f])
                    t -> sqle_n lib mm (apply_bterm (bterm [nvarx] e) [mk_fix f]) t)
    -> forall t e : NTerm,
         isprogram t
         -> isprogram_bt (bterm [nvarx] e)
         -> forall s (f : NTerm),
              isprogram f
              -> isprogram (apply_bterm (bterm [nvarx] e) [mk_fix f])
              -> computes_to_seq lib (apply_bterm (bterm [nvarx] e) [mk_fix f]) s
              -> is_approx_ub lib (fun n : nat => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t
              -> forall e2' : NTerm,
                   disjoint (bound_vars e2') [nvarx]
                   -> alpha_eq (sterm s) (apply_bterm (bterm [nvarx] e2') [mk_fix f])
                   -> forall j : nat,
                        (forall k : nat,
                           k >= j ->
                           approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx (k - j) f])
                                  (apply_bterm (bterm [nvarx] e) [fix_approx k f]))
                        -> {s' : ntseq
                            $ computes_to_seq lib t s'
                            # (forall n, sqle_n lib mm (s n) (s' n))}.
Proof.
    intros lib mm IHmm t e XX Hispbt s f Hp XX0 Hcvb Hub1 e2' Hcv1 Hcv2 j Hcv3.
    rename Hcv3 into Hapa.

    assert (forall i:nat, approx lib (apply_bterm (bterm [nvarx] e2') [fix_approx i f]) t)
      as CC
        by (intro i;dimp (Hapa (i+j));[omega|];
            assert (i+j-j = i) as ZZ by omega;
            rw ZZ in hyp;
            eapply approx_trans; eauto).

    clear Hub1 Hapa.
    rename Hcv1 into Hdis.
    invertsna Hcv2 Hal.

    destruct e2' as [v2|s2|op2 bs2];
      unfold apply_bterm in Hal0; allsimpl;
      try (complete (unfold lsubst in Hal0; allsimpl; boolvar; inversion Hal0));[].
    autorewrite with slow in *; ginv.
    clear Hdis.

    unfold apply_bterm in CC; allsimpl.

    applydup @reduces_to_preserves_program in Hcvb as isp; auto;[].
    assert (isprogram (sterm s2)) as isp2.
    { eapply alphaeq_preserves_program; try (exact isp).
      constructor; introv; eauto 3 with slow. }

    pose proof (CC 0) as H0a; autorewrite with slow in *.
    apply le_bin_rel_approx1_eauto in H0a.
    apply howe_lemma2_seq in H0a; eauto 3 with slow;[].
    exrepnd.
    exists f'; dands; auto.
    introv; eauto 3 with slow.
    pose proof (H0a1 n) as q.
    apply howetheorem1 in q; eauto 3 with slow.
    apply approx_sqle in q.
    specialize (q mm).
    eapply (fst (respects_alpha_sqlen _ _));[|exact q].
    eauto 3 with slow.
Qed.

(* end hide *)

(** %\noindent% We can now prove the LUB property similar to
    the way Crary did. Only the initial part of the proof is different.
    We have to deal with the dichotomy of [fix_value2] exactly the
    way we did in the proof of Compactness.

    After dealing with the dichotomy, the remaning argument is
    essentially a coinductive one. For these domain theoretic proofs,
    Like Crary, we make use of the fact of the fact that the computation
    system of Nuprl is deterministic. Howe showed that for such determinstic
    lazy computation systems, [approx] is equivalent of [sqle] (defined below).
    Hence, this proof can be done more conveniently by induction on natural
    numbers.
 *)

Lemma crary5_9 {o} : forall lib f t e,
  @isprogram o f
  -> is_approx_ub lib (fun n => apply_bterm (bterm [nvarx] e) [fix_approx n f]) t
  -> approx lib (apply_bterm (bterm [nvarx] e) [mk_fix f]) t.
Proof.
  introv Hv Hub.
  rw @approx_sqle. intro mm.
  generalize dependent Hub.
  generalize dependent Hv.
  revert f t e.
  induction mm; introv Hv Hub;
  duplicate Hub as Hubbb;
  repnud Hub; pose proof (Hub 0) as XX;
  apply approx_relates_only_progs in XX;
  repnd; unfold subst in XX0; apply @isprogram_lsubst_implies_ispbt in XX0;
  simpl in XX0; duplicate XX0 as Hispbt;
  apply @isprogram_bt_implies with (lnt:= [mk_fix f])in XX0; auto;
    try(prove_sub_range_sat; eauto with slow; fail); constructor; auto.
  unfolds_base.
  dands; auto.

  - introv Hcv.
    duplicate Hcv as Hcvb.
    rename tl_subterms into eclbt.
    apply fix_value2 in Hcv; auto;[].
    dorn Hcv;[|dorn Hcv].

    + repnud Hcv; exrepnd.
      repnud Hcv0.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.
      apply (sqlen_rel_rw _ mm _ _ _ _ _ _ Hcv1) in Hcvb; auto.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.
      exrepnd.
      rename Hcvb1 into Hcvb.
      duplicate Hcvb as Hcv.
      match goal with
          [ |- context ff [eclbt] ] =>
          let xx:= (context ff [lbtv]) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; repnd; dands; auto)]
      end.
      clear Hcvb0. clear dependent eclbt.
      rename lbtv into eclbt.
      clear dependent f. rename c into c0.
      allrw @isvalue_iff; repnd.
      rename t' into f.
      apply weaker_crary_5_8 in Hcv; auto.
      allsimpl; exrepnd.
      simpl in Hcv0. exrepnd.
      eapply crary_5_9_really_aux; eauto.

    + repnud Hcv; exrepnd.
      repnud Hcv1.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.
      apply (sqlen_rel_rw _ mm _ _ _ _ _ _ Hcv1) in Hcvb; auto.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.
      exrepnd.
      rename Hcvb1 into Hcvb.
      duplicate Hcvb as Hcv.
      match goal with
          [ |- context ff [eclbt] ] =>
          let xx:= (context ff [lbtv]) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; repnd; dands; auto)]
      end.
      applydup @cequiv_isprogram in Hcv1 as h; destruct h as [h1 h]; clear h1.
      clear Hcvb0. clear dependent eclbt.
      rename lbtv into eclbt.
      clear dependent f. rename c into c0.
      remember (mk_exception a e0) as f.
      apply weaker_crary_5_8_isp_can_or_exc in Hcv; auto;
      [|subst; constructor; auto; right; constructor; sp].
      exrepnd.
      clear Heqf e0.
      simpl in Hcv0. exrepnd.
      eapply crary_5_9_really_aux; eauto.

    + exrepnd. eapply @dummy_context_crary_5_8 with (f:=f) in Hcv; eauto.
      exrepnd. clear Hub. rename Hubbb into Hub1.
      simpl in Hcv0. exrepnd.
      eapply @crary_5_9_really_aux with (f:=f); eauto.

  - introv Hcv.
    duplicate Hcv as Hcvb.
    apply fix_value2_exc in Hcv; auto;[].
    dorn Hcv;[|dorn Hcv].

    + repnud Hcv; exrepnd.
      repnud Hcv0.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.
      apply (sqlen_rel_rw_exc _ _ mm _ _ _ _ _ Hcv1) in Hcvb; auto.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.
      exrepnd.
      rename Hcvb0 into Hcvb.
      duplicate Hcvb as Hcv.
      match goal with
          [ |- context ff [e0] ] =>
          let xx:= (context ff [e']) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; parallel YYY trs; repnd; dands; auto)]
      end.
      match goal with
          [ |- context ff [a] ] =>
          let xx:= (context ff [a']) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; parallel YYY trs; repnd; dands; auto)]
      end.
      clear dependent e0.
      clear dependent a.
      clear dependent f.
      allrw @isvalue_iff; repnd.
      rename t' into f.
      apply weaker_crary_5_8_exc_isp_can_or_exc in Hcv; auto;
      [|subst; split; sp; fail].
      exrepnd; allsimpl; exrepnd.
      eapply crary_5_9_really_aux_exc; eauto.

    + repnud Hcv; exrepnd.
      repnud Hcv1.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.
      apply (sqlen_rel_rw_exc _ _ mm _ _ _ _ _ Hcv1) in Hcvb; auto.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.
      exrepnd.
      rename Hcvb0 into Hcvb.
      duplicate Hcvb as Hcv.
      match goal with
          [ |- context ff [e0] ] =>
          let xx:= (context ff [e']) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; parallel YYY trs; repnd; dands; auto)]
      end.
      match goal with
          [ |- context ff [a] ] =>
          let xx:= (context ff [a']) in
          assert(xx) as ZZZ;
            [| (parallel ZZZ trs; parallel YYY trs; repnd; dands; auto)]
      end.
      applydup @cequiv_isprogram in Hcv1 as h; destruct h as [h1 h]; clear h1.
      clear dependent e0.
      clear dependent a.
      clear dependent f.
      remember (mk_exception a0 e1) as f.
      apply weaker_crary_5_8_exc_isp_can_or_exc in Hcv; auto;
      [|subst; constructor; auto; right; constructor; sp].
      exrepnd.
      clear Heqf e1.
      simpl in Hcv0. exrepnd.
      eapply crary_5_9_really_aux_exc; eauto.

    + exrepnd.
      eapply @dummy_context_crary_5_8_exc with (f:=f) in Hcv; eauto.
      exrepnd. clear Hub. rename Hubbb into Hub1.
      simpl in Hcv0. exrepnd.
      eapply @crary_5_9_really_aux_exc with (f:=f); eauto.

  - introv comp.
    pose proof (fix_value2 lib f (sterm f0) e) as Hcv; allsimpl.
    repeat (autodimp Hcv hyp).
    { unfold computes_to_value; dands; eauto 3 with slow. }
    repndors.

    + repnud Hcv; exrepnd.
      repnud Hcv0.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.

      eapply (sqlen_rel_rw_seq _ mm) in comp; eauto; exrepnd.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.

      applydup @computes_to_seq_implies_computes_to_value in comp1 as comp; eauto 3 with slow;[].
      applydup @weaker_crary_5_8 in comp; auto.
      allsimpl; exrepnd.

      destruct e2' as [v2|s2|op2 bs2];
        unfold apply_bterm in comp4; allsimpl;
        try (complete (unfold lsubst in comp4; allsimpl; boolvar; inversion comp4));[].
      autorewrite with slow in *.
      clear comp2.
      inversion comp4 as [|? ? aeq|]; subst; clear comp4.

      applydup @cequiv_isprogram in Hcv1; repnd.
      allunfold @computes_to_value; repnd.

      eapply crary_5_9_really_aux_seq in comp1;
        try (exact Hub1); try (exact IHmm); try (exact comp5);
          simpl; auto;
      [|unfold apply_bterm; simpl; autorewrite with slow; auto];[].
      exrepnd.
      eexists; dands; eauto.
      introv; eauto 3 with slow.

      eapply sqlen_n_trans; eauto.

    + repnud Hcv; exrepnd.
      repnud Hcv1.
      duplicate XX0 as XXb.
      apply (apply_bterm_fix_program_rw _ _ _ _ Hcv1) in XX0; auto.

      eapply (sqlen_rel_rw_seq _ mm) in comp; eauto; exrepnd.
      apply reduces_to_implies_cequiv in Hcv1; auto. clear Hub.
      apply (cequiv_approx_ub_rw _ _ _ _ _ Hcv1) in Hubbb.
      rename Hubbb into Hub1.

      applydup @cequiv_isprogram in Hcv1; repnd.

      applydup @computes_to_seq_implies_computes_to_value in comp1 as comp; eauto 3 with slow;[].
      applydup @weaker_crary_5_8_isp_can_or_exc in comp; auto;
      [|subst; constructor; auto; right; constructor; sp];[].
      allsimpl; exrepnd.

      destruct e2' as [v2|s2|op2 bs2];
        unfold apply_bterm in comp4; allsimpl;
        try (complete (unfold lsubst in comp4; allsimpl; boolvar; inversion comp4));[].
      autorewrite with slow in *.
      clear comp2.
      inversion comp4 as [|? ? aeq|]; subst; clear comp4.

      allunfold @computes_to_value; repnd.

      eapply crary_5_9_really_aux_seq in comp1;
        try (exact Hub1); try (exact IHmm); try (exact comp5);
          simpl;auto;
      [|unfold apply_bterm; simpl; autorewrite with slow; auto];[].
      exrepnd.
      eexists; dands; eauto.
      introv; eauto 3 with slow.

      eapply sqlen_n_trans; eauto.

    + exrepnd.
      applydup @computes_to_seq_implies_computes_to_value in comp as comp'; eauto 3 with slow;[].
      eapply @dummy_context_crary_5_8 with (f:=f) in Hcv; eauto.
      exrepnd. clear Hub. rename Hubbb into Hub1.
      simpl in Hcv0. exrepnd.
      eapply @crary_5_9_really_aux_seq with (f:=f); eauto 3 with slow.
Qed.

Lemma crary5_9_no_context {o} : forall lib f t,
  @isprogram o f
  -> is_approx_ub lib (fun n => fix_approx n f) t
  -> approx lib (mk_fix f) t.
Proof.
  introv Hpr Hv.
  apply (crary5_9 lib _ t (vterm nvarx) ) in Hpr; auto;
  allrw apply_bterm_var; auto.
Qed.

(* begin hide *)
(*
Definition interleaved {T : Set} (R : bin_rel T) (f g : nat -> T)
   :=
  forall n, {m : nat $ R (f n) (g m)}
  #
  forall n, {m : nat $ R (g n) (f m)}.

Lemma approx_approximations: forall f g s t,
  isprogram f
  -> isprogram g
  -> (snd (interleaved approx
      (fun n => apply_bterm (bterm [nvarx] s) [fix_approx n f])
      (fun n => apply_bterm (bterm [nvarx] t) [fix_approx n g])))
  -> cequiv (apply_bterm (bterm [nvarx] s) [mk_fix f])
            (apply_bterm (bterm [nvarx] t) [mk_fix g]).

Lemma cequiv_approximations: forall f g s t,
  isprogram f
  -> isprogram g
  -> interleaved approx
      (fun n => apply_bterm (bterm [nvarx] s) [fix_approx n f])
      (fun n => apply_bterm (bterm [nvarx] t) [fix_approx n g])
  -> cequiv (apply_bterm (bterm [nvarx] s) [mk_fix f])
            (apply_bterm (bterm [nvarx] t) [mk_fix g]).
Proof.
  introv Hpf Hpg Hint.
*)
