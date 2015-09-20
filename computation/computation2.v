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


Require Export alphaeq.
Require Export computation.
Require Export rel_nterm.
Require Export substitution2.
Require Export list_tacs.
(*Require Export tactics. (* WTF!! *)*)

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(** %\noindent% Now, we will extend the one step computation to multiple steps
    in a straighforward way.

*)

Fixpoint compute_at_most_k_steps {p}
         (lib : library)
         (k : nat)
         (t : NTerm) : @Comput_Result p :=
  match k with
    | 0 => csuccess t
    | S n => match compute_at_most_k_steps lib n t with
               | csuccess tn => compute_step lib tn
               | cfailure mesg subterm => cfailure mesg subterm
             end
  end.

Lemma compute_at_most_k_steps_0 {p} :
  forall lib t, @compute_at_most_k_steps p lib 0 t = csuccess t.
Proof. sp. Qed.

Lemma compute_at_most_k_steps_S {p} :
  forall lib n t,
    @compute_at_most_k_steps p lib (S n) t
    = match compute_at_most_k_steps lib n t with
        | csuccess tn => compute_step lib tn
        | cfailure mesg subterm => cfailure mesg subterm
      end.
Proof. sp. Qed.

(* begin hide *)
Example comp_test3 {p} :
  forall lib,
  compute_at_most_k_steps lib 2
     (mk_apply
       (mk_apply (mk_lam nvarx (vterm nvarx)) (mk_lam nvarx (vterm nvarx)))
       (mk_nat 0))
     = csuccess (@mk_nat p 0).
Proof. reflexivity.
Qed.

Example comp_ex_3 {p} :
  forall lib a,
  compute_at_most_k_steps lib 2
     (mk_apply
       (mk_apply (mk_lam nvarx (vterm nvarx)) (mk_lam nvarx (vterm nvarx)))
       (mk_exception a mk_zero))
     = csuccess (mk_exception a (@mk_zero p)).
Proof.
  introv.
  simpl; csunf.
  reflexivity.
Qed.


(* this formulation might be easier in some proofs .
   all definitions are currently using compute_at_most_k_steps
   We should be able to prove the equivaleunce between
  compute_at_most_k_stepsf and compute_at_most_k_steps*)
Fixpoint compute_at_most_k_stepsf {p} lib (k : nat) (t : @NTerm p) : Comput_Result :=
  match k with
    | 0 => csuccess t
    | S n => match compute_step lib t with
               | csuccess t => compute_at_most_k_stepsf lib n t
               | cfailure mesg subterm => cfailure mesg subterm
             end
  end.

Lemma compute_at_most_k_stepsf_0 {p} :
  forall lib t, @compute_at_most_k_stepsf p lib 0 t = csuccess t.
Proof. sp. Qed.

Lemma compute_at_most_k_stepsf_S {p} :
  forall lib n t,
    @compute_at_most_k_stepsf p lib (S n) t
    = match compute_step lib t with
        | csuccess t => compute_at_most_k_stepsf lib n t
        | cfailure mesg subterm => cfailure mesg subterm
      end.
Proof. sp. Qed.

Lemma compute_at_most_k_stepsf_can {p} :
  forall lib k c l c' l',
    compute_at_most_k_stepsf lib k (oterm (Can c) l) = csuccess (oterm (@Can p c') l')
    -> c = c' # l = l'.
Proof.
  introv comp.
  revert comp.
  induction k; simpl; intro comp.
  inversion comp; sp.
  apply IHk in comp; sp.
Qed.

Lemma compute_at_most_k_steps_eq_f {p} :
  forall lib k t,
    @compute_at_most_k_steps p lib k t = compute_at_most_k_stepsf lib k t.
Proof.
  induction k; simpl; sp.
  rewrite IHk.
  clear IHk.
  revert t.
  induction k; simpl; sp; destruct (compute_step lib t); auto.
Qed.

(* end hide *)

(* %\noindent% Here are some other useful definitions and
    lemmas that will
    be heavily used in later parts of our formalization.

 *)


(* General reduction functions *)

Definition reduces_in_atmost_k_steps {p} lib (t1 t2 : @NTerm p) (k : nat) :=
  compute_at_most_k_steps lib k t1 = csuccess t2.

Definition reduces_to {p} lib (t1 t2 : @NTerm p) :=
  {k : nat & reduces_in_atmost_k_steps lib t1 t2 k}.


(* reductions to values *)

Definition computes_to_value_in_max_k_steps {p} lib (k: nat) (a av : @NTerm p) :=
  reduces_in_atmost_k_steps lib a av k
  # isvalue av.

Definition computes_to_value {p} lib (t1 t2 : @NTerm p) :=
  reduces_to lib t1 t2
  # isvalue t2.


(* reductions to exceptions *)

Definition computes_to_exception_in_max_k_steps {p} lib a (t1 t2 : @NTerm p) (k : nat) :=
  reduces_in_atmost_k_steps lib t1 (mk_exception a t2) k.

Definition computes_to_exception {p} lib a (t1 t2 : @NTerm p) :=
  reduces_to lib t1 (mk_exception a t2).


(* reductions to markers *)

(* !!MOVE to opid *)
Definition mk_opabs (n : opname) (ps : list parameter) (s : opsign) : opabs :=
  {| opabs_name   := n;
     opabs_params := ps;
     opabs_sign   := s
  |}.

Definition abs_marker (m : marker) : opabs := mk_opabs m [] [].

Definition mk_marker {o} (m : marker) :=
  @oterm o (Abs (abs_marker m)) [].

Definition ismrk {o} lib (t : @NTerm o) :=
  match t with
    | oterm (Abs opabs) bs => find_entry lib opabs bs = None
    | _ => False
  end.

Definition is_mrk {o} (lib : @library o) (m : marker) :=
  ismrk lib (mk_marker m).

Definition computes_to_marker_in_max_k_steps {p} lib (a : @NTerm p) m k :=
  reduces_in_atmost_k_steps lib a (mk_marker m) k # is_mrk lib m.

Definition computes_to_marker {p} lib (t : @NTerm p) m :=
  reduces_to lib t (mk_marker m) # is_mrk lib m.


(* values or exceptions *)

Definition computes_to_val_or_exc_in_max_k_steps {p} lib (t1 t2 : @NTerm p) (k : nat) :=
  reduces_in_atmost_k_steps lib t1 t2 k
  # is_can_or_exc t2.

Definition computes_to_val_or_exc {p} lib (t1 t2 : @NTerm p) :=
  {k : nat & computes_to_val_or_exc_in_max_k_steps lib t1 t2 k}.


(* values or exceptions or markers *)

Definition computes_to_val_like_in_max_k_steps {p} lib (t1 t2 : @NTerm p) (k : nat) :=
  reduces_in_atmost_k_steps lib t1 t2 k
  # isvalue_like t2.

Definition computes_to_val_like {p} lib (t1 t2 : @NTerm p) :=
  {k : nat & computes_to_val_like_in_max_k_steps lib t1 t2 k}.


(* begin hide *)

Lemma alpha_eq_preserves_isvalue_like {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> isvalue_like a
    -> isvalue_like b.
Proof.
  introv aeq iv.
  unfold isvalue_like in iv.
  dorn iv.
  - apply iscan_implies in iv; repndors; exrepnd; subst.
    + inversion aeq; subst; left; sp.
    + inversion aeq; subst; left; sp.
  - apply alphaeq_preserves_isexc in aeq; sp.
Qed.

Definition isvaluec_like {o} (t : @CTerm o) :=
  isvalue_like (get_cterm t).

Definition reduces_toc {p} lib (t1 t2 : @CTerm p) :=
  reduces_to lib (get_cterm t1) (get_cterm t2).

Definition compute_1_step {p} lib (t : @NTerm p) :=
  match t with
    | oterm (Can _) _ => cfailure "term is already a value" t
    | oterm Exc _ => cfailure "term is already a exception" t
    | sterm _ => cfailure "term is already a value" t
    | vterm _ => compute_step lib t
    | oterm (NCan _) _ => compute_step lib t
    | oterm (Abs _) _ => compute_step lib t
  end.

Definition MoreStepsToGo := "more steps to go".

(** (computes_k_steps k t = csuccess u) iff it takes exactly k steps to
 * compute u from t. *)
Fixpoint computes_k_steps {p} lib (k : nat) (t : @NTerm p) : Comput_Result :=
  match k with
    | 0 => csuccess t
    | S n =>
      match computes_k_steps lib n t with
        | csuccess u => compute_1_step lib u
        | cfailure a b => cfailure a b
      end
  end.

Lemma computes_k_steps_S {p} :
  forall lib n t,
    @computes_k_steps p lib (S n) t
    = match computes_k_steps lib n t with
        | csuccess u => compute_1_step lib u
        | cfailure a b => cfailure a b
      end.
Proof. sp. Qed.

Lemma computes_k_steps_0 {p} :
  forall lib t, @computes_k_steps p lib 0 t = csuccess t.
Proof. sp. Qed.

Definition if_no_more {p} (n : nat) (res : @Comput_Result p) :=
  match n with
    | 0 => res
    | _ =>
      match res with
        | csuccess t => cfailure MoreStepsToGo t
        | cfailure s t => cfailure s t
      end
  end.

Fixpoint computes_k_stepsf {p} lib (k : nat) (t : @NTerm p) : Comput_Result :=
  match k with
    | 0 => csuccess t
    | S n =>
      match compute_1_step lib t with
        | csuccess t => computes_k_stepsf lib n t
        | cfailure mesg subterm => cfailure mesg subterm
      end
  end.

Lemma computes_k_stepsf_0 {p} :
  forall lib t, @computes_k_stepsf p lib 0 t = csuccess t.
Proof. sp. Qed.

Lemma computes_k_stepsf_S {p} :
  forall lib n t,
    @computes_k_stepsf p lib (S n) t
    = match compute_1_step lib t with
        | csuccess t => computes_k_stepsf lib n t
        | cfailure mesg subterm => cfailure mesg subterm
      end.
Proof. sp. Qed.

Lemma computes_k_steps_eq_f {p} :
  forall lib k t,
    @computes_k_steps p lib k t = computes_k_stepsf lib k t.
Proof.
  induction k; simpl; sp.
  rewrite IHk.
  clear IHk.
  revert t.
  induction k; simpl; sp;
  remember (compute_1_step lib t); destruct c; auto.
Qed.

Definition reduces_in_k_steps {p} lib (t1 t2 : @NTerm p) (k : nat) :=
  computes_k_steps lib k t1 = csuccess t2.

Definition reduces_in_k_stepsc {p} lib (t1 t2 : @CTerm p) (k : nat) :=
  computes_k_steps lib k (get_cterm t1) = csuccess (get_cterm t2).

Definition computes_to_ovalue {p} lib (t1 t2 : @NTerm p) :=
  reduces_to lib t1 t2 # isovalue t2.

(** Same as reduces_to but defined on WTerms *)
Definition reduces_to_wft {p} lib (t1 t2 : @WTerm p) :=
  let (a,_) := t1 in
  let (b,_) := t2 in
    {k : nat & compute_at_most_k_steps lib k a = csuccess b}.

(** Same as computes_to_value but defined on CTerm/NTerm *)
Definition computes_to_valuec {p} lib (t1 : @CTerm p) (t2 : NTerm) :=
  computes_to_value lib (get_cterm t1) t2.

(** Same as computes_to_value but defined on CTerm *)
Definition computes_to_valc {p} lib (t1 t2 : @CTerm p) :=
  computes_to_value lib (get_cterm t1) (get_cterm t2).

(** Same as computes_to_value but defined on WTerm *)
Definition computes_to_val {p} lib (t1 t2 : @WTerm p) :=
  computes_to_ovalue lib (get_wterm t1) (get_wterm t2).

(** Same as computes_to_value but defined on WTerm *)
Definition computes_to_valw {p} lib (t1 t2: @WTerm p) :=
  computes_to_value lib (get_wterm t1) (get_wterm t2).

Lemma computes_to_valc_to_valuec {p} :
  forall lib t1 t2,
    @computes_to_valc p lib t1 t2
    -> computes_to_valuec lib t1 (get_cterm t2).
Proof.
  sp.
Qed.

Lemma computes_to_value_wf {p} :
  forall lib t c bts,
    computes_to_value lib t (oterm (@Can p c) bts)
    -> map num_bvars bts= OpBindings (Can c).
Proof.
  intros ? ? ? ? Hcv.
  inversion Hcv as [Hred Hval].
  apply isvalue_wf; auto.
Qed.

Lemma computes_to_value_wf2 {p} :
  forall lib t c bts,
    computes_to_value lib t (oterm (@Can p c) bts)
    -> length bts= length(OpBindings (Can c)).
Proof. intros ? ? ? ? Hcv. inversion Hcv as [Hred Hval].
 apply isvalue_wf2; auto.
Qed.


Lemma computes_to_value_wf3 {p} :
  forall lib t c bts,
    computes_to_value lib t (oterm (@Can p c) bts)
    -> forall n,
         n < length bts
         -> num_bvars (selectbt bts n) = nth n (OpBindings (Can c)) 0.
Proof. intros ? ? ? ? Hcv. inversion Hcv as [Hred Hval].
 apply isvalue_wf3; auto.
Qed.

(* end hide *)
Definition hasvalue {p} lib (t : @NTerm p) :=
  {t' : NTerm & computes_to_value lib t t'}.
(* begin hide *)

Definition hasvaluec {p} lib (t : @CTerm p) := hasvalue lib (get_cterm t).

Definition raises_exception {p} lib (t : @NTerm p) :=
  {a : NTerm & {e : NTerm & computes_to_exception lib a t e}}.

Definition raises_exceptionc {p} lib (t : @CTerm p) :=
  raises_exception lib (get_cterm t).

Definition marks {p} lib (t : @NTerm p) :=
  {m : marker & computes_to_marker lib t m}.

Definition marksc {p} lib (t : @CTerm p) :=
  marks lib (get_cterm t).

Lemma computes_to_value_isvalue_refl {p} :
  forall lib t, @isvalue p t -> computes_to_value lib t t.
Proof.
 unfold computes_to_value; sp.
 exists 0; repeat constructor; assumption.
Qed.

Lemma computes_to_ovalue_isovalue_refl {p} :
  forall lib t, @isovalue p t -> computes_to_ovalue lib t t.
Proof.
  unfold computes_to_ovalue; sp.
  exists 0; repeat constructor; assumption.
Qed.

Lemma computes_to_value_isval_refl {p} :
  forall lib t, @isovalue_wft p t -> computes_to_val lib t t.
Proof.
  unfold computes_to_val, isovalue_wft; sp.
  destruct t.
  apply computes_to_ovalue_isovalue_refl; auto.
Qed.

Lemma computes_to_valc_refl {p} :
  forall lib t, @iscvalue p t -> computes_to_valc lib t t.
Proof.
 unfold computes_to_valc, computes_to_value, reduces_to; sp.
 exists 0; repeat constructor; assumption.
Qed.

(*
Lemma computes_to_value_isvalue_eq :
  forall t v : NTerm,
    computes_to_value t v
    -> isvalue t
    -> t = v.
Proof.
 unfold computes_to_value, reduces_to.
 intros t v H. destruct H as [H Hval]. destruct H as [k Heq].
 generalize dependent t.
 generalize dependent v.
 induction k; intros; simpl in Heq.
   inversion Heq. auto.
  inv_sub_clear H. simpl in Heq.
  inversion Heq. auto.
Qed.

*)

Lemma compute_on_value {p} :
  forall lib t,
    @isvalue p t
    -> forall k,
         compute_at_most_k_steps lib k t = csuccess t.
Proof.
  induction k; simpl;auto.
  rewrite IHk.
  apply compute_step_value. auto.
Qed.

Lemma compute_on_ovalue {p} :
  forall lib t,
    @isovalue p t
    -> forall k,
         compute_at_most_k_steps lib k t = csuccess t.
Proof.
  induction k; simpl;auto.
  rewrite IHk.
  apply compute_step_ovalue. auto.
Qed.

Lemma computes_to_value_isvalue_eq {p} :
  forall lib (t v : @NTerm p),
    computes_to_value lib t v
    -> isvalue t
    -> t = v.
Proof.
  unfold computes_to_value, reduces_to.
  introv h Hisval.
  destruct h as [H Hval].
  destruct H as [k Heq].
  unfold reduces_in_atmost_k_steps in Heq.
  rewrite compute_on_value in Heq; auto.
  inversion Heq. auto.
Qed.

Lemma computes_to_value_if_reduces_to {p} :
  forall lib t v, @reduces_to p lib t v -> isvalue v -> computes_to_value lib t v.
Proof.
  unfold computes_to_value; sp.
Qed.

Lemma computes_to_value_isvalue {p} :
  forall lib t v, @computes_to_value p lib t v -> isvalue v.
Proof.
 unfold computes_to_value; sp.
Qed.

Lemma computes_to_value_hasvalue {p} :
  forall lib t v, @computes_to_value p lib t v -> hasvalue lib t.
Proof.
  unfold hasvalue; sp.
  exists v; sp.
Qed.

Lemma computes_to_value_can {p} :
  forall lib t v,
    @computes_to_value p lib t v
    -> {c : CanonicalOp
        & {bts : list BTerm
        & v = oterm (Can c) bts}}
       [+] {f : ntseq & v = sterm f}.
Proof.
  unfold computes_to_value; introv Hcv; repnd; sp.
  allrw @isvalue_iff; repnd.
  allapply @iscan_implies.
  repndors; exrepnd; subst; allsimpl.
  - left; eexists; eexists; sp.
  - right; eexists; eauto.
Qed.

Lemma compute_at_most_k_steps_eq {p} :
  forall lib k (t : @NTerm p) t1 t2,
    compute_at_most_k_steps lib k t = t1
    -> compute_at_most_k_steps lib k t = t2
    -> t1 = t2.
Proof.
 intros lib k t t1 t2 H1 H2.
 rewrite <- H1 .
 rewrite <- H2 . auto.
Qed.

Lemma compute_at_most_k_steps_eqp {p} :
  forall lib k (t : @NTerm p) t1 t2,
    compute_at_most_k_steps lib k t = csuccess t1
    -> compute_at_most_k_steps lib k t = csuccess t2
    -> t1 = t2.
Proof.
 intros lib k t t1 t2 H1 H2.
 rewrite H1 in H2; inversion H2; auto.
Qed.

Lemma compute_at_most_k_steps_if_value {p} :
  forall lib k v,
   @isvalue p v -> compute_at_most_k_steps lib k v = csuccess v.
Proof.
 intros. apply compute_on_value. auto.
Qed.

(*
Lemma computes_at_most_k_steps_if_var :
  forall k v,
   computes_at_most_k_steps k (vterm v) = (vterm v).
Proof.
 induction k; simpl; sp.
Qed.

Lemma computes_at_most_k_steps_if_bterm :
  forall k vs t,
   computes_at_most_k_steps k (bterm vs t) = (bterm vs t).
Proof.
 induction k; simpl; sp.
Qed.
*)
(*
Lemma compute_at_most_k_steps_split :
  forall k n t u,
       compute_at_most_k_steps k t = progress u
    -> n <= k
    ->( texists it, compute_at_most_k_steps (k - n) t= progress it #
      (compute_at_most_k_steps n it) = prou).
Proof.
 induction k; intros.
 assert (n = 0) by omega; subst; simpl; auto.
 simpl in H.
 assert ((n = 0) [+] (0 < n)) by omega; destruct H1.
 rewrite H1; simpl; auto.
 assert (exists m : nat, n = S m) by (exists (n - 1); omega).
 sp. rewrite H2.
 assert (S k - S m = k - m) by omega; rewrite H3.
 simpl.
 destruct t.
 simpl in H; simpl; rewrite <- H; apply computes_at_most_k_steps_if_var.
 simpl in H; simpl; rewrite <- H; apply computes_at_most_k_steps_if_bterm.
 destruct o.
 simpl in H; simpl; rewrite <- H; apply computes_at_most_k_steps_if_value.
 constructor.
 (* make a new simpler boolean isvalue *)
 Abort.
*)

(** end hide *)
(** %\noindent% Here are some important properties about
    our computation system.

*)
Lemma no_change_after_value {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isvalue v1
    -> forall k, (compute_at_most_k_steps lib (k+k1) t = csuccess v1).
Proof.
  intros. induction k. simpl. auto.
  rewrite plus_Sn_m. simpl.
  rewrite IHk. apply compute_step_value.
  auto.
Qed.

(* begin hide *)

Lemma no_change_after_ovalue {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isovalue v1
    -> forall k, (compute_at_most_k_steps lib (k+k1) t = csuccess v1).
Proof.
  intros. induction k. simpl. auto.
  rewrite plus_Sn_m. simpl.
  rewrite IHk. apply compute_step_ovalue.
  auto.
Qed.

Lemma no_change_after_value2 {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isvalue v1
    -> forall k2,
         k1 <= k2
         -> compute_at_most_k_steps lib k2 t = csuccess v1.
Proof.
  intros. assert(k2=(k2-k1) + k1) as rwa by omega.
  rewrite rwa. apply no_change_after_value; auto.
Qed.

Lemma no_change_after_ovalue2 {p} :
  forall lib (t : @NTerm p) k1 v1,
    compute_at_most_k_steps lib k1 t = csuccess v1
    -> isovalue v1
    -> forall k2, k1<k2 -> (compute_at_most_k_steps lib k2 t = csuccess v1).
Proof.
 intros. assert(k2 = (k2 - k1) + k1) as rwa by omega.
 rewrite rwa. apply no_change_after_ovalue; auto.
Qed.

Lemma compute_step_exception {p} :
  forall lib e, @isexc p e -> compute_step lib e = csuccess e.
Proof.
  introv ise.
  destruct e; try (complete (inversion ise)).
  destruct o; try (complete (inversion ise)).
  simpl; auto.
Qed.

Lemma reduces_to_exception {p} :
  forall lib e t, @isexc p e -> reduces_to lib e t -> t = e.
Proof.
  introv ise r.
  destruct e; try (complete (inversion ise)).
  destruct o; try (complete (inversion ise)).
  clear ise.
  unfold reduces_to, reduces_in_atmost_k_steps in r; exrepnd.
  revert l r0.
  induction k; introv c.

  - simpl in c; inversion c; subst; auto.

  - rw @compute_at_most_k_steps_eq_f in c; simpl in c.
    rw <- @compute_at_most_k_steps_eq_f in c; sp.
Qed.

Lemma compute_at_most_k_steps_exception {p} :
  forall lib k (bterms : list (@BTerm p)),
    compute_at_most_k_steps lib k (oterm Exc bterms)
    = csuccess (oterm Exc bterms).
Proof.
  induction k; simpl; introv; auto.
  rw IHk; auto.
Qed.

Lemma compute_at_most_k_steps_can {p} :
  forall lib c k bterms,
    @compute_at_most_k_steps p lib k (oterm (Can c) bterms)
    = csuccess (oterm (Can c) bterms).
Proof.
  induction k; simpl; introv; auto.
  rw IHk; auto.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_can {p} :
  forall lib c bterms a k,
    @computes_to_val_or_exc_in_max_k_steps p lib (oterm (Can c) bterms) a k
    -> a = oterm (Can c) bterms.
Proof.
  introv comp.
  unfold computes_to_val_or_exc_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_can in comp0.
  inversion comp0; subst; sp.
Qed.

Lemma computes_to_val_or_exc_in_max_k_steps_exc {p} :
  forall lib (bterms : list (@BTerm p)) v k,
    @computes_to_val_or_exc_in_max_k_steps p lib (oterm Exc bterms) v k
    -> v = oterm Exc bterms.
Proof.
  introv comp.
  unfold computes_to_val_or_exc_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
  rw @compute_at_most_k_steps_exception in comp0.
  inversion comp0; subst; sp.
Qed.

Lemma no_change_after_exception {p} :
  forall lib a (t : @NTerm p) k1 e,
    computes_to_exception_in_max_k_steps lib a t e k1
    -> forall k, computes_to_exception_in_max_k_steps lib a t e (k + k1).
Proof.
  intros.
  induction k; simpl; auto.
  allunfold @computes_to_exception_in_max_k_steps.
  allunfold @reduces_in_atmost_k_steps; repnd.
  simpl.
  rw IHk; sp.
Qed.

Lemma no_change_after_exception2 {p} :
  forall lib a (t : @NTerm p) k1 v1,
    computes_to_exception_in_max_k_steps lib a t v1 k1
    -> forall k2,
         k1 <= k2
         -> computes_to_exception_in_max_k_steps lib a t v1 k2.
Proof.
  intros.
  assert(k2 = (k2 - k1) + k1) as rwa by omega.
  rewrite rwa.
  apply no_change_after_exception; auto.
Qed.

(* end hide *)
Lemma computes_to_value_eq {p} :
  forall lib t v1 v2,
    @computes_to_value p lib t v1
    -> computes_to_value lib t v2
    -> v1 = v2.
Proof.
 unfold computes_to_value, reduces_to.
 introv Hex1 Hex2.
 destruct Hex1 as [Hex1 Hv1].
 destruct Hex1 as [k1 Heq1].
 destruct Hex2 as [Hex2 Hv2].
 destruct Hex2 as [k2 Heq2].
 assert(k1=k2 \/ k1<k2 \/ k2<k1) as Htri by omega.
 destruct Htri as [Htri| Htri];[subst | destruct Htri as [Htri| Htri] ].
   apply compute_at_most_k_steps_eqp with lib k2 t; auto.

   assert(compute_at_most_k_steps lib k2 t = csuccess v1) as Heqcs.
   apply no_change_after_value2 with k1; auto; try omega.
    rewrite Heq2 in Heqcs. inversion Heqcs. auto.

   assert(compute_at_most_k_steps lib k1 t = csuccess v2) as Heqcs.
   apply no_change_after_value2 with k2; auto; try omega.
   rewrite Heq1 in Heqcs. inversion Heqcs. auto.
Qed.
(* begin hide *)

Lemma computes_to_ovalue_eq {p} :
  forall lib t v1 v2,
    @computes_to_ovalue p lib t v1
    -> computes_to_ovalue lib t v2
    -> v1 = v2.
Proof.
 unfold computes_to_ovalue, reduces_to.
 introv Hex1 Hex2.
 destruct Hex1 as [Hex1 Hv1].
 destruct Hex1 as [k1 Heq1].
 destruct Hex2 as [Hex2 Hv2].
 destruct Hex2 as [k2 Heq2].
 assert(k1=k2 \/ k1<k2 \/ k2<k1) as Htri by omega.
 destruct Htri as [Htri| Htri];[subst | destruct Htri as [Htri| Htri] ].
   apply compute_at_most_k_steps_eqp with lib k2 t; auto.

   assert(compute_at_most_k_steps lib k2 t = csuccess v1) as Heqcs.
   apply no_change_after_ovalue2 with k1; auto.
    rewrite Heq2 in Heqcs. inversion Heqcs. auto.

   assert(compute_at_most_k_steps lib k1 t = csuccess v2) as Heqcs.
   apply no_change_after_ovalue2 with k2; auto.
   rewrite Heq1 in Heqcs. inversion Heqcs. auto.
Qed.

(*
Lemma computes_to_val_eq :
  forall t v1 v2,
       computes_to_val t v1
    -> computes_to_val t v2
    -> get_wterm v1 = get_wterm v2.
Proof.
  sp; destruct t, v1, v2; allunfold computes_to_val.
  apply computes_to_value_eq with (v2 := x1) in H; subst; auto.
Qed.
*)

Lemma computes_to_val_eq {p} :
  forall lib t v1 v2,
    @computes_to_val p lib t v1
    -> computes_to_val lib t v2
    -> v1 = v2.
Proof.
  sp; destruct t, v1, v2; allunfold @computes_to_val.
  apply computes_to_ovalue_eq with (v2 := x1) in H; subst; auto.
  eauto with pi.
Qed.

Lemma computes_to_valw_eq {p} :
  forall lib t v1 v2,
    @computes_to_valw p lib t v1
    -> computes_to_valw lib t v2
    -> v1 = v2.
Proof.
  sp; destruct t, v1, v2; allunfold @computes_to_valw; allsimpl.
  apply computes_to_value_eq with (v2 := x1) in X; subst; auto.
  eauto with pi.
Qed.

Lemma computes_to_valc_isvalue_eq {p} :
  forall lib t v,
    @computes_to_valc p lib t v
    -> iscvalue t
    -> t = v.
Proof.
  unfold computes_to_valc, iscvalue.
  introv comp isv; destruct_cterms; allsimpl.
  apply cterm_eq; simpl.
  apply computes_to_value_isvalue_eq in comp; sp.
Qed.

Lemma computes_to_valc_eq {p} :
  forall lib t v1 v2,
    @computes_to_valc p lib t v1
    -> computes_to_valc lib t v2
    -> v1 = v2.
Proof.
  sp; destruct t, v1, v2; allunfold @computes_to_valc; allsimpl.
  apply computes_to_value_eq with (v2 := x1) in X; subst; auto.
  eauto with pi.
Qed.

Lemma reduces_to_symm {p} : forall lib (t : @NTerm p), reduces_to lib t t.
Proof.
 unfold reduces_to; sp; exists 0; simpl; sp.
Qed.
Hint Resolve reduces_to_symm : slow.

Lemma reduces_to_split1 {p} :
  forall lib t u,
    reduces_to lib t u
    -> t = u
    [+] {v : @NTerm p & reduces_to lib t v # compute_step lib v = csuccess u}.
Proof.
  unfold reduces_to; introv r; exrepnd.
  destruct k; simpl in r0; allunfold @reduces_in_atmost_k_steps.

  - simpl in r0; inversion r0; subst; sp.

  - simpl in r0.
    remember (compute_at_most_k_steps lib k t); destruct c; try (complete (inversion r0)).
    right; exists n; sp.
    exists k; sp.
Qed.

Lemma reduces_to_split2 {p} :
  forall lib t u,
    reduces_to lib t u
    -> t = u
    [+] {v : @NTerm p & compute_step lib t = csuccess v # reduces_to lib v u}.
Proof.
  introv H; unfold reduces_to in H; sp.
  revert r.
  unfold reduces_in_atmost_k_steps.
  revert t u.
  induction k; simpl; intros.
  inversion r; left; auto.
  remember (compute_at_most_k_steps lib k t).
  destruct c; try (complete (inversion r)); right.
  assert (compute_at_most_k_steps lib k t = csuccess n) by auto.
  apply IHk in H; sp. subst.
  exists u; sp; apply reduces_to_symm.
  exists v; sp.
  allunfold @reduces_to; sp.
  allunfold @reduces_in_atmost_k_steps; sp.
  exists (S k0); simpl.
  rewrite r0; auto.
Qed.

Lemma reduces_to_if_step {p} :
  forall lib (t u : @NTerm p),
    compute_step lib t = csuccess u -> reduces_to lib t u.
Proof.
 unfold reduces_to; sp; exists 1; simpl; sp.
Qed.
Hint Resolve reduces_to_if_step : slow.

Lemma reduces_to_if_split1 {p} :
  forall lib t u v,
  reduces_to lib t u
  -> compute_step lib u = @csuccess p v
  -> reduces_to lib t v.
Proof.
 unfold reduces_to; sp; exists (S k).
 allunfold @reduces_in_atmost_k_steps; allsimpl.
 rewrite r; auto.
Qed.

Lemma reduces_to_or {o} :
  forall lib t u v,
    @reduces_to o lib t u
    -> reduces_to lib t v
    -> (reduces_to lib u v [+] reduces_to lib v u).
Proof.
  introv H.
  unfold reduces_to, reduces_in_atmost_k_steps in H; exrepnd.
  revert H0 v.
  revert t u.
  induction k as [| k IHk ]; simpl; intros.
  - inversion H0; subst. left; auto.
  - remember (compute_at_most_k_steps lib k t).
    destruct c; try (complete (inversion H0)).
    assert (compute_at_most_k_steps lib k t = csuccess n) by auto.
    apply IHk with (v := v)  in H1; auto; sp.
    apply reduces_to_split2 in r; sp; subst.
    right; apply reduces_to_if_step; auto.
    rewrite H0 in p0; inversion p0; subst.
    left; auto.
    right; apply @reduces_to_if_split1 with (u := n); auto.
Qed.

Lemma reduces_to_if_value {p} :
  forall lib (t u : @NTerm p),
    reduces_to lib t u
    -> isvalue t
    -> t = u.
Proof.
 unfold reduces_to, reduces_in_atmost_k_steps; introv Hc Hisv; exrepnd.
 apply @compute_on_value with (lib := lib) (k := k) in Hisv.
 rewrite Hisv in Hc0; inversion Hc0; auto.
Qed.

Lemma reduces_to_value_eq {p} :
  forall lib (t u v : @NTerm p),
    computes_to_value lib t v
    -> reduces_to lib t u
    -> computes_to_value lib u v.
Proof.
  unfold computes_to_value; introv Hcv Hcr. repnd.
  apply @reduces_to_or with (u := u) in Hcv0; auto.
  dorn Hcv0; auto.
  apply reduces_to_if_value in Hcv0; auto; subst.
  split; auto.
  apply reduces_to_symm.
Qed.

Lemma computes_to_valc_reduces_toc {p} :
  forall lib (a b v : @CTerm p),
  computes_to_valc lib a v
  -> reduces_toc lib a b
  -> computes_to_valc lib b v.
Proof.
  destruct a, b; unfold computes_to_valc, reduces_toc; allsimpl; sp.
  apply reduces_to_value_eq with (t := x); auto.
Qed.

Lemma reduces_to_exception_eq {p} :
  forall lib a (t u e : @NTerm p),
    computes_to_exception lib a t e
    -> reduces_to lib t u
    -> computes_to_exception lib a u e.
Proof.
  unfold computes_to_exception; introv Hcv Hcr. repnd.
  apply @reduces_to_or with (u := u) in Hcv; auto.
  dorn Hcv; auto.
  apply reduces_to_exception in Hcv; auto; subst; tcsp.
  apply reduces_to_symm.
Qed.


Lemma  compute_at_most_k_steps_trans {p} :
  forall lib n m a b c,
     compute_at_most_k_steps lib n a = csuccess b
  -> compute_at_most_k_steps lib m b = @csuccess p c
  -> compute_at_most_k_steps lib (n+m) a = csuccess c.
Proof.  intros ? ? ?. remember (n+m) as smn.
 generalize dependent m. generalize dependent n.
 revert smn. induction smn; intros  ? ? Heq  ? ? ? Hca Hcb.
 assert(m=0) by omega.  assert(n=0) by omega. subst. inverts Hca. inverts Hcb. auto.
 destruct m. inverts Hcb. rewrite Heq. assert (n+0=n) as H99  by omega .
 rewrite H99. auto.
 rewrite <- plus_n_Sm in Heq. inverts Heq. simpl in Hcb.
 simpl. remember (compute_at_most_k_steps lib m b) as ckb.
 destruct ckb as [tb | berr]; inverts Hcb.
 assert (compute_at_most_k_steps lib (n + m) a = csuccess tb) as Hnm.
   apply (IHsmn n m) with (b:=b); auto.
 rewrite Hnm; auto.
Qed.

Lemma reduces_in_atmost_k_steps_0 {p} :
  forall lib (t u : @NTerm p), reduces_in_atmost_k_steps lib t u 0 <=> t = u.
Proof.
  unfold reduces_in_atmost_k_steps; simpl; introv; split; intro k; subst; auto.
  inversion k; subst; auto.
Qed.

Lemma reduces_in_atmost_k_steps_S {p} :
  forall lib t v k,
    reduces_in_atmost_k_steps lib t v (S k)
    <=> {u : @NTerm p
        & compute_step lib t = csuccess u
        # reduces_in_atmost_k_steps lib u v k}.
Proof.
  introv.
  unfold reduces_in_atmost_k_steps.
  rw @compute_at_most_k_steps_eq_f.
  rw @compute_at_most_k_stepsf_S.
  remember (compute_step lib t); destruct c;
  try (rw <- @compute_at_most_k_steps_eq_f);
  split; intro comp; exrepnd.

  - exists n; sp.

  - inversion comp1; subst; GC; auto.

  - inversion comp.

  - inversion comp1.
Qed.

Lemma compute_at_most_k_steps_trans_exc {p} :
  forall lib en n m (a b c : @NTerm p),
    reduces_in_atmost_k_steps lib a b n
    -> computes_to_exception_in_max_k_steps lib en b c m
    -> computes_to_exception_in_max_k_steps lib en a c (n+m).
Proof.
  unfold computes_to_exception_in_max_k_steps.
  induction n; introv cn cm; allsimpl.

  - inversion cn; subst; simpl; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eapply IHn in cn0; eauto.
Qed.

Lemma reduces_to_computes_to_exception {p} :
  forall lib en (a b e : @NTerm p),
    reduces_to lib a b
    -> computes_to_exception lib en b e
    -> computes_to_exception lib en a e.
Proof.
  introv redto compex.
  allunfold @computes_to_exception; exrepnd.
  allunfold @reduces_to; exrepnd.
  generalize (compute_at_most_k_steps_trans_exc lib en k0 k a b e); intro h.
  unfold computes_to_exception_in_max_k_steps in h.
  repeat (autodimp h hyp); repnd; dands; auto.
  exists (k0 + k); sp.
Qed.

(* end hide *)
Lemma reduces_to_trans {p} :
  forall lib a b c, @reduces_to p lib a b -> reduces_to lib b c -> reduces_to lib a c.
Proof. intros ? ? ? ? Hrab Hrbc. allunfold @reduces_to.
 exrepnd. exists (k0+k). apply @compute_at_most_k_steps_trans with (b:=b); auto.
Qed.
(* begin hide *)

Lemma ispair_descriminate {p} :
  forall lib t v a b,
    @computes_to_value p lib t v
    -> if ispair v
       then reduces_to lib (mk_ispair t a b) a
       else reduces_to lib (mk_ispair t a b) b.
Abort.

(*Lemma ispair_descriminate :
  forall t a b,
    hasvalue t
    -> texists v,
         computes_to_value t v
         # ((assert (ispair v) # reduces_to (mk_ispair t a b) a)
             [+] (! assert (ispair v) # reduces_to (mk_ispair t a b) b)).*)

(*
page 3 end
I think Howe means that when he says t1 R t2
 he means t1 (alpha_rel R) t2
*)

(* this is not true
Theorem close_under_comput_contains:
 forall (R:NTerm-> NTerm->Prop) (tl tr:NTerm),
    (R tl tr) -> (closed tl) -> (closed tr) ->
   (close_under_comput R) tl tr.
  intros. unfold close_under_comput.
  repeat (split;auto). intros.
*)

(*
Theorem closed_op :
 forall o lnt, closed (oterm o lnt)
 -> forall l, (LIn l lnt) -> closed l.
Proof.
 unfold closed. intros.
 simpl in H.
 remember (free_vars l) as lfree.
 destruct lfree. auto.
 apply flat_map_empty with (l:=l) in H.
 rewrite  Heqlfree. auto. auto.
Qed.

Theorem is_program1: forall t, 
  isprogram t -> exists o:Opid, exists lnt : list NTerm,
   t= oterm o lnt # forall l, LIn l  lnt ->   (closed l # nt_wf l) 
    # map num_bvars lnt = OpBindings o.
Proof.
 intros. inversion_clear H.
 destruct H1. inv_sub_clear H.
 exists o. exists lnt. split;auto.
 inv_sub_clear H1. intros.
 repeat( split; auto).
 apply closed_op with (l:=l) in H0; auto.
Qed.

*)



Theorem is_program_ot_subst1 {p} :
  forall o nt1 bts nt1r,
    @isprogram p (oterm o ((bterm [] nt1):: bts))
    -> (isprogram nt1r)  -> isprogram (oterm o ((bterm [] nt1r):: bts)).
Proof. intros ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. unfold closed in Hclos. simpl in Hclos.
    apply app_eq_nil in Hclos. repnd.  rewrite remove_var_nil in Hclos0.
    inverts Hispst as Hclosst Hispst. unfold closed in Hclosst.
    rewrite remove_var_nil. rewrite Hclosst. rewrite Hclos. split;auto.
    inverts Hisp. constructor;auto. 
    intros ? Hin. inverts Hin. constructor; auto.
    apply X. right; auto.
Qed.
(*
Theorem is_program_ot_fst_bnd1: forall  v o nt1 bts, isprogram (oterm o ((bterm [v] nt1):: bts))
   -> nt_wf nt1.
Proof. intros ? ? ? ? Hisp. apply isprogram_ot_iff in Hisp. repnd.
  assert (isprogram_bt (bterm [v] nt1)) by (apply Hisp; left;auto).
  inversion H. inversion H1; auto.
Qed.
*)    
Theorem  isp_can_form_test_step {p} : forall ct cc nt1 nt2,
   (isprogram nt1) -> (@isprogram p nt2)
   -> isprogram (compute_step_canonical_form_test ct cc nt1 nt2).
Proof.
 intros. unfold compute_step_canonical_form_test.
 destruct(canonical_form_test_for ct cc); auto.
Qed.



Tactic Notation "destructarg1bt1" ident(btsarg1) ident(Hcomp):=
            destruct btsarg1 as [| arg1bt1 arg1bts]; inverts Hcomp as Hcomp;
            destruct arg1bt1 as [arg1bt1vs arg1bt1b];
            destruct arg1bt1vs as [| arg1bt1v1]; inverts Hcomp as Hcomp;
            try(destruct arg1bt1vs as [| arg1bt1v2]; inverts Hcomp as Hcomp);
            destruct arg1bts as [|arg1bt2]; inverts Hcomp as Hcomp.

Tactic Notation "destructarg1bt2" ident(arg1bt2) ident(arg1bts) ident(Hcomp) :=
            destruct arg1bt2 as [arg1bt2vs arg1bt2b];
            destruct arg1bt2vs as [| arg1bt2v1]; inverts Hcomp as Hcomp;
            try(destruct arg1bt2vs as [| arg1bt2v2]; inverts Hcomp as Hcomp);
            destruct arg1bts as [|arg1bt2]; inverts Hcomp as Hcomp.


Lemma compute_step_apply_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_apply arg1c t arg1bts bstr = csuccess u
    -> {v : NVar
        & {b, arg : @NTerm p
        $ arg1c = NLambda
        # arg1bts = [bterm [v] b]
        # bstr = [bterm [] arg]
        # u = subst b v arg}}
      [+] {f : nseq
           & {arg : NTerm
           & arg1c = Nseq f
           # arg1bts = []
           # bstr = [bterm [] arg]
           # u = mk_eapply (mk_nseq f) arg}}.
Proof.
  introv e; allsimpl; destruct arg1c; destruct arg1bts; allsimpl; inversion e;
  thin_trivials.
  - destruct b; destruct l.
    inversion e.
    destruct l; try (complete (inversion e)).
    destruct arg1bts; try (complete (inversion e)).
    destruct bstr; try (complete (inversion e)).
    destruct b; destruct l; try (complete (inversion e)).
    destruct bstr; inversion e.
    left.
    exists n0 n n1; sp.
  - destruct bstr; ginv.
    destruct b.
    destruct l; ginv.
    destruct bstr; ginv.
    right.
    exists n n0; sp.
Qed.

(*
Lemma compute_step_apseq_success {o} :
  forall f arg1c (t : @NTerm o) arg1bts bstr u,
    compute_step_apseq f arg1c t arg1bts bstr = csuccess u
    -> {n : nat
        & arg1c = Nint (Z.of_nat n)
        # arg1bts = []
        # bstr = []
        # u = mk_nat (f n)}.
Proof.
  introv e; allsimpl; destruct arg1c; destruct arg1bts; allsimpl; inversion e;
  thin_trivials.
  destruct bstr; ginv.
  boolvar; ginv.
  eexists; dands; eauto.
  rw Znat.Z2Nat.id; auto.
Qed.
 *)

Lemma compute_step_fix_success {p} :
  forall t arg1 bstr u,
    compute_step_fix t arg1 bstr = @csuccess p u
    -> (bstr = [] # u = mk_apply arg1 t).
Proof.
  introv e; destruct bstr; auto; simpl in e; inversion e; sp.
Qed.

Lemma compute_step_spread_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_spread arg1c t arg1bts bstr = csuccess u
    -> {a, b : NTerm $ {va, vb: NVar $ {arg : @NTerm p
        $ arg1c = NPair
         # arg1bts = [bterm [] a, bterm [] b]
         # bstr = [bterm [va,vb] arg]
         # u = lsubst arg [(va,a),(vb,b)] }}}.
Proof.
  intros. destruct arg1c, arg1bts; inversion H.
  destruct b; destruct l; destruct arg1bts.
  inversion H1.
  destruct b; destruct l; destruct arg1bts; destruct bstr; inversion H1; thin_trivials.
  allsimpl. destruct b; destruct l; inversion H; thin_trivials.
  destruct l.
  inversion H.
  destruct l; destruct bstr; inversion H; subst.
  exists n n0 n2 n3 n1; sp.
  inversion H1.
  inversion H1.
Qed.

Lemma compute_step_dsup_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_dsup arg1c t arg1bts bstr = csuccess u
    -> {a, b : NTerm $ {va, vb: NVar $ {arg : @NTerm p $
         arg1c = NSup
         # arg1bts = [bterm [] a, bterm [] b]
         # bstr = [bterm [va,vb] arg]
         # u = lsubst arg [(va,a),(vb,b)] }}}.
Proof.
  intros. destruct arg1c, arg1bts; inversion H.
  destruct b; destruct l; destruct arg1bts.
  inversion H1.
  destruct b; destruct l; destruct arg1bts; destruct bstr; inversion H1; thin_trivials.
  allsimpl. destruct b; destruct l; inversion H; thin_trivials.
  destruct l.
  inversion H.
  destruct l; destruct bstr; inversion H; subst.
  exists n n0 n2 n3 n1; sp.
  inversion H1.
  inversion H1.
Qed.

Lemma compute_step_decide_success {p} :
  forall arg1c (t : @NTerm p) arg1bts bstr u,
    compute_step_decide arg1c t arg1bts bstr = csuccess u
    -> {d : NTerm & {v1 : NVar & {t1 : NTerm & {v2 : NVar & {t2 : NTerm
         $ arg1bts = [bterm [] d]
         # bstr = [bterm [v1] t1, bterm [v2] t2]
         # ((arg1c = NInj NInl # u = subst t1 v1 d)
            [+]
            (arg1c = NInj NInr # u = subst t2 v2 d)) }}}}}.
Proof.
  intros.
  destruct arg1c, arg1bts; inversion H.
  destruct b; destruct l; destruct arg1bts; destruct bstr; inversion H1; thin_trivials.
  allsimpl. destruct b; destruct l; inversion H; thin_trivials.
  destruct l; destruct bstr; inversion H; thin_trivials.
  destruct b; destruct l; inversion H; thin_trivials.
  destruct l; destruct bstr; inversion H; subst.
  exists n n1 n0 n3 n2; sp.
  destruct c; ginv.
Qed.

Lemma compute_step_cbv_success {p} :
  forall t arg1 bstr u,
    compute_step_cbv t arg1 bstr = csuccess u
    -> {v : NVar & {x : @NTerm p
        & bstr = [bterm [v] x]
        # u = subst x v arg1 }}.
Proof.
  intros. destruct bstr; inversion H.
  destruct b; destruct l; inversion H1; thin_trivials.
  allsimpl; destruct l; destruct bstr; inversion H; subst.
  exists n0 n; auto.
Qed.

Lemma compute_step_can_test_success {p} :
  forall top arg1c t arg1bts bstr u,
    compute_step_can_test top arg1c t arg1bts bstr = csuccess u
    -> {arg2nt, arg3nt : @NTerm p $
         bstr = [bterm [] arg2nt, bterm [] arg3nt]
         # u = if canonical_form_test_for top arg1c then arg2nt else arg3nt}.
Proof.
  intros. destruct bstr; inversion H.
  destruct b; destruct l; inversion H1; thin_trivials.
  allsimpl; destruct bstr; inversion H; subst; thin_trivials.
  destruct b; destruct l; destruct bstr; inversion H.
  exists n n0; auto.
Qed.

Lemma compute_step_try_catch {p} :
  forall lib a (e : @NTerm p) v b,
    compute_step lib (mk_try e a v b)
    = match e with
        | vterm x => cfailure compute_step_error_not_closed (mk_try e a v b)
        | sterm f => csuccess (mk_atom_eq a a e mk_bot)
        | oterm (Can _) _ => csuccess (mk_atom_eq a a e mk_bot)
        | oterm Exc bs =>
          match bs with
            | [bterm [] a', bterm [] x] => csuccess (mk_atom_eq a a' (subst b v x) e)
            | _ => cfailure inappropriate_args_to_catch (mk_try e a v b)
          end
        | oterm _ _ =>
          match compute_step lib e with
            | csuccess f => csuccess (mk_try f a v b)
            | cfailure str t => cfailure str t
          end
      end.
Proof.
  introv.
  destruct e as [x|f|op bs]; auto.
  dopid op as [can|ncan|exc|abs] Case; simpl; auto.
  csunf; simpl; auto.
Qed.

Lemma compute_step_try_success {p} :
  forall t arg1 bstr u,
    compute_step_try t arg1 bstr = csuccess u
    -> {a : NTerm
       & {v : NVar
       & {x : @NTerm p
       & bstr = [bterm [] a, bterm [v] x]
       # u = mk_atom_eq a a arg1 mk_bot }}}.
Proof.
  introv comp.
  destruct bstr; allsimpl; ginv.
  destruct b as [l z].
  destruct l as [|x l]; allsimpl; ginv.
  destruct bstr as [|w bstr]; allsimpl; ginv.
  destruct w as [l q].
  destruct l as [|x l]; allsimpl; ginv.
  destruct l as [|y l]; allsimpl; ginv.
  destruct bstr; ginv.
  eexists; eexists; eexists; dands; eauto.
Qed.

Lemma compute_step_catch_success {p} :
  forall nc t arg1bts bstr u,
    compute_step_catch nc t arg1bts bstr = csuccess u
    -> (nc = NTryCatch
        # {a : NTerm
           & {a' : NTerm
           & {v : NVar
           & {b : NTerm
           & {e : @NTerm p
           & bstr = [bterm [] a, bterm [v] b]
           # arg1bts = [bterm [] a', bterm [] e]
           # u = mk_atom_eq a a' (subst b v e) (oterm Exc arg1bts) }}}}})
       [+] (nc <> NTryCatch # u = oterm Exc arg1bts).
Proof.
  introv c.
  dopid_noncan nc Case; allsimpl;
  try (complete (inversion c; subst; right; dands; auto; intro k; inversion k)).
  destruct bstr; boolvar; ginv; subst;
  try (complete (right; dands; auto; intro k; inversion k; subst; sp)).
  destruct b; try (complete (inversion c)).
  destruct l; try (complete (inversion c)).
  destruct bstr; try (complete (inversion c)).
  destruct b; try (complete (inversion c)).
  destruct l; try (complete (inversion c)).
  destruct l; try (complete (inversion c)).
  destruct bstr; try (complete (inversion c)).
  destruct arg1bts; try (complete (inversion c)).
  destruct b; try (complete (inversion c)).
  destruct l; try (complete (inversion c)).
  destruct arg1bts; ginv.
  destruct b; try (complete (inversion c)).
  destruct l; try (complete (inversion c)).
  destruct arg1bts; ginv.
  left; dands; auto.
  repeat eexists.
Qed.

Lemma compute_step_ncompop_ncan1 {p} :
  forall lib comp nc ncbts rest,
    compute_step lib
      (oterm (NCan (NCompOp comp))
             (bterm [] (oterm (@NCan p nc) ncbts) :: rest))
    = match compute_step lib (oterm (NCan nc) ncbts) with
        | csuccess f => csuccess (oterm (NCan (NCompOp comp)) (bterm [] f :: rest))
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv.
  rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_ncompop_abs1 {p} :
  forall lib comp x ncbts rest,
    compute_step lib
      (oterm (NCan (NCompOp comp))
             (bterm [] (oterm (@Abs p x) ncbts) :: rest))
    = match compute_step_lib lib x ncbts with
        | csuccess f => csuccess (oterm (NCan (NCompOp comp)) (bterm [] f :: rest))
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv.
  rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_ncompop_ncan2 {p} :
  forall lib comp c cbts nc ncbts rest,
    compute_step lib
      (oterm (NCan (NCompOp comp))
             (bterm [] (oterm (Can c) cbts)
              :: bterm [] (oterm (@NCan p nc) ncbts)
              :: rest))
    = if co_wf comp c cbts
      then match compute_step lib (oterm (NCan nc) ncbts) with
             | csuccess f => csuccess (oterm (NCan (NCompOp comp))
                                             (bterm [] (oterm (Can c) cbts)
                                                    :: bterm [] f
                                                    :: rest))
             | cfailure str ts => cfailure str ts
           end
      else cfailure bad_args (oterm (NCan (NCompOp comp))
                                    (bterm [] (oterm (Can c) cbts)
                                           :: bterm [] (oterm (@NCan p nc) ncbts)
                                           :: rest)).
Proof.
  introv.
  rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_ncompop_abs2 {p} :
  forall lib comp c cbts x ncbts rest,
    compute_step lib
      (oterm (NCan (NCompOp comp))
             (bterm [] (oterm (Can c) cbts)
              :: bterm [] (oterm (@Abs p x) ncbts)
              :: rest))
    = if co_wf comp c cbts
      then match compute_step_lib lib x ncbts with
             | csuccess f => csuccess (oterm (NCan (NCompOp comp))
                                             (bterm [] (oterm (Can c) cbts)
                                                    :: bterm [] f
                                                    :: rest))
             | cfailure str ts => cfailure str ts
           end
      else cfailure bad_args (oterm (NCan (NCompOp comp))
                                    (bterm [] (oterm (Can c) cbts)
                                           :: bterm [] (oterm (@Abs p x) ncbts)
                                           :: rest)).
Proof.
  introv.
  rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_narithop_ncan1 {p} :
  forall lib ar nc ncbts rest,
    compute_step lib
      (oterm (NCan (NArithOp ar))
             (bterm [] (oterm (@NCan p nc) ncbts) :: rest))
    = match compute_step lib (oterm (NCan nc) ncbts) with
        | csuccess f => csuccess (oterm (NCan (NArithOp ar)) (bterm [] f :: rest))
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_narithop_abs1 {p} :
  forall lib ar x ncbts rest,
    compute_step lib
      (oterm (NCan (NArithOp ar))
             (bterm [] (oterm (@Abs p x) ncbts) :: rest))
    = match compute_step_lib lib x ncbts with
        | csuccess f => csuccess (oterm (NCan (NArithOp ar)) (bterm [] f :: rest))
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; rw @compute_step_eq_unfold; sp.
Qed.

Lemma compute_step_narithop_ncan2 {p} :
  forall lib ar c cbts nc ncbts rest,
    compute_step lib
      (oterm (NCan (NArithOp ar))
             (bterm [] (oterm (Can c) cbts)
              :: bterm [] (oterm (@NCan p nc) ncbts)
              :: rest))
    = if ca_wf c cbts
      then match compute_step lib (oterm (NCan nc) ncbts) with
             | csuccess f => csuccess (oterm (NCan (NArithOp ar))
                                             (bterm [] (oterm (Can c) cbts)
                                                    :: bterm [] f
                                                    :: rest))
             | cfailure str ts => cfailure str ts
           end
      else cfailure bad_args (oterm (NCan (NArithOp ar))
                                    (bterm [] (oterm (Can c) cbts)
                                           :: bterm [] (oterm (@NCan p nc) ncbts)
                                           :: rest)).
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma compute_step_narithop_abs2 {p} :
  forall lib ar c cbts x ncbts rest,
    compute_step lib
      (oterm (NCan (NArithOp ar))
             (bterm [] (oterm (Can c) cbts)
              :: bterm [] (oterm (@Abs p x) ncbts)
              :: rest))
    = if ca_wf c cbts
      then match compute_step_lib lib x ncbts with
             | csuccess f => csuccess (oterm (NCan (NArithOp ar))
                                             (bterm [] (oterm (Can c) cbts)
                                                    :: bterm [] f
                                                    :: rest))
             | cfailure str ts => cfailure str ts
           end
      else cfailure bad_args (oterm (NCan (NArithOp ar))
                                    (bterm [] (oterm (Can c) cbts)
                                           :: bterm [] (oterm (@Abs p x) ncbts)
                                           :: rest)).
Proof.
  introv; csunf; auto.
Qed.

Ltac gpdest x :=
  let o := fresh "o" in
  let p := fresh "p" in
  remember (get_param_from_cop x) as o;
    match goal with
      | [ H : o = get_param_from_cop x |- _ ] =>
        symmetry in H;
          destruct o as [p|];
          try (complete ginv);
          destruct p;
          try (complete ginv);
          try (apply get_param_from_cop_pki in H);
          try (apply get_param_from_cop_pks in H);
          try (apply get_param_from_cop_pka in H);
          try (subst x);
          try (complete ginv)
    end.

Lemma compute_step_sleep_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_sleep arg1c t arg1bts bstr = csuccess u
    -> {z : Z $
         arg1c = Nint z
         # arg1bts = []
         # bstr = []
         # u = @mk_axiom p}.
Proof.
  introv e.
  unfold compute_step_sleep in e.
  destruct arg1bts; try (complete (inversion e)).
  destruct bstr; try (complete (inversion e)).
  gpdest arg1c; ginv.
  exists z ; sp.
Qed.

Lemma compute_step_tuni_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_tuni arg1c t arg1bts bstr = csuccess u
    -> {n : nat $
         arg1c = Nint (Z.of_nat n)
         # arg1bts = []
         # bstr = []
         # u = @mk_uni p n}.
Proof.
  introv e.
  unfold compute_step_tuni in e.
  destruct arg1bts; try (complete (inversion e)).
  destruct bstr; try (complete (inversion e)).
  gpdest arg1c.
  boolvar; ginv.
  exists (Z.to_nat z); dands; auto.
  rw Znat.Z2Nat.id; auto.
Qed.

Lemma compute_step_minus_success {p} :
  forall arg1c t arg1bts bstr u,
    compute_step_minus arg1c t arg1bts bstr = csuccess u
    -> {z : Z $
         arg1c = Nint z
         # arg1bts = []
         # bstr = []
         # u = @mk_integer p (- z)}.
Proof.
  introv e.
  unfold compute_step_minus in e.
  destruct arg1bts; try (complete (inversion e)).
  destruct bstr; try (complete (inversion e)).
  gpdest arg1c; ginv.
  exists z; dands; auto.
Qed.

Lemma compute_step_lib_success {o} :
  forall (lib : @library o) oa1 bs u,
    compute_step_lib lib oa1 bs = csuccess u
    -> {oa2 : opabs
        & {vars : list sovar_sig
        & {rhs : SOTerm
        & {correct : correct_abs oa2 vars rhs
           & found_entry lib oa1 bs oa2 vars rhs correct
           # u = mk_instance vars bs rhs}}}}.
Proof.
  introv c.
  unfold compute_step_lib in c.
  remember (unfold_abs lib oa1 bs) as k; destruct k; inversion c; subst; GC.
  induction lib; allsimpl; try (complete (inversion Heqk)).
  remember (unfold_abs_entry a oa1 bs) as h; destruct h.
  - inversion Heqk; subst; GC.
    clear IHlib.
    destruct a; allsimpl.
    exists opabs vars rhs correct.
    unfold found_entry; simpl.
    destruct (matching_entry_deq oa1 opabs vars bs); repnd; inversion Heqh; dands; auto.
  - apply IHlib in Heqk; clear IHlib; exrepnd.
    exists oa2 vars rhs correct; dands; auto; subst.
    allunfold @found_entry; allsimpl; destruct a.
    allunfold @unfold_abs_entry.
    destruct (matching_entry_deq oa1 opabs vars0 bs); repnd; inversion Heqh; dands; auto.
Qed.

Lemma isprogram_compute_step_lib {o} :
  forall (lib : @library o) x bs t,
    isprogram (oterm (Abs x) bs)
    -> compute_step_lib lib x bs = csuccess t
    -> isprogram t.
Proof.
  introv isp comp.
  apply compute_step_lib_success in comp; exrepnd; subst.
  apply isprogram_subst_lib in comp0; auto.
  introv i.
  apply isprogram_ot_iff in isp; repnd; sp.
Qed.

Lemma compute_step_parallel_success {p} :
  forall arg1c (t : @NTerm p) arg1bts bstr u,
    compute_step_parallel arg1c t arg1bts bstr = csuccess u
    -> u = mk_axiom.
Proof.
  introv e; allsimpl.
  unfold compute_step_parallel in e; ginv; auto.
Qed.

(*
Lemma compute_step_lib_success_change_bs {o} :
  forall (lib : @library o) oa bs1 bs2 res,
    compute_step_lib lib oa bs1 = res
    -> map num_bvars bs1 = map num_bvars bs2
    -> compute_step_lib lib oa bs2 = res.
*)

Definition isnoncan_like {o} (t : @NTerm o) :=
  isnoncan t [+] isabs t.
Hint Unfold isnoncan_like.

Ltac rename_eq x y h :=
  match goal with
    | [ H : x = y |- _ ] => rename H into h
  end.

Definition found_atom {o} (sub : @atom_sub o) v a :=
  find_atom sub v = Some a.

Ltac fold_found_atom :=
  match goal with
    | [ H : find_atom ?s ?v = Some ?a |- _ ] =>
      fold (found_atom s v a) in H
  end.

Ltac fold_found_atoms := repeat fold_found_atom.

Ltac dest_find_atom a e :=
  fold_found_atoms;
  match goal with
    | [ H : find_atom _ _ = _ |- _ ] => fail 0
    | [ H : context[find_atom ?s ?v] |- _ ] =>
      remember (find_atom s v) as a;
        rename_eq a (find_atom s v) e;
        symmetry in e;
        destruct a as [a|];
        try (complete ginv)
  end;
  allunfold (@found_atom).

Lemma isvalue_like_sterm {o} :
  forall (f : @ntseq o), isvalue_like (sterm f).
Proof.
  introv.
  unfold isvalue_like; simpl; sp.
Qed.
Hint Resolve isvalue_like_sterm : slow.

Lemma compute_step_fresh_success {o} :
  forall lib nc x v vs (t : @NTerm o) bs comp a u,
    compute_step_fresh lib nc x v vs t bs comp a
    = csuccess u
    -> nc = NFresh
       # vs = []
       # bs = []
       # (
           (t = vterm v # u = x)
           [+]
           (isvalue_like t # u = pushdown_fresh v t)
           [+]
           {x : NTerm
            & isnoncan_like t
            # comp = csuccess x
            # u = mk_fresh v (subst_utokens x [(a,mk_var v)])}
         ).
Proof.
  introv c.
  unfold compute_step_fresh in c.
  destruct nc; allsimpl; ginv.
  destruct vs; allsimpl; ginv.
  destruct bs; allsimpl; ginv.
  dands; auto.
  destruct t as [v1|f1|op1 bs1]; ginv; allsimpl; auto.
  - boolvar; ginv; tcsp.
  - right; left.
    dands; eauto 3 with slow.
  - dopid op1 as [can1|ncan1|exc1|abs1] Case; ginv.
    + Case "Can".
      right; left; dands; eauto with slow.
    + Case "NCan".
      right; right.
      destruct comp; allsimpl; ginv.
      exists n; dands; tcsp.
    + Case "Exc".
      right; left; dands; eauto with slow.
    + Case "Abs".
      right; right.
      destruct comp; allsimpl; ginv.
      exists n; dands; tcsp.
Qed.

Lemma compute_step_ncan_bterm_cons_success {o} :
  forall lib nc v vs (t : @NTerm o) bs u,
    compute_step lib (oterm (NCan nc) (bterm (v :: vs) t :: bs))
    = csuccess u
    -> nc = NFresh
       # vs = []
       # bs = []
       # (
           (t = vterm v # u = mk_fresh v t)
           [+]
           (isvalue_like t # u = pushdown_fresh v t)
           [+]
           {x : NTerm
            & let a := get_fresh_atom t in
              isnoncan_like t
              # compute_step lib (subst t v (mk_utoken a)) = csuccess x
              # u = mk_fresh v (subst_utokens x [(a,mk_var v)])}
         ).
Proof.
  introv comp.
  rw @compute_step_eq_unfold in comp; allsimpl.
  apply compute_step_fresh_success in comp; sp; subst; sp.
  right; right.
  eexists; dands; eauto.
Qed.

(*
Definition get_markers_o {p} (o : @Opid p) : list marker :=
  match o with
    | Abs opabs => [opabs_name opabs]
    | _ => []
  end.

Fixpoint get_markers {p} (t : @NTerm p) : list marker :=
  match t with
    | vterm _ => []
    | sterm _ => []
    | oterm o bterms => (get_markers_o o) ++ (flat_map get_markers_b bterms)
  end
with get_markers_b {p} (bt : @BTerm p) : list marker :=
       match bt with
         | bterm _ t => get_markers t
       end.

Fixpoint get_markers_soterm {p} (t : @SOTerm p) : list marker :=
  match t with
    | sovar _ ts => flat_map get_markers_soterm ts
    | soterm o bs => (get_markers_o o) ++ (flat_map get_markers_sobterm bs)
  end
with get_markers_sobterm {p} (bt : @SOBTerm p) : list marker :=
       match bt with
         | sobterm _ t => get_markers_soterm t
       end.

Definition get_markers_entry {o} (entry : @library_entry o) :=
  match entry with
    | lib_abs opabs vars rhs correct => get_markers_soterm rhs
  end.

Definition get_markers_lib {o} (lib : @library o) :=
  flat_map get_markers_entry lib.

Definition get_markers_ce {o} (ce : @compenv o) :=
  get_markers_lib (ce_library ce).
*)

(*
Lemma compute_step_ncan_vterm_success {o} :
  forall lib ncan v (bs : list (@BTerm o)) u,
    compute_step lib (oterm (NCan ncan) (bterm [] (vterm v) :: bs))
    = csuccess u
    -> {a : get_patom_set o
        & find_atom (ce_atom_sub lib) v = Some a
        # (
            (ncan = NFix
             # bs = []
             # u = mk_apply (mk_utoken a) (mk_fix (mk_utoken a)))
            [+]
            {x : NVar
             & {b : NTerm
             & ncan = NCbv
             # bs = [bterm [x] b]
             # u = subst b x (mk_utoken a)}}
            [+]
            {x : NVar
             & {b : NTerm
             & {en : exc_name
             & ncan = NTryCatch en
             # bs = [bterm [x] b]
             # u = mk_utoken a}}}
            [+]
            {t1 : NTerm
             & {bs1 : list BTerm
             & bs = nobnd t1 :: bs1
             # ncan = NCompOp CompOpAtomeq
             # (
                 {t2 : NTerm
                  & {t3 : NTerm
                  & {a' : get_patom_set o
                  & bs1 = [nobnd t2, nobnd t3]
                  # (t1 = mk_utoken a'
                     [+] {v : NVar
                          & t1 = vterm v
                          # find_atom (ce_atom_sub lib) v = Some a'})
                  # ((a = a' # u = t2) [+] (a <> a' # u = t3))}}}
                 [+]
                 {x : NTerm
                  & compute_step lib t1 = csuccess x
                  # isnoncan_like t1
                  # u = oterm (NCan ncan) (nobnd (mk_utoken a) :: nobnd x :: bs1) }
                 [+]
                 (isexc t1 # u = t1)
               )}}
            [+]
            {t1 : NTerm
             & {t2 : NTerm
             & {x : CanonicalTest
             & ncan = NCanTest x
             # bs = [nobnd t1, nobnd t2]
             # ((x = CanIsuatom # u = t1) [+] (x <> CanIsuatom # u = t2))}}}
          )
       }.
Proof.
  introv comp.
  allsimpl.
  unfold compute_var in comp.
  dest_find_atom a e.
  exists a; dands; auto.
  dopid_noncan ncan Case;
    try (complete (allsimpl; ginv));
    try (complete (destruct bs; ginv)).

  - Case "NFix".
    allsimpl.
    apply compute_step_fix_success in comp; repnd; subst.
    left; auto.

  - Case "NCbv".
    allsimpl.
    apply compute_step_cbv_success in comp; exrepnd; subst.
    right; left.
    exists v0 x; auto.

  - Case "NTryCatch".
    allsimpl.
    apply compute_step_try_success in comp; exrepnd; subst.
    right; right; left.
    exists v0 x e0; auto.

  - Case "NCompOp".
    right; right; right; left.
    destruct bs; ginv; try (complete (allsimpl; boolvar; ginv)).
    destruct b as [l t].
    destruct l; ginv; try (complete (allsimpl; boolvar; ginv)).
    destruct t as [v1|op1 bs1]; try (complete (allsimpl; boolvar; ginv)).

    + allsimpl; boolvar; allsimpl; tcsp; GC; ginv.
      unfold compute_var in comp.
      dest_find_atom a' e'; allsimpl.
      unfold compute_step_comp in comp; allsimpl.
      destruct bs; ginv.
      destruct b as [l t].
      destruct l; ginv.
      destruct bs; ginv.
      destruct b as [l t2].
      destruct l; ginv.
      destruct bs; ginv.
      destruct c; ginv.
      exists (@vterm o v1) [nobnd t, nobnd t2]; dands; auto.
      left.
      exists t t2  a'; dands; boolvar; tcsp.
      right.
      exists v1; sp.

    + dopid op1 as [can1|ncan1|exc1|mrk1|abs1] SCase.

      * SCase "Can".
        allsimpl; boolvar; allsimpl; tcsp; GC; ginv.
        unfold compute_step_comp in comp.
        destruct bs1; allsimpl; ginv.
        destruct bs; allsimpl; ginv.
        destruct b as [l t1].
        destruct l; ginv.
        destruct bs; allsimpl; ginv.
        destruct b as [l t2].
        destruct l; ginv.
        destruct bs; allsimpl; ginv.
        destruct c; ginv.

        remember (get_str_from_cop can1) as g.
        symmetry in Heqg; destruct g; ginv.
        allapply @get_str_from_cop_ska; subst.

        exists (mk_utoken g) [nobnd t1, nobnd t2]; dands; auto.
        left.
        exists t1 t2 g; dands; boolvar; auto.

      * SCase "NCan".
        remember (compute_step lib (oterm (NCan ncan1) bs1)) as c1; ginv.
        destruct c1;
          try (complete (allsimpl; boolvar; allsimpl; tcsp; ginv;
                         rw <- Heqc1 in comp; allsimpl; ginv)).
        exists (oterm (NCan ncan1) bs1) bs; dands; auto.
        { simpl in comp; boolvar; ginv; destruct c; allsimpl; allsimpl; tcsp. }
        right; left.
        exists n; dands; auto.
        allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv; auto.

      * SCase "Exc".
        allsimpl; ginv; boolvar; allsimpl; tcsp; ginv.
        exists (oterm (Exc exc1) bs1) bs; dands; auto.
        { destruct c; allsimpl; allsimpl; tcsp. }

      * SCase "Mrk".
        allsimpl; ginv; boolvar; allsimpl; tcsp; ginv.

      * SCase "Abs".
        remember (compute_step lib (oterm (Abs abs1) bs1)) as c1; ginv.
        destruct c1; try (complete (allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv)).
        exists (oterm (Abs abs1) bs1) bs; dands; auto.
        { simpl in comp; boolvar; ginv; destruct c; allsimpl; allsimpl; tcsp. }
        right; left.
        exists n; dands; auto.
        allsimpl; boolvar; allsimpl; tcsp; ginv; rw <- Heqc1 in comp; allsimpl; ginv; auto.

  - Case "NArithOp".
    allsimpl; boolvar; allsimpl; tcsp; ginv.

  - Case "NCanTest".
    right; right; right; right.
    allsimpl.
    apply compute_step_can_test_success in comp; exrepnd; subst.
    exists arg2nt arg3nt c; dands; auto.
    destruct c; allsimpl; tcsp;
    try (complete (right; dands; auto; intro k; inversion k)).
Qed.
*)

(*
Lemma get_markers_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    subset (get_markers (lsubst_aux t sub))
           (get_markers t ++ flat_map get_markers (range sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "vterm".
    simpl.
    remember (sub_find sub v) as f; symmetry in Heqf; destruct f; simpl; auto.
    apply sub_find_some in Heqf.
    introv i.
    rw lin_flat_map.
    exists n; dands; auto.
    apply in_range_iff.
    exists v; sp.

  - Case "sterm".
    simpl; auto.

  - Case "oterm".
    simpl.
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    apply subset_flat_map; introv i.
    destruct x; simpl.
    pose proof (ind n l i (sub_filter sub l)) as h.
    introv k; apply h in k.
    allrw in_app_iff; dorn k.
    + left.
      rw lin_flat_map.
      exists (bterm l n); simpl; sp.
    + rw lin_flat_map in k; exrepnd.
      right.
      rw lin_flat_map.
      exists x0; dands; auto.
      apply in_range_iff in k1; exrepnd.
      apply in_sub_filter in k2; repnd.
      apply in_range_iff.
      exists v; sp.
Qed.

Lemma get_markers_swap {o} :
  forall (t : @NTerm o) s,
    get_markers (swap s t) = get_markers t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_markers_cswap {o} :
  forall (t : @NTerm o) s,
    get_markers (cswap s t) = get_markers t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma alpaheq_preserves_get_markers {o} :
  forall (t1 t2 : @NTerm o),
    alphaeq t1 t2
    -> get_markers t1 = get_markers t2.
Proof.
  nterm_ind1s t1 as [v|f ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "sterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    inversion aeq as [|?|? ? ? len imp]; subst; allsimpl.
    apply app_if; auto.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 c.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    simpl.
    applydup in_combine_sel_iff in c; exrepnd.
    pose proof (imp n) as k; autodimp k hyp.
    unfold selectbt in k.
    rw (nth_select1 n bs default_bt) in c3; auto.
    rw (nth_select1 n bts2 default_bt) in c1; auto; cpx.
    rw <- c3 in k.
    rw <- c1 in k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    apply (ind t1 _ l1) in a; auto.

    + allrw @get_markers_cswap; auto.

    + apply in_combine in c; sp.

    + rw @osize_cswap; eauto 3 with slow.
Qed.

Lemma get_markers_lsubst {o} :
  forall (t : @NTerm o) sub,
    subset (get_markers (lsubst t sub))
           (get_markers t ++ flat_map get_markers (range sub)).
Proof.
  introv.
  unfold lsubst; boolvar.
  - apply get_markers_lsubst_aux.
  - t_change t'.
    pose proof (get_markers_lsubst_aux t' sub) as k.
    introv i; apply k in i; allrw in_app_iff; dorn i; tcsp.
    left.
    pose proof (alpaheq_preserves_get_markers t t') as e; autodimp e hyp.
    + apply alphaeq_eq; auto.
    + rw e; sp.
Qed.
*)

Lemma nt_wf_subst {o} :
  forall (t : @NTerm o) v u,
    nt_wf t -> nt_wf u -> nt_wf (subst t v u).
Proof.
  introv wt wu.
  allrw @nt_wf_eq.
  unfold subst.
  apply lsubst_preserves_wf_term; eauto with slow.
Qed.

Lemma wf_term_subst {o} :
  forall (t : @NTerm o) v u,
    wf_term t -> wf_term u -> wf_term (subst t v u).
Proof.
  introv wt wu.
  unfold subst.
  apply lsubst_preserves_wf_term; eauto with slow.
Qed.

Lemma socovered_implies_remove_so_vars_nil {o} :
  forall (t : @SOTerm o) (sub : @SOSub o),
    socovered t (sodom sub)
    -> remove_so_vars (sodom sub) (so_free_vars t) = [].
Proof.
  introv cov.
  unfold socovered in cov.
  apply remove_so_vars_if_subsovars; auto.
Qed.

Lemma socovered_if_alphaeq_sosub {o} :
  forall (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    socovered t (sodom sub1)
    -> alphaeq_sosub sub1 sub2
    -> socovered t (sodom sub2).
Proof.
  introv cov aeq.
  apply alphaeq_sosub_implies_eq_sodoms in aeq.
  rw <- aeq; auto.
Qed.
Hint Resolve socovered_if_alphaeq_sosub : slow.

Lemma socovered_if_so_alphaeq {o} :
  forall (t1 t2 : @SOTerm o) (sub : @SOSub o),
    socovered t1 (sodom sub)
    -> so_alphaeq t1 t2
    -> socovered t2 (sodom sub).
Proof.
  introv cov aeq.
  apply so_alphaeq_preserves_free_vars in aeq.
  allunfold @socovered; rw <- aeq; auto.
Qed.
Hint Resolve socovered_if_so_alphaeq : slow.

Lemma subvars_free_vars_sosub_if_socovered {o} :
  forall (t : @SOTerm o) (sub : @SOSub o),
    socovered t (sodom sub)
    -> subvars (free_vars (sosub sub t))
               (free_vars_sosub sub).
Proof.
  introv cov.
  unfold sosub; boolvar.

  - pose proof (isprogram_sosub_aux_free_vars t sub) as h.
    rw @socovered_implies_remove_so_vars_nil in h; allsimpl; auto.

  - sosub_change sub'.
    applydup @alphaeq_sosub_preserves_free_vars in h as e.
    pose proof (isprogram_sosub_aux_free_vars t sub') as k.
    pose proof (socovered_if_alphaeq_sosub t sub sub') as s; repeat (autodimp s hyp).
    rw @socovered_implies_remove_so_vars_nil in k; allsimpl; auto.
    rw e; auto.

  - fo_change t'.
    pose proof (isprogram_sosub_aux_free_vars t' sub) as k.
    pose proof (socovered_if_so_alphaeq t t' sub) as cov'; repeat (autodimp cov' hyp).
    rw @socovered_implies_remove_so_vars_nil in k; allsimpl; auto.

  - fo_change t'.
    sosub_change sub'.
    applydup @alphaeq_sosub_preserves_free_vars in h1 as e.
    pose proof (isprogram_sosub_aux_free_vars t' sub') as k.
    pose proof (socovered_if_so_alphaeq t t' sub) as cov'; repeat (autodimp cov' hyp).
    pose proof (socovered_if_alphaeq_sosub t' sub sub') as cov''; repeat (autodimp cov'' hyp).
    rw @socovered_implies_remove_so_vars_nil in k; allsimpl; auto.
    rw e; auto.
Qed.

Lemma free_vars_sosub_mk_abs_subst {o} :
  forall (bs : list (@BTerm o)) vars,
    subvars (free_vars_sosub (mk_abs_subst vars bs))
            (flat_map free_vars_bterm bs).
Proof.
  induction bs; introv; allsimpl.
  - rw @mk_abs_subst_nil_r; simpl; auto.
  - destruct vars; simpl; auto.
    destruct s.
    destruct a.
    boolvar; simpl; subst; auto.
    apply subvars_app_lr; auto.
Qed.

Lemma subvars_free_vars_mk_instance {o} :
  forall vars bs (t : @SOTerm o),
    socovered t vars
    -> matching_bterms vars bs
    -> subvars (free_vars (mk_instance vars bs t))
               (flat_map free_vars_bterm bs).
Proof.
  introv cov m.
  unfold mk_instance.
  pose proof (subvars_free_vars_sosub_if_socovered
                t (mk_abs_subst vars bs)) as h.
  autodimp h hyp.
  - rw <- @mk_abs_subst_some_prop2; auto.
  - pose proof (free_vars_sosub_mk_abs_subst bs vars) as k.
    eapply subvars_trans; eauto.
Qed.

Lemma compute_step_compop_success_can_can {o} :
  forall c can1 can2 bs1 bs2 bs (t u : @NTerm o),
    compute_step_comp c can1 can2 bs1 bs2 bs t = csuccess u
    -> {t1 : NTerm
        & {t2 : NTerm
        & bs1 = []
        # bs2 = []
        # bs = [nobnd t1, nobnd t2]
        # (
            {n1 : Z
             & {n2 : Z
             & c = CompOpLess
             # get_param_from_cop can1 = Some (PKi n1)
             # get_param_from_cop can2 = Some (PKi n2)
             # u = if Z_lt_le_dec n1 n2 then t1 else t2}}
            [+]
            {pk1 : param_kind
             & {pk2 : param_kind
             & c = CompOpEq
             # get_param_from_cop can1 = Some pk1
             # get_param_from_cop can2 = Some pk2
             # u = if param_kind_deq pk1 pk2 then t1 else t2}}
          )}}.
Proof.
  introv comp.
  unfold compute_step_comp in comp.
  destruct bs1; ginv.
  destruct bs2; ginv.
  destruct bs; ginv.
  destruct b as [l1 t1].
  destruct l1; ginv.
  destruct bs; ginv.
  destruct b as [l2 t2].
  destruct l2; ginv.
  destruct bs; ginv.
  exists t1 t2; dands; auto.
  destruct c.

  - left.
    gpdest can1; gpdest can2.
    boolvar; ginv; eexists; eexists; dands; eauto; boolvar; tcsp; try omega.

  - right.
    gpdest can1; gpdest can2; ginv; boolvar; ginv; tcsp;
    eexists; eexists; dands; eauto; boolvar; ginv; tcsp.
Qed.

Lemma compute_step_arithop_success_can_can {o} :
  forall c can1 can2 bs1 bs2 bs (t u : @NTerm o),
    compute_step_arith c can1 can2 bs1 bs2 bs t = csuccess u
    -> bs1 = []
       # bs2 = []
       # bs = []
       # {n1 : Z
          & {n2 : Z
          & get_param_from_cop can1 = Some (PKi n1)
          # get_param_from_cop can2 = Some (PKi n2)
          # u = mk_integer (get_arith_op c n1 n2) }}.
Proof.
  introv comp.
  unfold compute_step_arith in comp.
  destruct bs1; ginv.
  destruct bs2; ginv.
  destruct bs; ginv.
  gpdest can1; gpdest can2; ginv; dands; auto.
  eexists; eexists; dands; eauto.
Qed.

(*
Definition get_markers_sosub {o} (sub : @SOSub o) :=
  flat_map get_markers_b (sorange sub).

Lemma subset_get_markers_lsubst_aux {o} :
  forall (t : @NTerm o) (sub : @Sub o),
    subset (get_markers (lsubst_aux t sub))
           (get_markers t ++ flat_map get_markers (range sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as f;
      symmetry in Heqf; destruct f;
      simpl; auto.

    apply sub_find_some in Heqf.
    introv i.
    rw lin_flat_map.
    exists n; dands; auto.
    apply in_range_iff; eexists; eauto.

  - Case "oterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    apply subset_flat_map; introv i; destruct x; simpl.
    pose proof (ind n l i) as h.
    introv k; apply h in k; allrw in_app_iff; dorn k.

    + left.
      rw lin_flat_map; eexists; dands; eauto.

    + right.
      allrw lin_flat_map; exrepnd.
      allrw @in_range_iff; exrepnd.
      allrw @in_sub_filter; repnd.
      exists x0; dands; auto.
      apply in_range_iff; exists v; auto.
Qed.

Lemma get_markers_apply_list {o} :
  forall ts (t : @NTerm o),
    get_markers (apply_list t ts)
    = get_markers t ++ flat_map get_markers ts.
Proof.
  induction ts; introv; allsimpl; allrw app_nil_r; auto.
  rw IHts; simpl; allrw app_nil_r; rw app_assoc; auto.
Qed.

Lemma subset_get_markers_sosub_aux {o} :
  forall (t : @SOTerm o) (sub : @SOSub o),
    subset (get_markers (sosub_aux sub t))
           (get_markers_soterm t ++ get_markers_sosub sub).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as f;
      symmetry in Heqf; destruct f.

    + destruct s; allsimpl.
      pose proof (subset_get_markers_lsubst_aux
                    n (combine l (map (sosub_aux sub) ts))) as h.
      introv k; apply h in k; allrw in_app_iff.
      applydup @sosub_find_some in Heqf; repnd.
      dorn k.

      * right.
        rw lin_flat_map.
        exists (bterm l n); dands; auto.
        apply in_sorange; simpl; exists v; auto.

      * allrw lin_flat_map; exrepnd.
        rw @range_combine in k1; allrw map_length; auto.
        allrw in_map_iff; exrepnd; subst.
        apply ind in k0; auto; allrw in_app_iff.
        dorn k0.

        {left; exists a; sp. }

        { right; allrw lin_flat_map; exrepnd; exists x0; sp. }

    + rw @get_markers_apply_list; simpl.
      rw flat_map_map; unfold compose.
      apply subset_flat_map; introv i.
      pose proof (ind x i sub) as h.
      introv k; apply h in k; allrw in_app_iff; dorn k; tcsp.
      left.
      apply lin_flat_map.
      exists x; sp.

  - Case "soterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    introv i.
    rw lin_flat_map in i; exrepnd.
    destruct x0; allsimpl.
    pose proof (ind s l i1 (sosub_filter sub (vars2sovars l))) as h;
      apply h in i0; clear h; allrw in_app_iff; dorn i0.

    + left; rw lin_flat_map; eexists; dands; eauto.

    + allrw lin_flat_map; exrepnd.
      allrw @in_sorange; exrepnd.
      destruct x0; allsimpl.
      allrw @in_sosub_filter; repnd.
      right.
      exists (bterm l0 n); dands; auto.
      apply in_sorange.
      exists v; simpl; auto.
Qed.

Definition get_markers_sk {o} (sk : @sosub_kind o) :=
  match sk with
    | sosk l t => get_markers t
  end.

Lemma get_markers_sosub_cons {o} :
  forall v sk (sub : @SOSub o),
    get_markers_sosub ((v,sk) :: sub)
    = get_markers_sk sk ++ get_markers_sosub sub.
Proof.
  introv.
  unfold get_markers_sosub; simpl.
  destruct sk; simpl; auto.
Qed.

Lemma alphaeq_sk_preserves_markers {o} :
  forall (sk1 sk2 : @sosub_kind o),
    alphaeq_sk sk1 sk2
    -> get_markers_sk sk1 = get_markers_sk sk2.
Proof.
  introv aeq.
  destruct sk1, sk2; allsimpl.
  unfold alphaeq_sk in aeq.
  pose proof (alpaheq_preserves_get_markers
                (oterm Exc [bterm l n])
                (oterm Exc [bterm l0 n0])) as h.
  simpl in h; allrw app_nil_r; apply h.
  constructor; simpl; tcsp.
  introv i.
  destruct n1; try omega.
  unfold selectbt; allsimpl; auto.
Qed.

Lemma alphaeq_sosub_preserves_markers {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> get_markers_sosub sub1 = get_markers_sosub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq; subst; clear aeq.
  allrw @get_markers_sosub_cons.
  rw (IHsub1 sub2); auto.
  f_equal.
  apply alphaeq_sk_preserves_markers; auto.
Qed.

Lemma get_markers_soterm_so_swap {o} :
  forall (t : @SOTerm o) s,
    get_markers_soterm (so_swap s t) = get_markers_soterm t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; auto.

  - Case "soterm".
    f_equal.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; auto.
    destruct x; allsimpl.
    eapply ind; eauto.
Qed.

Lemma so_alphaeq_preserves_markers {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> get_markers_soterm t1 = get_markers_soterm t2.
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1|op1 bs1 ind1] Case; introv aeq; allsimpl.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; clear aeq; allsimpl.
    apply eq_flat_maps_diff; auto.
    introv i; applydup imp in i as k.
    apply ind1 in k; auto.
    allapply in_combine; sp.

  - Case "soterm".
    inversion aeq as [|? ? ? len imp]; subst; clear aeq; allsimpl.
    apply f_equal.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    applydup imp in i as k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    applydup in_combine in i; repnd.
    pose proof (ind1 t1
                     (so_swap (mk_swapping l1 vs) t1)
                     l1) as h;
      repeat (autodimp h hyp); allrw @sosize_so_swap; auto.
    pose proof (h (so_swap (mk_swapping l2 vs) t2) a) as x; clear h.
    allrw @get_markers_soterm_so_swap; auto.
Qed.
*)

(*
Lemma alphaeq_preserves_markers {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_markers t1 = get_markers t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv aeq; allsimpl; auto.

  - Case "vterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "sterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply f_equal.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    applydup aeq0 in i as k.
    apply alphaeqbt_eq in k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    applydup in_combine in i; repnd.
    pose proof (ind1 t1
                     (cswap (mk_swapping l1 vs) t1)
                     l1) as h;
      repeat (autodimp h hyp); allrw @osize_cswap; eauto 3 with slow.
    pose proof (h (cswap (mk_swapping l2 vs) t2)) as x; clear h.
    apply alphaeq_eq in a.
    autodimp x hyp.
    allrw @get_markers_cswap; auto.
Qed.
*)

Lemma get_utokens_swap {o} :
  forall s (t : @NTerm o),
    get_utokens (swap s t) = get_utokens t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_utokens_cswap {o} :
  forall s (t : @NTerm o),
    get_utokens (cswap s t) = get_utokens t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

(*
Lemma subset_get_markers_sosub {o} :
  forall (t : @SOTerm o) (sub : @SOSub o),
    subset (get_markers (sosub sub t))
           (get_markers_soterm t ++ get_markers_sosub sub).
Proof.
  introv; unfold sosub; boolvar.

  - apply subset_get_markers_sosub_aux.

  - sosub_change sub'.
    pose proof (subset_get_markers_sosub_aux t sub') as k.
    introv i; apply k in i; allrw in_app_iff; dorn i; tcsp.
    right.
    apply alphaeq_sosub_preserves_markers in h; rw h; auto.

  - fo_change t'.
    pose proof (subset_get_markers_sosub_aux t' sub) as k.
    introv i; apply k in i; allrw in_app_iff; dorn i; tcsp.
    left.
    apply so_alphaeq_preserves_markers in h; rw h; auto.

  - fo_change t'.
    sosub_change sub'.
    pose proof (subset_get_markers_sosub_aux t' sub') as k.
    introv i; apply k in i; allrw in_app_iff; dorn i; tcsp.
    + left.
      apply so_alphaeq_preserves_markers in h; rw h; auto.
    + right.
      apply alphaeq_sosub_preserves_markers in h1; rw h1; auto.
Qed.

Lemma get_markers_sosub_mk_abs_subst {o} :
  forall (bs : list (@BTerm o)) vars,
    matching_bterms vars bs
    -> get_markers_sosub (mk_abs_subst vars bs)
       = flat_map get_markers_b bs.
Proof.
  introv m.
  unfold get_markers_sosub.
  rw @sorange_mk_abs_subst; auto.
Qed.

Lemma subset_get_markers_mk_instance {o} :
  forall vars bs (t : @SOTerm o),
    matching_bterms vars bs
    -> subset (get_markers (mk_instance vars bs t))
              (get_markers_soterm t ++ flat_map get_markers_b bs).
Proof.
  introv m; unfold mk_instance.
  pose proof (subset_get_markers_sosub t (mk_abs_subst vars bs)) as h.
  introv i; apply h in i; allrw in_app_iff; dorn i; tcsp.
  right.
  rw @get_markers_sosub_mk_abs_subst in i; auto.
Qed.

Lemma get_markers_if_found_entry {o} :
  forall lib oa1 bs oa2 vars (t : @SOTerm o) correct,
    found_entry lib oa1 bs oa2 vars t correct
    -> subset (get_markers_soterm t) (get_markers_lib lib).
Proof.
  induction lib; introv fe; allsimpl.
  - inversion fe.
  - unfold found_entry in fe; allsimpl; destruct a.
    boolvar; cpx.
    + inversion fe; subst; simpl.
      introv i; allrw in_app_iff; sp.
    + apply IHlib in fe; introv i; apply fe in i; allrw in_app_iff; sp.
Qed.
*)

Lemma eq_maps3 :
  forall (A B C : Type) (f : A -> B) (g  : C -> B) (la : list A) (lc : list C),
    length la = length lc
    -> (forall a c,  LIn (a,c) (combine la lc) -> f a = g c)
    -> map f la = map g lc.
Proof.
  induction la; destruct lc; introv len imp; allsimpl; tcsp; cpx.
  f_equal; auto.
Qed.

Lemma sosub_wf_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> sosub_wf sub1
    -> sosub_wf sub2.
Proof.
  induction sub1; destruct sub2; introv aeq sw; eauto with slow;
  inversion aeq as [| ? ? ? ? ? ask ass]; subst.
  destruct sk1, sk2.
  allrw @sosub_wf_cons; repnd; dands; auto.
  allrw <- @alphaeq_sk_iff_alphaeq_bterm.
  allrw @alphaeqbt_eq.
  apply alphaeqbt_preserves_wf in ask.
  allrw @bt_wf_eq.
  destruct ask as [ask1 ask2]; sp.
Qed.

Lemma wf_soterm_so_alphaeq {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> wf_soterm t1
    -> wf_soterm t2.
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1|op1 bs1 ind1] Case; introv aeq wf.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; clear aeq.
    allrw @wf_sovar.
    introv i.
    pose proof (combine_in_right _ _ ts2 ts1) as h.
    autodimp h hyp; try omega.
    pose proof (h t i) as k; clear h; exrepnd.
    applydup imp in k0.
    applydup in_combine in k0; repnd.
    applydup wf in k3.
    eapply ind1; eauto.

  - Case "soterm".
    inversion aeq as [|? ? ? len imp]; subst; clear aeq.
    allrw @wf_soterm_iff; repnd; dands; auto.

    + rw <- wf0.
      symmetry.
      apply eq_maps3; auto.
      introv i.
      applydup imp in i.
      inversion i0 as [? ? ? ? ? len1 len2 disj norep aeq]; subst; allsimpl; omega.

    + introv i.
      pose proof (combine_in_right _ _ bts2 bs1) as h.
      autodimp h hyp; try omega.
      pose proof (h (sobterm vs t) i) as k; clear h; exrepnd.
      applydup imp in k0.
      applydup in_combine in k0; repnd.
      inversion k1 as [? ? ? ? ? len1 len2 disj norep aeq]; subst; clear k1; allsimpl.
      applydup wf in k3.
      pose proof (ind1 t1 (so_swap (mk_swapping vs1 vs0) t1) vs1 k3) as h.
      autodimp h hyp; try (rw @sosize_so_swap); auto.
      pose proof (h (so_swap (mk_swapping vs vs0) t) aeq) as k; clear h.
      allrw <- @wf_soterm_so_swap; sp.
Qed.

Lemma wf_sosub {p} :
  forall (t : SOTerm) (sub : @SOSub p),
    wf_soterm t
    -> sosub_wf sub
    -> wf_term (sosub sub t).
Proof.
  introv wft wfs; simpl.
  pose proof (unfold_sosub sub t) as h; exrepnd; rw h1.

  apply isprogram_sosub_aux_wf; auto.

  - eapply wf_soterm_so_alphaeq; eauto.

  - eapply sosub_wf_alphaeq_sosub; eauto.
Qed.

Lemma sosub_wf_prop1 {o} :
  forall (sub : @SOSub o),
    sosub_wf sub
    <=>
    (forall b, LIn b (sorange sub) -> wf_bterm b).
Proof.
  induction sub; allsimpl; split; intro k; tcsp.
  - destruct a; destruct s; introv i; repndors; subst;
    allrw @sosub_wf_cons; repnd; auto.
    apply IHsub; auto.
  - destruct a; destruct s.
    allrw @sosub_wf_cons; dands; tcsp.
    + pose proof (k (bterm l n0)) as h; autodimp h hyp.
    + apply IHsub; sp.
Qed.

Lemma sosub_wf_mk_abs_subst {o} :
  forall vars (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> (forall b, LIn b bs -> wf_bterm b)
    -> sosub_wf (mk_abs_subst vars bs).
Proof.
  introv m imp.
  apply sosub_wf_prop1; introv i.
  rw @sorange_mk_abs_subst in i; auto.
Qed.

Lemma wf_mk_instance {o} :
  forall oa0 oa vars rhs (lib : @library o) bs correct,
    found_entry lib oa0 bs oa vars rhs correct
    -> (forall b, LIn b bs -> wf_bterm b)
    -> wf_term (mk_instance vars bs rhs).
Proof.
  introv f i.
  unfold correct_abs in correct; repnd.
  unfold mk_instance.
  apply wf_sosub; auto.
  apply sosub_wf_mk_abs_subst; auto.
  apply found_entry_implies_matching_entry in f.
  unfold matching_entry in f; repnd; auto.
Qed.

Lemma wf_exception_iff {p} :
  forall a (e : @NTerm p), wf_term (mk_exception a e) <=> (wf_term a # wf_term e).
Proof.
  introv; split; intro k.
  - allrw <- @nt_wf_eq.
    inversion k as [|?|? ? i eop]; subst; allsimpl.
    pose proof (i (nobnd e)) as h1; autodimp h1 hyp.
    pose proof (i (nobnd a)) as h2; autodimp h2 hyp.
    inversion h1; inversion h2; subst; auto.
  - apply wf_exception; sp.
Qed.

(*
Fixpoint get_markers_utok_sub {o} (sub : @utok_sub o) :=
  match sub with
    | [] => []
    | (_,t) :: s => get_markers t ++ get_markers_utok_sub s
  end.
*)

Definition wf_utok_sub {o} (sub : @utok_sub o) :=
  forall a t, LIn (a,t) sub -> wf_term t.

Lemma utok_sub_find_some {o} :
  forall (sub : @utok_sub o) a t,
    utok_sub_find sub a = Some t
    -> LIn (a,t) sub.
Proof.
  induction sub; simpl; tcsp; introv k.
  destruct a; boolvar; subst; ginv; tcsp.
Qed.

Lemma in_free_vars_utok_sub {o} :
  forall v (sub : @utok_sub o),
    LIn v (free_vars_utok_sub sub)
    <=> {a : get_patom_set o & {t : NTerm & LIn (a,t) sub # LIn v (free_vars t)}}.
Proof.
  induction sub; simpl; split; intro k; tcsp.
  - destruct a; allrw in_app_iff; repndors.
    + exists g n; tcsp.
    + rw IHsub in k; exrepnd.
      exists a t; sp.
  - exrepnd; repndors; cpx; allrw in_app_iff; tcsp.
    rw IHsub; right.
    exists a1 t; sp.
Qed.

(*
Lemma in_get_markers_utok_sub {o} :
  forall m (sub : @utok_sub o),
    LIn m (get_markers_utok_sub sub)
    <=> {a : get_patom_set o & {t : NTerm & LIn (a,t) sub # LIn m (get_markers t)}}.
Proof.
  induction sub; simpl; split; intro k; tcsp.
  - destruct a; allrw in_app_iff; repndors.
    + exists g n; tcsp.
    + rw IHsub in k; exrepnd.
      exists a t; sp.
  - exrepnd; repndors; cpx; allrw in_app_iff; tcsp.
    rw IHsub; right.
    exists a1 t; sp.
Qed.
*)

Definition free_vars_bterms {o} (bs : list (@BTerm o)) :=
  flat_map free_vars_bterm bs.

Lemma bterm_in_implies_subvars_free_vars {o} :
  forall l (t : @NTerm o) bs,
    LIn (bterm l t) bs
    -> subvars (free_vars t) (l ++ free_vars_bterms bs).
Proof.
  introv i.
  rw subvars_prop; introv j.
  rw in_app_iff.
  destruct (in_deq _ deq_nvar x l); tcsp.
  right.
  rw lin_flat_map.
  eexists; dands; eauto; simpl.
  rw in_remove_nvars; sp.
Qed.

Definition get_utok {o} (op : @Opid o) :=
  match op with
    | Can (NUTok a) => Some a
    | _ => None
  end.

Lemma get_utok_some {o} :
  forall (op : @Opid o) a,
    get_utok op = Some a
    -> op = Can (NUTok a).
Proof.
  introv e.
  dopid op as [can|ncan|exc|abs] Case; try (complete (allsimpl; sp)).
  destruct can; allsimpl; ginv; auto.
Qed.

Lemma subst_utokens_aux_oterm {o} :
  forall op bs (s : @utok_sub o),
    subst_utokens_aux (oterm op bs) s
    = match get_utok op with
        | Some a => subst_utok a (map (fun b => subst_utokens_aux_b b s) bs) s
        | None => oterm op (map (fun b => subst_utokens_aux_b b s) bs)
      end.
Proof.
  introv.
  dopid op as [can|ncan|exc|abs] Case; tcsp.
  destruct can; simpl; auto.
Qed.

Definition lsubst_bterms_aux {o} (bs : list (@BTerm o)) sub :=
  map (fun b => lsubst_bterm_aux b sub) bs.

Lemma fold_lsubst_bterms_aux {o} :
  forall (bs : list (@BTerm o)) sub,
    map (fun b => lsubst_bterm_aux b sub) bs
    = lsubst_bterms_aux bs sub.
Proof. sp. Qed.

Lemma lsubst_aux_oterm {o} :
  forall op bs (s : @Sub o),
    lsubst_aux (oterm op bs) s
    = oterm op (lsubst_bterms_aux bs s).
Proof. sp. Qed.

Lemma free_vars_subst_utokens_aux {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    subvars (free_vars (subst_utokens_aux t sub))
            (free_vars t ++ free_vars_utok_sub sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "vterm".
    simpl; allrw subvars_prop; simpl; introv k; repndors; tcsp.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f; simpl; eauto with slow.

      { apply utok_sub_find_some in Heqf.
        apply subvars_app_weak_r.
        rw subvars_prop; introv i.
        rw @in_free_vars_utok_sub.
        exists g n; sp. }

      { rw flat_map_map; unfold compose.
        apply subvars_flat_map; introv i.
        destruct x as [l t]; simpl.
        apply subvars_remove_nvars.
        eapply subvars_trans;[eapply ind; eauto|].
        apply subvars_app_l; dands; eauto with slow.
        eapply subvars_trans;[eapply bterm_in_implies_subvars_free_vars; eauto|].
        rw subvars_app_l; dands; eauto with slow.
      }

    + simpl; allrw flat_map_map; unfold compose.
      rw subvars_flat_map; intros x i; destruct x as [l t]; simpl.
      pose proof (ind t l i sub) as h.
      rw subvars_remove_nvars.
      eapply subvars_trans;[exact h|].
      rw subvars_app_l; dands; eauto with slow.
      rw subvars_prop; introv j; allrw in_app_iff.
      rw lin_flat_map.
      pose proof (in_deq _ deq_nvar x l) as p; destruct p; tcsp.
      left; left; eexists; dands; eauto; simpl.
      rw in_remove_nvars; sp.
Qed.

Lemma unfold_subst_utokens {o} :
  forall (sub : @utok_sub o) t,
    {t' : NTerm
     & alpha_eq t t'
     # disjoint (bound_vars t') (free_vars_utok_sub sub)
     # subst_utokens t sub = subst_utokens_aux t' sub}.
Proof.
  introv.
  unfold subst_utokens; boolvar.
  - exists t; dands; eauto with slow.
  - t_change t'; exists t'; dands; eauto with slow.
Qed.

Lemma free_vars_subst_utokens {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    subvars (free_vars (subst_utokens t sub))
            (free_vars t ++ free_vars_utok_sub sub).
Proof.
  introv.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0.
  apply alphaeq_preserves_free_vars in h1.
  rw h1.
  apply free_vars_subst_utokens_aux.
Qed.

(*
Definition get_markers_bs {o} (bs : list (@BTerm o)) :=
  flat_map get_markers_b bs.

Lemma bterm_in_implies_subset_get_markers {o} :
  forall l (t : @NTerm o) bs,
    LIn (bterm l t) bs
    -> subset (get_markers t) (get_markers_bs bs).
Proof.
  introv i j.
  rw lin_flat_map.
  eexists; dands; eauto; simpl.
Qed.

Lemma get_markers_subst_utokens_aux {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    subset (get_markers (subst_utokens_aux t sub))
           (get_markers t ++ get_markers_utok_sub sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "vterm".
    simpl; auto.

  - Case "sterm".
    simpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f; simpl; eauto with slow.

      { apply utok_sub_find_some in Heqf.
        apply subset_app_l.
        introv i.
        rw @in_get_markers_utok_sub.
        exists g n; sp. }

      { rw flat_map_map; unfold compose.
        apply subset_flat_map; introv i.
        destruct x as [l t]; simpl.
        eapply subset_trans;[eapply ind; eauto|].
        apply subset_app; dands; eauto with slow.
        apply subset_app_r.
        apply (bterm_in_implies_subset_get_markers l t); auto. }

    + simpl; try (apply subset_cons2); allrw flat_map_map; unfold compose.
      apply subset_app; dands; eauto with slow.
      rw subset_flat_map; intros x i; destruct x as [l t]; simpl.
      pose proof (ind t l i sub) as h.
      eapply subset_trans;[exact h|].
      rw subset_app; dands; eauto with slow.
      apply subset_app_r.
      apply subset_app_l.
      introv j; allrw in_app_iff.
      rw lin_flat_map; eexists; eauto.
Qed.

Lemma get_markers_subst_utokens {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    subset (get_markers (subst_utokens t sub))
           (get_markers t ++ get_markers_utok_sub sub).
Proof.
  introv.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0.
  apply alphaeq_preserves_markers in h1.
  rw h1.
  apply get_markers_subst_utokens_aux.
Qed.
*)

Lemma wf_oterm_iff {o} :
  forall (op : Opid) (bs : list (@BTerm o)),
    wf_term (oterm op bs)
    <=>
    (map num_bvars bs = OpBindings op
     # (forall b : BTerm, LIn b bs -> wf_bterm b)).
Proof.
  introv.
  rw @wf_term_eq.
  rw @nt_wf_oterm_iff.
  split; intro k; repnd; dands; auto; introv i; apply k in i;
  apply bt_wf_eq; auto.
Qed.

Lemma wf_bterm_iff {o} :
  forall l (t : @NTerm o),
    wf_bterm (bterm l t) <=> wf_term t.
Proof.
  introv.
  unfold wf_bterm, wf_term; simpl; sp.
Qed.

Lemma isprog_nout_iff {o} :
  forall (t : @NTerm o),
    isprog_nout t <=> (nt_wf t # closed t # noutokens t).
Proof.
  introv.
  unfold isprog_nout.
  rw @wf_term_eq.
  rw @no_vars_like_b_true_iff.
  split; sp.
Qed.

Lemma wf_sterm_iff {o} :
  forall (f : @ntseq o),
    wf_term (sterm f) <=> (forall n : nat, isprog_nout (f n)).
Proof.
  introv.
  split; intro h.
  - introv.
    apply wf_term_eq in h.
    inversion h as [|? imp|]; subst; clear h.
    pose proof (imp n) as h; repnd.
    apply isprog_nout_iff; sp.
  - apply wf_term_eq.
    constructor; introv.
    pose proof (h n) as q; clear h.
    apply isprog_nout_iff in q; sp.
Qed.

Lemma wf_subst_utokens_aux {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    wf_term t
    -> wf_utok_sub sub
    -> wf_term (subst_utokens_aux t sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv wt ws; auto.

  Case "oterm".
  rw @subst_utokens_aux_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

  + allapply @get_utok_some; subst; allsimpl.
    unfold subst_utok.
    remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f; simpl; eauto with slow.

    { apply utok_sub_find_some in Heqf.
      apply ws in Heqf; auto. }

    { allrw @wf_oterm_iff; allrw map_map; allunfold @compose; repnd; dands; auto.

      - rw <- wt0; apply eq_maps; introv i; destruct x as [l t]; simpl.
        unfold num_bvars; simpl; auto.

      - introv i.
        allrw in_map_iff; exrepnd; subst.
        destruct a as [l t]; simpl.
        apply wf_bterm_iff.
        eapply ind; eauto.
        apply wt in i1.
        apply wf_bterm_iff in i1; auto.
    }

  + simpl; allrw @wf_oterm_iff; repnd; allrw map_map; allunfold @compose; dands;
    try (complete (rw <- wt0; apply eq_maps; introv i; destruct x; simpl; tcsp)).
    introv i; rw in_map_iff in i; exrepnd; subst.
    destruct a; simpl.
    apply wf_bterm_iff.
    eapply ind; eauto.
    apply wt in i1; apply wf_bterm_iff in i1; auto.
Qed.

Lemma wf_subst_utokens {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    wf_term t
    -> wf_utok_sub sub
    -> wf_term (subst_utokens t sub).
Proof.
  introv wt ws.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0.
  apply wf_subst_utokens_aux; auto.
  apply alphaeq_preserves_wf in h1.
  allrw @wf_term_eq; rw h1; auto.
Qed.

Lemma subars_remove_nvars_lr :
  forall vs vs1 vs2,
    subvars vs1 vs2
    -> subvars (remove_nvars vs vs1) (remove_nvars vs vs2).
Proof.
  introv sv.
  allrw subvars_prop; introv i; allrw in_remove_nvars; repnd; dands; tcsp.
Qed.

(* !! MOVE everything about cl_sub to some substitution file *)
Definition cl_sub {p} (sub : @Substitution p) := sub_range_sat sub closed.

Lemma implies_cl_sub_filter {o} :
  forall (sub : @Sub o) l,
    cl_sub sub -> cl_sub (sub_filter sub l).
Proof.
  introv cl.
  allunfold @cl_sub.
  allunfold @sub_range_sat.
  introv i.
  apply in_sub_filter in i; repnd.
  apply cl in i0; sp.
Qed.
Hint Resolve implies_cl_sub_filter : slow.

Lemma lsubst_aux_trivial_cl {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> disjoint (dom_sub sub) (free_vars t)
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; introv cl disj; auto.

  - Case "vterm".
    allrw disjoint_singleton_r.
    remember (sub_find sub v) as f; symmetry in Heqf; destruct f; auto.
    apply sub_find_some in Heqf.
    apply in_dom_sub in Heqf; sp.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    f_equal.
    eapply ind; eauto.

    + apply implies_cl_sub_filter; auto.

    + rw <- @dom_sub_sub_filter.
      rw disjoint_flat_map_r in disj.
      apply disj in i; simpl in i.
      rw disjoint_remove_nvars_l; auto.
Qed.

Lemma lsubst_aux_trivial_cl2 {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> closed t
    -> lsubst_aux t sub = t.
Proof.
  introv clsub clt.
  apply lsubst_aux_trivial_cl; auto.
  rw clt; auto.
Qed.

Lemma cl_sub_nil {o} : @cl_sub o [].
Proof.
  unfold cl_sub, sub_range_sat; allsimpl; sp.
Qed.
Hint Resolve cl_sub_nil : slow.

Lemma cl_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    cl_sub ((v,t) :: sub) <=> (closed t # cl_sub sub).
Proof.
  unfold cl_sub, sub_range_sat; introv; split; intro k; repnd; dands; introv.
  - apply (k v); simpl; sp.
  - intro i; apply (k v0); simpl; sp.
  - intro i; simpl in i; dorn i; cpx.
    apply (k v0); auto.
Qed.

Lemma implies_cl_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    closed t
    -> cl_sub sub
    -> cl_sub ((v,t) :: sub).
Proof.
  introv clt cls.
  rw @cl_sub_cons; sp.
Qed.
Hint Resolve implies_cl_sub_cons : slow.

Lemma cl_sub_eq {p} :
  forall (sub : @Sub p),
    cl_sub sub <=> (forall t, LIn t (range sub) -> closed t).
Proof.
  induction sub; simpl; split; intro k; tcsp.

  - apply cl_sub_nil.

  - destruct a; apply cl_sub_cons in k; repnd.
    introv i; dorn i; subst; auto.
    rw IHsub in k; apply k in i; auto.

  - destruct a; apply cl_sub_cons; dands; auto.
    apply IHsub; introv i.
    apply k; sp.
Qed.

Lemma cl_sub_eq2 {p} :
  forall (sub : @Sub p),
    cl_sub sub <=> (forall v t, LIn (v,t) sub -> closed t).
Proof.
  induction sub; simpl; split; intro k; tcsp.
Qed.

Lemma free_vars_lsubst_aux_cl {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> free_vars (lsubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op lbt ind] Case; simpl; introv k; auto.

  - Case "vterm".
    remember (sub_find sub v) as f; destruct f; symmetry in Heqf; simpl.
    + apply sub_find_some in Heqf.
      rw @cl_sub_eq in k.
      assert (LIn n (range sub)) as i by (apply in_range_iff; eexists; eauto).
      apply k in i; rw i.
      symmetry.
      rw <- null_iff_nil.
      rw null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqf; sp.
    + apply sub_find_none2 in Heqf.
      symmetry.
      rw <- remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "sterm".
    allrw remove_nvars_nil_r; auto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    rw remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.

    rw remove_nvars_comm.

    apply ind with (sub := sub_filter sub l) in i; sp;
    [|apply implies_cl_sub_filter; auto].
    rw i; clear i.
    repeat (rw remove_nvars_app_l).
    apply remove_nvars_comb.
Qed.

Lemma cl_sub_implies_disjoint_bv_sub {o} :
  forall (sub : @Sub o) t,
    cl_sub sub -> disjoint_bv_sub t sub.
Proof.
  introv cl.
  unfold cl_sub in cl.
  unfold disjoint_bv_sub.
  allunfold @sub_range_sat.
  introv i.
  apply cl in i; rw i; auto.
Qed.

Lemma sub_free_vars_if_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub -> sub_free_vars sub = [].
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a; allrw @cl_sub_cons; repnd.
  rw IHsub; auto.
  rw cl0; auto.
Qed.

Lemma sub_free_vars_iff_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub <=> sub_free_vars sub = [].
Proof.
  induction sub; split; introv cl; allsimpl; auto.
  - apply cl_sub_nil.
  - destruct a; allrw @cl_sub_cons; repnd.
    apply IHsub in cl; rw cl; rw cl0; auto.
  - destruct a; allrw @cl_sub_cons.
    apply app_eq_nil_iff in cl; repnd.
    apply IHsub in cl; dands; auto.
Qed.

Lemma lsubst_oterm_cl_sub {o} :
  forall op bs (sub : @Sub o),
    cl_sub sub
    -> lsubst (oterm op bs) sub
       = oterm op (map (fun b => lsubst_bterm_aux b sub) bs).
Proof.
  introv cl.
  unfold lsubst.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp.
  provefalse; sp.
Qed.

Definition subst_bterm_aux {p} (b : @BTerm p) (v : NVar) (u : NTerm) : BTerm :=
  lsubst_bterm_aux b [(v,u)].

Lemma subst_oterm_cl_sub {o} :
  forall op bs v (t : @NTerm o),
    closed t
    -> subst (oterm op bs) v t
       = oterm op (map (fun b => subst_bterm_aux b v t) bs).
Proof.
  introv cl.
  unfold subst.
  rw @lsubst_oterm_cl_sub; eauto with slow.
Qed.

Lemma subst_aux_oterm {o} :
  forall op bs v (t : @NTerm o),
    subst_aux (oterm op bs) v t
    = oterm op (map (fun b => subst_bterm_aux b v t) bs).
Proof. sp. Qed.

Lemma sub_free_vars_app {o} :
  forall (s1 s2 : @Sub o),
    sub_free_vars (s1 ++ s2) = sub_free_vars s1 ++ sub_free_vars s2.
Proof.
  induction s1; introv; allsimpl; auto.
  destruct a; rw IHs1.
  rw app_assoc; auto.
Qed.

Lemma implies_cl_sub_app {o} :
  forall (s1 s2 : @Sub o),
    cl_sub s1
    -> cl_sub s2
    -> cl_sub (s1 ++ s2).
Proof.
  introv cl1 cl2.
  allrw @sub_free_vars_iff_cl_sub.
  rw @sub_free_vars_app.
  allrw; auto.
Qed.
Hint Resolve implies_cl_sub_app : slow.

Lemma cl_lsubst_aux_app_sub_filter {o} :
  forall (t : @NTerm o) s1 s2,
    lsubst_aux t (s1 ++ s2)
    = lsubst_aux t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.

  - Case "vterm".
    allrw @sub_find_app.
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto.
    rw @sub_find_sub_filter_eta; auto.
    apply sub_find_none_iff; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    allrw @sub_filter_app.
    rewrite (ind t l); eauto with slow.
    f_equal.
    rw <- @dom_sub_sub_filter.
    allrw <- @sub_filter_app_r.
    f_equal; f_equal.
    rw <- @sub_filter_app_as_remove_nvars.
    allrw @sub_filter_app_r.
    rw @sub_filter_swap; auto.
Qed.

Lemma cl_lsubst_app_sub_filter {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s2
    -> lsubst t (s1 ++ s2)
       = lsubst t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof.
  introv cl2.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_app.
  allrw (sub_free_vars_if_cl_sub s2); eauto with slow.
  allrw (sub_free_vars_if_cl_sub (sub_filter s2 (dom_sub s1))); eauto with slow.
  allrw app_nil_r.

  boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp));
  apply cl_lsubst_aux_app_sub_filter; auto.
Qed.

Lemma cl_lsubst_aux_app {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> lsubst_aux t (s1 ++ s2)
       = lsubst_aux (lsubst_aux t s1) s2.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl1 cl2; simpl; auto.

  - Case "vterm".
    allrw @sub_find_app.
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto.
    apply sub_find_some in Heqsf1.
    rw @lsubst_aux_trivial_cl2; auto.
    rw @cl_sub_eq2 in cl1.
    apply cl1 in Heqsf1; auto.

  - Case "oterm".
    f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    allrw @sub_filter_app.
    rewrite (ind t l); eauto with slow.
Qed.

Lemma cl_lsubst_app {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> lsubst t (s1 ++ s2)
       = lsubst (lsubst t s1) s2.
Proof.
  introv cl1 cl2.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp)).
  apply cl_lsubst_aux_app; auto.
Qed.

Lemma cl_lsubst_aux_swap {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> disjoint (dom_sub s1) (dom_sub s2)
    -> lsubst_aux (lsubst_aux t s1) s2
       = lsubst_aux (lsubst_aux t s2) s1.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl1 cl2 disj; simpl; auto.

  - Case "vterm".
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto;
    remember (sub_find s2 v) as sf2; symmetry in Heqsf2; destruct sf2; auto;
    simpl; allrw; allapply @sub_find_some; auto.
    + allapply @in_dom_sub.
      apply disj in Heqsf1; sp.
    + rw @lsubst_aux_trivial_cl2; auto.
      rw @cl_sub_eq2 in cl1.
      apply cl1 in Heqsf1; auto.
    + rw @lsubst_aux_trivial_cl2; auto.
      rw @cl_sub_eq2 in cl2.
      apply cl2 in Heqsf2; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    rewrite (ind t l); eauto with slow.
    allrw <- @dom_sub_sub_filter.
    apply disjoint_remove_nvars2; apply disjoint_sym.
    apply disjoint_remove_nvars2; apply disjoint_sym; auto.
Qed.

Lemma cl_lsubst_swap {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> disjoint (dom_sub s1) (dom_sub s2)
    -> lsubst (lsubst t s1) s2
       = lsubst (lsubst t s2) s1.
Proof.
  introv cl1 cl2 disj.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp)).
  apply cl_lsubst_aux_swap; auto.
Qed.

Lemma cl_lsubst_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub -> lsubst t sub = lsubst_aux t sub.
Proof.
  introv cl.
  apply lsubst_lsubst_aux.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma cl_subst_subst_aux {o} :
  forall (t : @NTerm o) v u,
    closed u -> subst t v u = subst_aux t v u.
Proof.
  introv cl.
  unfold subst, subst_aux.
  apply cl_lsubst_lsubst_aux; eauto with slow.
Qed.

Lemma closed_mk_utoken {o} :
  forall a, @closed o (mk_utoken a).
Proof. sp. Qed.
Hint Resolve closed_mk_utoken : slow.

Lemma subst_bterm_aux_nobnd {o} :
  forall (t : @NTerm o) v u,
    subst_bterm_aux (nobnd t) v u
    = nobnd (subst_aux t v u).
Proof. sp. Qed.

Lemma subst_bterm_aux_1bterm {o} :
  forall x (t : @NTerm o) v u,
    subst_bterm_aux (bterm [x] t) v u
    = if deq_nvar x v
      then bterm [x] t
      else bterm [x] (subst_aux t v u).
Proof.
  introv.
  unfold subst_bterm_aux; simpl; boolvar; allrw not_over_or; repnd; repndors;
  subst; tcsp.
  allrw @lsubst_aux_nil; auto.
Qed.

Lemma subst_aux_mk_var {o} :
  forall x v (u : @NTerm o),
    subst_aux (mk_var x) v u
    = if deq_nvar x v then u else mk_var x.
Proof.
  introv.
  unfold subst_aux; simpl; boolvar; tcsp.
Qed.

Lemma subst_aux_mk_utoken {o} :
  forall a v (u : @NTerm o),
    subst_aux (mk_utoken a) v u
    = mk_utoken a.
Proof. sp. Qed.

Lemma map_nil :
  forall A B (f : A -> B), map f [] = [].
Proof. sp. Qed.

(* !!MOVE to terms2 *)
Lemma isnoncan_implies {p} :
  forall t : @NTerm p,
    isnoncan t
    -> {c : NonCanonicalOp & {bterms : list BTerm & t = oterm (NCan c) bterms}}.
Proof.
  introv isc.
  destruct t; try (complete (inversion isc)).
  destruct o; try (complete (inversion isc)).
  exists n l; sp.
Qed.

(* !!MOVE to terms2 *)
Lemma isabs_implies {p} :
  forall t : @NTerm p,
    isabs t
    -> {abs : opabs & {bterms : list BTerm & t = oterm (Abs abs) bterms}}.
Proof.
  introv isc.
  destruct t; try (complete (inversion isc)).
  destruct o; try (complete (inversion isc)).
  exists o l; sp.
Qed.

Lemma compute_step_ncompop_ncanlike2 {p} :
  forall lib comp c cbts (t : @NTerm p) rest,
    isnoncan_like t
    -> compute_step
         lib
         (oterm (NCan (NCompOp comp))
                (bterm [] (oterm (Can c) cbts)
                       :: bterm [] t
                       :: rest))
       = if co_wf comp c cbts
         then match compute_step lib t with
                | csuccess f => csuccess (oterm (NCan (NCompOp comp))
                                                (bterm [] (oterm (Can c) cbts)
                                                       :: bterm [] f
                                                       :: rest))
                | cfailure str ts => cfailure str ts
              end
         else cfailure bad_args (oterm (NCan (NCompOp comp))
                                       (bterm [] (oterm (Can c) cbts)
                                              :: bterm [] t
                                              :: rest)).
Proof.
  introv isn.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    rw @compute_step_eq_unfold; sp.
  - apply isabs_implies in isn; exrepnd; subst.
    rw @compute_step_eq_unfold; sp.
Qed.

Lemma isnoncan_like_cl_lsubst {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> isnoncan_like t
    -> isnoncan_like (lsubst t sub).
Proof.
  introv cl isn.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    left.
    rw @lsubst_oterm_cl_sub; auto.
  - apply isabs_implies in isn; exrepnd; subst.
    right.
    rw @lsubst_oterm_cl_sub; auto.
Qed.

Lemma isnoncan_like_cl_subst {o} :
  forall (t : @NTerm o) v u,
    closed u
    -> isnoncan_like t
    -> isnoncan_like (subst t v u).
Proof.
  introv cl isn.
  unfold subst; apply isnoncan_like_cl_lsubst; eauto with slow.
Qed.
Hint Resolve isnoncan_like_cl_subst : slow.

(*
Lemma compute_step_ncompop_vterm_ncan2 {p} :
  forall lib v a nc ncbts rest,
    find_atom (ce_atom_sub lib) v = Some a
    -> compute_step lib
                    (oterm (NCan (NCompOp CompOpAtomeq))
                           (bterm [] (vterm v)
                                  :: bterm [] (oterm (@NCan p nc) ncbts)
                                  :: rest))
       = match compute_step lib (oterm (NCan nc) ncbts) with
           | csuccess f => csuccess (oterm (NCan (NCompOp CompOpAtomeq))
                                           (bterm [] (mk_utoken a)
                                                  :: bterm [] f
                                                  :: rest))
           | cfailure str ts => cfailure str ts
         end.
Proof.
  introv e.
  simpl.
  unfold compute_var; rw e; simpl; boolvar; allsimpl; ginv; tcsp.
Qed.

Lemma compute_step_ncompop_vterm_abs2 {p} :
  forall lib v a nc ncbts rest,
    find_atom (ce_atom_sub lib) v = Some a
    -> compute_step lib
                    (oterm (NCan (NCompOp CompOpAtomeq))
                           (bterm [] (vterm v)
                                  :: bterm [] (oterm (@Abs p nc) ncbts)
                                  :: rest))
       = match compute_step lib (oterm (Abs nc) ncbts) with
           | csuccess f => csuccess (oterm (NCan (NCompOp CompOpAtomeq))
                                           (bterm [] (mk_utoken a)
                                                  :: bterm [] f
                                                  :: rest))
           | cfailure str ts => cfailure str ts
         end.
Proof.
  introv e.
  simpl.
  unfold compute_var; rw e; simpl; boolvar; allsimpl; ginv; tcsp.
Qed.

Lemma compute_step_ncompop_vterm_ncanlike2 {p} :
  forall lib comp v a (t : @NTerm p) rest,
    isnoncan_like t
    -> find_atom (ce_atom_sub lib) v = Some a
    -> compute_step
         lib
         (oterm (NCan (NCompOp comp))
                (bterm [] (vterm v)
                       :: bterm [] t
                       :: rest))
       = if correct_comp_op comp (NUTok a)
         then match compute_step lib t with
                | csuccess f => csuccess (oterm (NCan (NCompOp comp))
                                                (bterm [] (mk_utoken a)
                                                       :: bterm [] f
                                                       :: rest))
                | cfailure str ts => cfailure str ts
              end
         else cfailure bad_args (oterm (NCan (NCompOp comp))
                                       (bterm [] (mk_utoken a)
                                              :: bterm [] t
                                              :: rest)).
Proof.
  introv isn fa.
  unfold isnoncan_like in isn; repndors.
  - apply isnoncan_implies in isn; exrepnd; subst.
    simpl; unfold compute_var; rw fa; simpl.
    boolvar; allsimpl; tcsp.
  - apply isabs_implies in isn; exrepnd; subst; sp.
    simpl; unfold compute_var; rw fa; simpl.
    boolvar; allsimpl; tcsp.
Qed.
*)

Fixpoint lsubst_aux_sub {p} (sub1 sub2 : @Sub p) : Sub :=
  match sub1 with
    | nil => nil
    | (v,t) :: sub => (v,lsubst_aux t sub2) :: lsubst_aux_sub sub sub2
  end.

Lemma sub_find_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o) v,
    sub_find (lsubst_aux_sub sub1 sub2) v
    = option_map (fun t => lsubst_aux t sub2) (sub_find sub1 v).
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; simpl; boolvar; auto.
Qed.

Lemma lsubst_aux_trivial_cl_term {p} :
  forall (t : @NTerm p) sub,
    disjoint (free_vars t) (dom_sub sub)
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; introv cl; auto.

  - Case "vterm".
    allrw disjoint_singleton_l.
    apply sub_find_none_iff in cl; rw cl; auto.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    f_equal.
    eapply ind; eauto.
    rw <- @dom_sub_sub_filter.
    rw disjoint_flat_map_l in cl.
    apply cl in i; simpl in i.
    apply disjoint_remove_nvars_l in i; auto.
Qed.

Lemma lsubst_aux_trivial_cl_term2 {p} :
  forall (t : @NTerm p) sub,
    closed t
    -> lsubst_aux t sub = t.
Proof.
  introv cl; apply lsubst_aux_trivial_cl_term.
  rw cl; auto.
Qed.

Lemma sub_filter_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o) l,
    sub_filter (lsubst_aux_sub sub1 sub2) l
    = lsubst_aux_sub (sub_filter sub1 l) sub2.
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; simpl; boolvar; simpl; tcsp.
  rw IHsub1; auto.
Qed.

Lemma lsubst_aux_sub_filter_range {o} :
  forall (sub1 sub2 : @Sub o) vs,
    disjoint vs (sub_free_vars sub1)
    -> lsubst_aux_sub sub1 sub2
       = lsubst_aux_sub sub1 (sub_filter sub2 vs).
Proof.
  induction sub1; introv disj; allsimpl; auto.
  destruct a.
  allrw disjoint_app_r; repnd.
  rw <- IHsub1; auto.
  f_equal.
  f_equal.
  rw @lsubst_aux_sub_filter; eauto with slow.
Qed.

Lemma subvars_sub_free_vars_sub_filter {o} :
  forall (sub : @Sub o) l,
    subvars (sub_free_vars (sub_filter sub l)) (sub_free_vars sub).
Proof.
  introv; rw subvars_prop; introv i.
  allrw @in_sub_free_vars_iff; exrepnd.
  apply in_sub_filter in i0; repnd.
  exists x0 t; sp.
Qed.

Lemma sub_filter_sub_filter_dom_sub {o} :
  forall (sub2 sub1 : @Sub o) l,
    sub_filter (sub_filter sub2 l) (dom_sub sub1)
    = sub_filter (sub_filter sub2 l) (dom_sub (sub_filter sub1 l)).
Proof.
  induction sub2; introv; simpl; auto.
  destruct a; boolvar; simpl; boolvar; simpl; tcsp.
  - provefalse.
    allrw <- @dom_sub_sub_filter.
    allrw in_remove_nvars; sp.
  - provefalse.
    allrw <- @dom_sub_sub_filter.
    allrw in_remove_nvars; sp.
  - rw IHsub2; auto.
Qed.

Lemma simple_lsubst_aux_lsubst_aux_sub {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> lsubst_aux (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                  (lsubst_aux_sub sub1 sub2)
       = lsubst_aux (lsubst_aux t sub1) sub2.
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case; introv clsub disj2.

  - Case "vterm".
    allsimpl.
    destruct (in_deq NVar deq_nvar x (dom_sub sub1)) as [i|i].

    + rw @sub_find_sub_filter; tcsp; simpl; boolvar; auto.
      rw @sub_find_lsubst_aux_sub.
      remember (sub_find sub1 x) as f; symmetry in Heqf; destruct f; simpl; auto.
      apply sub_find_none_iff in Heqf; sp.

    + applydup @sub_find_none_iff in i; rw i0; simpl.
      rw @sub_find_sub_filter_eta; simpl; tcsp.
      remember (sub_find sub2 x) as f; symmetry in Heqf; destruct f;
      simpl; boolvar; tcsp.

      * apply sub_find_some in Heqf.
        dup clsub as cl.
        rw @cl_sub_eq2 in clsub.
        applydup clsub in Heqf.
        apply lsubst_aux_trivial_cl_term2; auto.

      * rw @sub_find_lsubst_aux_sub; rw i0; simpl; auto.

  - Case "sterm".
    simpl; auto.

  - Case "oterm".
    simpl.
    allrw map_map; unfold compose.
    f_equal; apply eq_maps; introv i.

    destruct x; allsimpl.
    allrw disjoint_flat_map_l.
    applydup disj2 in i as j; simpl in j.
    rw disjoint_app_l in j; repnd.
    f_equal.

    rw @sub_filter_swap.
    rw @sub_filter_lsubst_aux_sub.
    rw (lsubst_aux_sub_filter_range (sub_filter sub1 l) sub2 l); auto;
    [| eapply subvars_disjoint_r;[|exact j0];
       apply subvars_sub_free_vars_sub_filter].
    rw @sub_filter_sub_filter_dom_sub.
    eapply ind; eauto.

    + apply implies_cl_sub_filter; auto.

    + eapply subvars_disjoint_r;[|exact j].
      apply subvars_sub_free_vars_sub_filter.
Qed.

Lemma cl_lsubst_sub_eq_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub2
    -> lsubst_sub sub1 sub2 = lsubst_aux_sub sub1 sub2.
Proof.
  induction sub1; introv cl; simpl; auto.
  destruct a; f_equal; tcsp.
  f_equal.
  rw @cl_lsubst_lsubst_aux; auto.
Qed.

Lemma flat_map_free_vars_range_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub -> flat_map free_vars (range sub) = [].
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a; allsimpl.
  rw @cl_sub_cons in cl; repnd.
  rw IHsub; auto.
  rw cl0; auto.
Qed.

Lemma lsubst_aux_alpha_congr_same_cl_sub {o} :
  forall (t1 t2 : @NTerm o) sub,
    alpha_eq t1 t2
    -> cl_sub sub
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub).
Proof.
  introv aeq cl.
  pose proof (sub_eta sub) as e.
  rw e; clear e.
  apply lsubst_aux_alpha_congr; auto.
  - rw @sub_eta_length; auto.
  - rw @sub_eta_length; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
Qed.

Lemma lsubst_aux_alpha_congr_same_disj {o} :
  forall (t1 t2 : @NTerm o) sub,
    alpha_eq t1 t2
    -> disjoint (bound_vars t1) (sub_free_vars sub)
    -> disjoint (bound_vars t2) (sub_free_vars sub)
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub).
Proof.
  introv aeq disj1 disj2.
  pose proof (sub_eta sub) as e.
  rw e; clear e.
  apply lsubst_aux_alpha_congr; auto.
  - rw @sub_eta_length; auto.
  - rw @sub_eta_length; auto.
  - rw <- @sub_free_vars_is_flat_map_free_vars_range; eauto with slow.
  - rw <- @sub_free_vars_is_flat_map_free_vars_range; eauto with slow.
  - unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
Qed.

Lemma eqvars_bound_vars_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    eqvars (bound_vars (lsubst_aux t sub))
           (bound_vars t ++ sub_bound_vars (sub_keep_first sub (free_vars t))).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf.
    + apply sub_keep_first_singleton_r_some in Heqsf; rw Heqsf; simpl.
      allrw app_nil_r; sp.
    + apply sub_keep_first_singleton_r_none in Heqsf; rw Heqsf; simpl; auto.

  - Case "sterm".
    rw @sub_keep_first_nil_r; simpl; auto.

  - Case "oterm".
    allrw flat_map_map; unfold compose.
    rw eqvars_prop; introv; split; intro i;
    allrw in_app_iff; allrw lin_flat_map; exrepnd.

    + destruct x0 as [l t].
      allsimpl.
      allrw in_app_iff.
      pose proof (ind t l i1 (sub_filter sub l)) as h; clear ind.
      destruct (in_deq NVar deq_nvar x l) as [d|d].

      * left; eexists; dands; eauto; simpl.
        rw in_app_iff; sp.

      * repndors; tcsp.
        rw eqvars_prop in h; apply h in i0; clear h.
        allrw in_app_iff; repndors.

        { left; eexists; dands; eauto; simpl.
          allrw in_app_iff; sp. }

        { right.
          allrw @sub_bound_vars_is_flat_map_bound_vars_range.
          allrw lin_flat_map; exrepnd.
          exists x0; dands; auto.
          allrw @in_range_iff; exrepnd.
          exists v.
          allrw @in_sub_keep_first; repnd.
          allrw @sub_find_sub_filter_some; repnd.
          dands; auto.
          rw lin_flat_map.
          eexists; dands; eauto; simpl.
          rw in_remove_nvars; sp. }

    + repndors; exrepnd.

      * destruct x0 as [l t]; allsimpl; allrw in_app_iff.
        pose proof (ind t l i1 (sub_filter sub l)) as h; clear ind.
        eexists; dands; eauto; allsimpl.
        allrw in_app_iff; repndors; tcsp.
        right.
        rw eqvars_prop in h; apply h; clear h.
        rw in_app_iff; sp.

      * allrw @sub_bound_vars_is_flat_map_bound_vars_range.
        allrw lin_flat_map; exrepnd.
        allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw lin_flat_map; exrepnd.
        destruct x1 as [l t]; allsimpl.
        eexists; dands; eauto; allsimpl.
        allrw in_app_iff; allrw in_remove_nvars; repnd.
        right.
        pose proof (ind t l i2 (sub_filter sub l)) as h; clear ind.
        rw eqvars_prop in h; apply h; clear h.
        rw in_app_iff.
        allrw @sub_bound_vars_is_flat_map_bound_vars_range.
        allrw lin_flat_map.
        right.
        exists x0; dands; auto.
        rw @in_range_iff.
        exists v.
        rw @in_sub_keep_first; dands; auto.
        allrw @sub_find_sub_filter_some; sp.
Qed.

Lemma disjoint_bound_vars_lsubst_aux {o} :
  forall (t t' : @NTerm o) sub vs,
    disjoint (bound_vars t') vs
    -> disjoint (bound_vars (lsubst_aux t sub)) vs
    -> alpha_eq t t'
    -> disjoint (bound_vars (lsubst_aux t' sub)) vs.
Proof.
  introv d1 d2 aeq.
  pose proof (eqvars_bound_vars_lsubst_aux t' sub) as h'.
  intros v i1 i2.
  rw eqvars_prop in h'; apply h' in i1; clear h'.
  allrw in_app_iff; repndors.

  - apply d1 in i1; sp.

  - pose proof (eqvars_bound_vars_lsubst_aux t sub) as h.
    apply disjoint_sym in d2; applydup d2 in i2.
    apply disjoint_sym in d1; applydup d1 in i2.
    destruct i0.
    rw eqvars_prop in h; apply h; clear h.
    rw in_app_iff.
    right.
    apply alphaeq_preserves_free_vars in aeq.
    rw aeq; auto.
Qed.

Lemma cl_sub_free_vars_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub2
    -> sub_free_vars (lsubst_aux_sub sub1 sub2)
       = remove_nvars (dom_sub sub2) (sub_free_vars sub1).
Proof.
  induction sub1; introv cl; simpl.
  - rw remove_nvars_nil_r; auto.
  - destruct a; simpl.
    rw remove_nvars_app_r.
    rw IHsub1; auto.
    f_equal.
    rw @free_vars_lsubst_aux_cl; auto.
Qed.

Lemma simple_lsubst_aux_lsubst_aux_sub_aeq2 {o} :
  forall (t t' : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> disjoint (bound_vars t') (sub_free_vars sub1)
    -> disjoint (bound_vars (lsubst_aux t (sub_filter sub2 (dom_sub sub1))))
                (sub_free_vars (lsubst_aux_sub sub1 sub2))
    -> alpha_eq t t'
    -> alpha_eq
         (lsubst_aux (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                     (lsubst_aux_sub sub1 sub2))
         (lsubst_aux (lsubst_aux t' sub1) sub2).
Proof.
  introv cl disj1 disj2 aeq.
  pose proof (simple_lsubst_aux_lsubst_aux_sub t' sub1 sub2 cl disj1) as h.
  rw <- h; clear h.
  pose proof (lsubst_aux_alpha_congr_same_cl_sub
                t t'
                (sub_filter sub2 (dom_sub sub1))
                aeq) as a.
  autodimp a hyp; eauto with slow.
  apply lsubst_aux_alpha_congr_same_disj; auto.
  apply (disjoint_bound_vars_lsubst_aux t); auto.
  rw @cl_sub_free_vars_lsubst_aux_sub; auto.
  apply disjoint_remove_nvars_l.
  apply disjoint_remove_nvars2; auto.
Qed.
Lemma subvars_d :
  forall vs1 vs2, decidable (subvars vs1 vs2).
Proof.
  introv.
  unfold decidable, subvars, assert.
  destruct (sub_vars vs1 vs2); sp.
  right; sp.
Defined.

Fixpoint bound_vars_ncl {p} (t : @NTerm p) : list NVar :=
  match t with
    | vterm v => []
    | sterm f => []
    | oterm op bts => flat_map bound_vars_bterm_ncl bts
  end
 with bound_vars_bterm_ncl {p} (bt : BTerm) :=
  match bt with
  | bterm lv nt =>
    if subvars_d (free_vars nt) lv
    then []
    else lv ++ bound_vars_ncl nt
  end.

Definition alphaeq_op {o} (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => alphaeq t1 t2
    | None, None => True
    | _, _ => False
  end.

Lemma alphaeq_sub_sub_find {o} :
  forall (sub1 sub2 : @Sub o) v,
    alphaeq_sub sub1 sub2
    -> alphaeq_op (sub_find sub1 v) (sub_find sub2 v).
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq as [|? ? ? ? ? aeqt aeqs]; subst; clear aeq.
  boolvar; tcsp.
Qed.

Lemma alphaeq_oterm_implies_combine {o} :
  forall op bs (t : @NTerm o),
    alphaeq (oterm op bs) t
    -> {bs' : list BTerm
        & t = oterm op bs'
        # length bs = length bs'
        # (forall b1 b2 : BTerm,
             LIn (b1, b2) (combine bs bs')
             -> alphaeqbt b1 b2)}.
Proof.
  introv aeq.
  apply alphaeq_eq in aeq.
  apply alpha_eq_oterm_implies_combine in aeq; exrepnd.
  exists bs'; dands; auto.
  introv i.
  apply aeq0 in i.
  apply alphaeqbt_eq; auto.
Qed.

Lemma alphaeq_oterm_combine {o} :
  forall op (bs1 bs2 : list (@BTerm o)),
    alphaeq (oterm op bs1) (oterm op bs2)
    <=>
    (length bs1 = length bs2
     # (forall b1 b2 : BTerm,
          LIn (b1, b2) (combine bs1 bs2) -> alphaeqbt b1 b2)).
Proof.
  introv.
  rw @alphaeq_eq.
  rw @alpha_eq_oterm_combine.
  split; intro k; exrepnd; dands; auto; introv i; apply k in i;
  apply alphaeqbt_eq; auto.
Qed.

Lemma alphaeqbt_all {o} :
  forall (b1 b2 : @BTerm o), alphaeqbt b1 b2 <=> (forall l, alphaeqbt_vs l b1 b2).
Proof.
  introv; split; intro k.
  - introv.
    pose proof (alphaeq_all (oterm Exc [b1]) (oterm Exc [b2])) as h.
    destruct h as [h1 h2].
    clear h2.

    autodimp h1 hyp.
    { constructor; simpl; tcsp.
      introv i; destruct n; allsimpl; cpx. }

    pose proof (h1 l) as h; clear h1.
    inversion h as [|?|? ? ? ? i]; subst; allsimpl; tcsp; GC.
    pose proof (i 0) as p; tcsp.

  - pose proof (k []); auto.
Qed.

Lemma swapbvars_remove_nvars :
  forall vs1 vs2 l vs,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> swapbvars (mk_swapping vs1 vs2) (remove_nvars l vs)
       = remove_nvars (swapbvars (mk_swapping vs1 vs2) l)
                      (swapbvars (mk_swapping vs1 vs2) vs).
Proof.
  induction vs; introv norep disj; simpl.
  - allrw remove_nvars_nil_r; simpl; auto.
  - allrw remove_nvars_cons_r; boolvar; tcsp; try (rw <- IHvs; auto); allsimpl; tcsp.
    + provefalse.
      allrw in_swapbvars.
      destruct Heqb0.
      exists a; sp.
    + provefalse.
      allrw in_swapbvars; exrepnd.
      apply swapvars_eq in Heqb1; auto; subst; tcsp.
Qed.

Lemma free_vars_swap {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars (swap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw flat_map_map; unfold compose.
  rw @swapbvars_flat_map.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  rw swapbvars_remove_nvars; auto.
  erewrite ind; eauto.
Qed.

Lemma free_vars_cswap {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars (cswap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw flat_map_map; unfold compose.
  rw @swapbvars_flat_map.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  rw swapbvars_remove_nvars; auto.
  erewrite ind; eauto.
Qed.

Lemma bound_vars_ncl_swap {o} :
  forall (t : @NTerm o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> bound_vars_ncl (swap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (bound_vars_ncl t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; allsimpl.
  rw @free_vars_swap; auto.
  boolvar; allsimpl; tcsp.

  - destruct n.
    allrw subvars_prop; introv j.
    pose proof (s (swapvar (mk_swapping vs1 vs2) x)) as h.
    autodimp h hyp.
    { allrw in_swapbvars.
      exists x; dands; auto. }
    allrw in_swapbvars; exrepnd.
    apply swapvars_eq in h0; subst; auto.

  - destruct n.
    allrw subvars_prop; introv j.
    allrw in_swapbvars; exrepnd; subst.
    applydup s in j1.
    eexists; dands; eauto.

  - rw swapbvars_app; f_equal.
    apply (ind t l); auto.
Qed.

Lemma bound_vars_ncl_cswap {o} :
  forall (t : @NTerm o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> bound_vars_ncl (cswap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (bound_vars_ncl t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; allsimpl.
  rw @free_vars_cswap; auto.
  boolvar; allsimpl; tcsp.

  - destruct n.
    allrw subvars_prop; introv j.
    pose proof (s (swapvar (mk_swapping vs1 vs2) x)) as h.
    autodimp h hyp.
    { allrw in_swapbvars.
      exists x; dands; auto. }
    allrw in_swapbvars; exrepnd.
    apply swapvars_eq in h0; subst; auto.

  - destruct n.
    allrw subvars_prop; introv j.
    allrw in_swapbvars; exrepnd; subst.
    applydup s in j1.
    eexists; dands; eauto.

  - rw swapbvars_app; f_equal.
    apply (ind t l); auto.
Qed.

Lemma sub_free_vars_swap_sub {o} :
  forall vs1 vs2 (sub : @Sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_free_vars (swap_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (sub_free_vars sub).
Proof.
  induction sub; introv norep disj; allsimpl; auto.
  destruct a.
  rw swapbvars_app; f_equal; tcsp.
  rw @free_vars_swap; auto.
Qed.

Lemma sub_free_vars_cswap_sub {o} :
  forall vs1 vs2 (sub : @Sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_free_vars (cswap_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (sub_free_vars sub).
Proof.
  induction sub; introv norep disj; allsimpl; auto.
  destruct a.
  rw swapbvars_app; f_equal; tcsp.
  rw @free_vars_cswap; auto.
Qed.

(*
Lemma lsubst_aux_alpha_congr_ncl {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    alphaeq t1 t2
    -> disjoint (sub_free_vars sub1) (bound_vars_ncl t1)
    -> disjoint (sub_free_vars sub2) (bound_vars_ncl t2)
    -> alphaeq_sub sub1 sub2
    -> alphaeq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv aeqt d1 d2 aeqs; allsimpl.

  - Case "vterm".
    inversion aeqt; subst; clear aeqt; allsimpl.
    remember (sub_find sub1 v1) as sf1; symmetry in Heqsf1.
    remember (sub_find sub2 v1) as sf2; symmetry in Heqsf2.
    applydup (alphaeq_sub_sub_find sub1 sub2 v1) in aeqs.
    rw Heqsf1 in aeqs0.
    rw Heqsf2 in aeqs0.
    destruct sf1, sf2; allsimpl; tcsp.
    apply alphaeq_refl.

  - Case "sterm".
    inversion aeqt; subst; simpl.
    constructor; auto.

  - Case "oterm".
    apply alphaeq_oterm_implies_combine in aeqt; exrepnd; subst; allsimpl.
    apply alphaeq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; cpx; allsimpl.

    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    allsimpl.
    applydup aeqt0 in i1.
    applydup in_combine in i1; repnd.
    disj_flat_map; allsimpl.

    rw @alphaeqbt_all in i0.
    pose proof (i0 (allvars (lsubst_aux t1 (sub_filter sub1 l1))
                            ++ allvars (lsubst_aux t2 (sub_filter sub2 l2))
                   )
               ) as h; clear i0.
    inversion h as [? ? ? ? ? len1 len2 disj norep a]; subst; clear h; allsimpl.
    allrw disjoint_app_r; repnd.

    apply (aeqbt _ vs); allsimpl; auto.

    { allrw disjoint_app_r; sp. }

    apply (alphaeq_vs_implies_less _ _ _ []) in a; auto.
    repeat (rw @lsubst_aux_cswap_cswap; eauto with slow).

    pose proof (ind1 t1 (cswap (mk_swapping l1 vs) t1) l1) as h; clear ind1.
    repeat (autodimp h hyp).
    { rw @osize_cswap; eauto 3 with slow. }

    pose proof (h (cswap (mk_swapping l2 vs) t2)
                  (cswap_sub (mk_swapping l1 vs) (sub_filter sub1 l1))
                  (cswap_sub (mk_swapping l2 vs) (sub_filter sub2 l2)))
      as k; clear h.
    repeat (autodimp k hyp).

    + rw @bound_vars_ncl_cswap; eauto with slow.
      rw @sub_free_vars_cswap_sub; eauto with slow.
      apply disjoint_swap; eauto with slow.
      clear i4.
      boolvar.

Abort.
 *)

Lemma in_sub_bound_vars_iff {o} :
  forall (sub : @Sub o) v,
    LIn v (sub_bound_vars sub)
    <=> {x : NVar $ {t : NTerm $
         LIn (x,t) sub # LIn v (bound_vars t)}}.
Proof.
  induction sub; simpl; sp.
  split; sp.
  rw in_app_iff.
  rw IHsub; split; sp; inj; sp.
  exists a0 a; sp.
  exists x t; sp.
  right; exists x t; sp.
Qed.

Lemma simple_lsubst_aux_lsubst_aux_sub_aeq3 {o} :
  forall (t u : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> disjoint (bound_vars u) (sub_free_vars (lsubst_aux_sub sub1 sub2))
    -> disjoint (sub_bound_vars sub2) (sub_free_vars sub1)
    -> alpha_eq u (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
    -> alpha_eq
         (lsubst_aux u (lsubst_aux_sub sub1 sub2))
         (lsubst_aux (lsubst_aux t sub1) sub2).
Proof.
  introv cl disj1 disj2 disj3 aeq.
  pose proof (simple_lsubst_aux_lsubst_aux_sub t sub1 sub2 cl disj1) as h.
  rw <- h; clear h.

  apply lsubst_aux_alpha_congr_same_disj; auto.
  rw @cl_sub_free_vars_lsubst_aux_sub; auto.

  intros v i1 i2.
  pose proof (eqvars_bound_vars_lsubst_aux t (sub_filter sub2 (dom_sub sub1))) as h.
  rw eqvars_prop in h; apply h in i1; clear h.
  allrw in_app_iff; allrw in_remove_nvars; repnd.
  repndors.

  - apply disj1 in i1; sp.

  - apply disjoint_sym in disj3; apply disj3 in i0.
    destruct i0.
    allrw @in_sub_bound_vars_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allrw @sub_find_sub_filter_some; repnd.
    exists x t0; dands; auto.
    apply sub_find_some in i4; auto.
Qed.

Lemma simple_lsubst_lsubst_sub_aeq3 {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> disjoint (sub_bound_vars sub2) (sub_free_vars sub1)
    -> alpha_eq
         (lsubst (lsubst t (sub_filter sub2 (dom_sub sub1)))
                 (lsubst_sub sub1 sub2))
         (lsubst (lsubst t sub1) sub2).
Proof.
  introv cl disj.

  rw (cl_lsubst_lsubst_aux t (sub_filter sub2 (dom_sub sub1))); eauto with slow.
  rw (cl_lsubst_lsubst_aux (lsubst t sub1) sub2); eauto with slow.
  rw (cl_lsubst_sub_eq_lsubst_aux_sub sub1 sub2); auto.

  pose proof (unfold_lsubst
                (lsubst_aux_sub sub1 sub2)
                (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))) as h.
  pose proof (unfold_lsubst sub1 t) as k.
  exrepnd.
  rw h0; rw k0.

  pose proof (lsubst_aux_alpha_congr_same_cl_sub
                t t'
                (sub_filter sub2 (dom_sub sub1))
                k1) as a.
  autodimp a hyp; eauto with slow.

  assert (alpha_eq t'0 (lsubst_aux t' (sub_filter sub2 (dom_sub sub1)))) as aeq.
  { eapply alpha_eq_trans;[|exact a]; eauto with slow. }

  clear dependent t.
  rename t'0 into u.
  rename t' into t.

  apply simple_lsubst_aux_lsubst_aux_sub_aeq3; auto.
Qed.

Lemma found_entry_lsubst_aux {o} :
  forall sub (oa0 oa : opabs) (vars : list sovar_sig)
         (rhs : @SOTerm o) (lib : library) (bs : list BTerm)
         (correct : correct_abs oa vars rhs),
    found_entry lib oa0 bs oa vars rhs correct
    -> found_entry lib oa0 (lsubst_bterms_aux bs sub) oa vars rhs correct.
Proof.
  introv fe.
  eapply found_entry_change_bs; eauto.
  unfold lsubst_bterms_aux; rw map_map.
  apply eq_maps; introv i.
  destruct x; simpl.
  unfold num_bvars, compose; simpl; auto.
Qed.

Lemma find_entry_implies_unfold_abs {o} :
  forall (lib : @library o) oa1 oa2 bs vars rhs correct,
    find_entry lib oa1 bs = Some (lib_abs oa2 vars rhs correct)
    -> unfold_abs lib oa1 bs = Some (mk_instance vars bs rhs).
Proof.
  induction lib; introv fe; allsimpl; tcsp.
  destruct a; allsimpl.
  destruct (matching_entry_deq oa1 opabs vars0 bs).
  - inversion fe; subst; GC; auto.
  - apply IHlib in fe; auto.
Qed.

Lemma found_entry_implies_compute_step_lib_success {o} :
  forall (lib : @library o) oa1 oa2 bs vars rhs correct,
    found_entry lib oa1 bs oa2 vars rhs correct
    -> compute_step_lib lib oa1 bs
       = csuccess (mk_instance vars bs rhs).
Proof.
  introv fe.
  unfold compute_step_lib.
  unfold found_entry in fe.
  apply find_entry_implies_unfold_abs in fe.
  rw fe; auto.
Qed.

Definition lsubst_aux_sk {o} (sub : @Sub o) (sk : @sosub_kind o) : sosub_kind :=
  bterm2sk (lsubst_bterm_aux (sk2bterm sk) sub).

Fixpoint lsubst_aux_sosub {o} (sub1 : @Sub o) (sub2 : @SOSub o) : @SOSub o :=
  match sub2 with
    | [] => []
    | (v,sk) :: rest => (v,lsubst_aux_sk sub1 sk) :: lsubst_aux_sosub sub1 rest
  end.

Fixpoint sub2sosub {o} (sub : @Sub o) : SOSub :=
  match sub with
    | [] => []
    | (v,t) :: rest => (v,sosk [] t) :: sub2sosub rest
  end.

Definition covered_sosub {o} (sub1 : @SOSub o) (sub2 : @Sub o) :=
  subvars (free_vars_sosub sub1) (dom_sub sub2).

Lemma cover_so_vars_sosub_change_bvars_alpha {o} :
  forall (t : @SOTerm o) (sub : @SOSub o) vars,
    cover_so_vars t sub
    <=> cover_so_vars t (sosub_change_bvars_alpha vars sub).
Proof.
  introv; unfold cover_so_vars.
  sosub_change s.
  allapply @alphaeq_sosub_implies_eq_sodoms; allrw; sp.
Qed.

Lemma implies_cover_so_vars_sosub_change_bvars_alpha {o} :
  forall (t : @SOTerm o) (sub : @SOSub o) vars,
    cover_so_vars t sub
    -> cover_so_vars t (sosub_change_bvars_alpha vars sub).
Proof.
  introv cov.
  apply cover_so_vars_sosub_change_bvars_alpha; auto.
Qed.

Ltac sub_change s :=
  match goal with
    | [ H : context[sub_change_bvars_alpha ?vs ?sub] |- _ ] =>
      let h := fresh "h" in
      pose proof (sub_change_bvars_alpha_spec vs sub) as h;
        simpl in h;
        remember (sub_change_bvars_alpha vs sub) as s;
        clear_eq s (sub_change_bvars_alpha vs sub);
        repnd
    | [ |- context[sub_change_bvars_alpha ?vs ?sub] ] =>
      let h := fresh "h" in
      pose proof (sub_change_bvars_alpha_spec vs sub) as h;
        simpl in h;
        remember (sub_change_bvars_alpha vs sub) as s;
        clear_eq s (sub_change_bvars_alpha vs sub);
        repnd
  end.

Lemma covered_sosub_sub_change_bvars_alpha {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vars,
    covered_sosub sub1 sub2
    <=> covered_sosub sub1 (sub_change_bvars_alpha vars sub2).
Proof.
  introv; unfold covered_sosub.
  sub_change s.
  allapply @alphaeq_sub_implies_eq_doms.
  allrw; sp.
Qed.

Lemma implies_covered_sosub_sub_change_bvars_alpha {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vars,
    covered_sosub sub1 sub2
    -> covered_sosub sub1 (sub_change_bvars_alpha vars sub2).
Proof.
  introv cov.
  apply covered_sosub_sub_change_bvars_alpha; auto.
Qed.

Lemma covered_sosub_sosub_change_bvars_alpha {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vars,
    covered_sosub sub1 sub2
    <=> covered_sosub (sosub_change_bvars_alpha vars sub1) sub2.
Proof.
  introv; unfold covered_sosub.
  sosub_change s.
  allapply @alphaeq_sosub_preserves_free_vars.
  allrw; sp.
Qed.

Lemma implies_covered_sosub_sosub_change_bvars_alpha {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vars,
    covered_sosub sub1 sub2
    -> covered_sosub (sosub_change_bvars_alpha vars sub1) sub2.
Proof.
  introv cov.
  apply covered_sosub_sosub_change_bvars_alpha; auto.
Qed.

Lemma implies_cl_sub_sub_change_bvars_alpha {o} :
  forall (sub : @Sub o) vars,
    cl_sub sub -> cl_sub (sub_change_bvars_alpha vars sub).
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a; allrw @cl_sub_cons; repnd; dands; auto.
  unfold closed; rw @free_vars_change_bvars_alpha; auto.
Qed.

Definition covered_sk {o} (sk : @sosub_kind o) (sub : @Sub o) :=
  subvars (free_vars_sk sk) (dom_sub sub).

Lemma covered_sosub_cons {o} :
  forall v sk (sub1 : @SOSub o) (sub2 : @Sub o),
    covered_sosub ((v,sk) :: sub1) sub2
    <=> (covered_sk sk sub2 # covered_sosub sub1 sub2).
Proof.
  introv; unfold covered_sosub, covered_sk; simpl.
  rw subvars_app_l; sp.
Qed.

Lemma null_eqvars :
  forall vs1 vs2,
    eqvars vs1 vs2
    -> null vs1
    -> null vs2.
Proof.
  introv eqv n.
  rw eqvars_prop in eqv.
  apply (null_subset _ vs2 vs1); auto.
  introv i; apply eqv in i; auto.
Qed.

Lemma free_vars_sosub_lsubst_aux_sosub_if_covered {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o),
    cl_sub sub2
    -> covered_sosub sub1 sub2
    -> free_vars_sosub (lsubst_aux_sosub sub2 sub1) = [].
Proof.
  induction sub1; introv cl cov; allsimpl; auto.
  destruct a; allsimpl.
  allrw @covered_sosub_cons; repnd.
  rw IHsub1; auto.
  destruct s; simpl.
  unfold covered_sk in cov0; allsimpl.
  rw subvars_remove_nvars in cov0; allrw app_nil_r.
  pose proof (eqvars_free_vars_disjoint_aux n0 (sub_filter sub2 l)) as h.
  autodimp h hyp.
  - introv i.
    apply in_sub_filter in i; repnd.
    rw @cl_sub_eq2 in cl.
    apply cl in i0; rw i0; sp.
  - rw <- @dom_sub_sub_filter in h.
    apply (eqvars_remove_nvars l l) in h; auto.
    rw <- null_iff_nil.
    apply eqvars_sym in h; apply null_eqvars in h; auto.
    rw remove_nvars_app_r.
    rw null_app; dands; clear h.
    + rw <- remove_nvars_comp.
      rw remove_nvars_app_l.
      apply null_remove_nvars; introv i.
      rw subvars_prop in cov0; apply cov0 in i.
      allrw in_app_iff; sp.
    + apply null_remove_nvars; introv i.
      apply in_sub_free_vars in i; exrepnd.
      apply in_sub_keep_first in i0; repnd.
      apply sub_find_some in i2.
      apply in_sub_filter in i2; repnd.
      rw @cl_sub_eq2 in cl.
      apply cl in i3.
      rw i3 in i1; allsimpl; sp.
Qed.

Lemma free_vars_sosub_sub2sosub_cl_sub {o} :
  forall sub : @Sub o,
    cl_sub sub
    -> free_vars_sosub (sub2sosub sub) = [].
Proof.
  induction sub; introv cl; allsimpl; cpx.
  destruct a.
  allrw @cl_sub_cons; repnd; simpl; rw remove_nvars_nil_l.
  rw cl0; simpl.
  rw IHsub; auto.
Qed.

Ltac rw_cl_sub_step :=
  match goal with
    | [ H : disjoint [] _ |- _ ] => clear H
    | [ H : disjoint _ [] |- _ ] => clear H
    | [ |- disjoint [] _ ] => complete auto
    | [ |- disjoint _ [] ] => complete auto

    | [ H1 : cl_sub ?s, H2 : context[free_vars_sosub (sub2sosub ?s)] |- _ ] =>
      rewrite (free_vars_sosub_sub2sosub_cl_sub s H1) in H2; simpl in H2
    | [ H : cl_sub ?s |- context[free_vars_sosub (sub2sosub ?s)] ] =>
      rewrite (free_vars_sosub_sub2sosub_cl_sub s H); simpl

    | [ H1 : cl_sub ?s, H2 : context[sub_free_vars ?s] |- _ ] =>
      rewrite (sub_free_vars_if_cl_sub s H1) in H2; simpl in H2
    | [ H : cl_sub ?s |- context[sub_free_vars ?s] ] =>
      rewrite (sub_free_vars_if_cl_sub s H); simpl

    | [ |- context[free_vars_sosub (lsubst_aux_sosub ?s2 ?s1)] ] =>
      rewrite (free_vars_sosub_lsubst_aux_sosub_if_covered s1 s2);
        [ simpl
        | auto; complete (repeat rw_cl_sub_step)
        | auto; complete (repeat rw_cl_sub_step)
        ]

    | [ H : context[free_vars_sosub (lsubst_aux_sosub ?s2 ?s1)] |- _ ] =>
      rewrite (free_vars_sosub_lsubst_aux_sosub_if_covered s1 s2) in H;
        [ simpl in H
        | clear H; auto; complete (repeat rw_cl_sub_step)
        | clear H; auto; complete (repeat rw_cl_sub_step)
        ]

    | [ |- cl_sub (sub_change_bvars_alpha ?vs ?s) ] =>
      apply (implies_cl_sub_sub_change_bvars_alpha s vs);
        auto;
        complete (repeat rw_cl_sub_step)
    | [ |- covered_sosub (sosub_change_bvars_alpha ?vs ?s1) ?s2 ] =>
      apply (implies_covered_sosub_sosub_change_bvars_alpha s1 s2 vs);
        auto;
        complete (repeat rw_cl_sub_step)
    | [ |- covered_sosub ?s1 (sub_change_bvars_alpha ?vs ?s2) ] =>
      apply (implies_covered_sosub_sub_change_bvars_alpha s1 s2 vs);
        auto;
        complete (repeat rw_cl_sub_step)
    | [ |- cover_so_vars ?t (sub_change_bvars_alpha ?vs ?s) ] =>
      apply (implies_cover_so_vars_sosub_change_bvars_alpha t s vs);
        auto;
        complete (repeat rw_cl_sub_step)
  end.

Ltac rw_cl_sub := repeat (rw_cl_sub_step; auto).

Lemma free_vars_sosub_app {o} :
  forall sub1 sub2 : @SOSub o,
    free_vars_sosub (sub1 ++ sub2)
    = free_vars_sosub sub1 ++ free_vars_sosub sub2.
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; allsimpl; rw IHsub1; rw app_assoc; auto.
Qed.

Lemma bound_vars_sosub_app {o} :
  forall sub1 sub2 : @SOSub o,
    bound_vars_sosub (sub1 ++ sub2)
    = bound_vars_sosub sub1 ++ bound_vars_sosub sub2.
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; allsimpl; rw IHsub1; rw app_assoc; auto.
Qed.

Lemma bound_vars_sosub_sub2sosub {o} :
  forall sub : @Sub o,
    bound_vars_sosub (sub2sosub sub) = sub_bound_vars sub.
Proof.
  induction sub; simpl; auto.
  destruct a; simpl; rw IHsub; auto.
Qed.

Lemma sosub_find_app {p} :
  forall v (sub1 sub2 : @SOSub p),
    sosub_find (sub1 ++ sub2) v
    = match sosub_find sub1 v with
        | Some t => Some t
        | None => sosub_find sub2 v
      end.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; boolvar; subst; auto.
Qed.

Lemma sosub_find_lsubst_aux_sosub {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) v,
    sosub_find (lsubst_aux_sosub sub2 sub1) v
    = match sosub_find sub1 v with
        | Some sk => Some (lsubst_aux_sk sub2 sk)
        | None => None
      end.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; simpl; boolvar; subst; auto.
Qed.

Lemma lsubst_aux_sub_combine {o} :
  forall vs (ts : list (@NTerm o)) sub,
    lsubst_aux_sub (combine vs ts) sub
    = combine vs (map (fun t => lsubst_aux t sub) ts).
Proof.
  induction vs; destruct ts; introv; simpl; auto.
  rw IHvs; auto.
Qed.

Lemma lsubst_aux_apply_list {o} :
  forall ts (t : @NTerm o) sub,
    lsubst_aux (apply_list t ts) sub
    = apply_list (lsubst_aux t sub) (map (fun t => lsubst_aux t sub) ts).
Proof.
  induction ts; introv; allsimpl; auto.
  rw IHts; simpl; allrw @sub_filter_nil_r; auto.
Qed.

Lemma sosub_find_sub2sosub {o} :
  forall (sub : @Sub o) v n,
    sosub_find (sub2sosub sub) (v,n)
    = if deq_nat n 0
      then match sub_find sub v with
             | Some t => Some (sosk [] t)
             | None => None
           end
      else None.
Proof.
  induction sub; introv; simpl; auto; try (destruct a);
  simpl; boolvar; auto; cpx; subst; cpx;
  rw IHsub; boolvar; tcsp.
Qed.

Lemma sosub_filter_app {o} :
  forall (sub1 sub2 : @SOSub o) vs,
    sosub_filter (sub1 ++ sub2) vs
    = sosub_filter sub1 vs ++ sosub_filter sub2 vs.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; boolvar; auto.
  rw IHsub1; auto.
Qed.

Lemma sosub_filter_lsubst_aux_sosub {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vs,
    sosub_filter (lsubst_aux_sosub sub2 sub1) vs
    = lsubst_aux_sosub sub2 (sosub_filter sub1 vs).
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; allsimpl; boolvar; allsimpl; auto.
  rw IHsub1; auto.
Qed.

Lemma sosub_filter_sub2sosub {o} :
  forall (sub : @Sub o) l,
    sosub_filter (sub2sosub sub) (vars2sovars l)
    = sub2sosub (sub_filter sub l).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; allsimpl; auto.
  - provefalse.
    destruct n1.
    apply in_map_iff; eexists; eauto.
  - provefalse.
    allrw in_map_iff; exrepnd; allunfold var2sovar; cpx.
  - rw IHsub; auto.
Qed.

Lemma subvars_free_vars_sosub_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    subvars (free_vars_sosub (sosub_filter sub vs))
            (free_vars_sosub sub).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; destruct s; allsimpl; boolvar; simpl; auto.
  - apply subvars_app_weak_r; auto.
  - apply subvars_app_lr; auto.
Qed.

Lemma lsubst_aux_sosub_sub_filter_if_disjoint {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) l,
    disjoint l (free_vars_sosub sub1)
    -> lsubst_aux_sosub sub2 sub1
       = lsubst_aux_sosub (sub_filter sub2 l) sub1.
Proof.
  induction sub1; introv disj; allsimpl; auto.
  destruct a; allsimpl.
  allrw disjoint_app_r; repnd.
  rw <- IHsub1; auto.
  f_equal; f_equal.
  destruct s; allsimpl.
  unfold lsubst_aux_sk; simpl; f_equal.
  pose proof (lsubst_bterm_aux_trim l Exc [bterm l0 n0]) as h.
  simpl in h; allrw app_nil_r; autodimp h hyp; eauto with slow.
  pose proof (h sub2 (bterm l0 n0)) as k; clear h; simpl in k.
  repeat (autodimp k hyp).
  inversion k; auto.
Qed.

Lemma lsubst_aux_sosub_aux_aeq {o} :
  forall (t : @SOTerm o) (sub1 : SOSub) (sub2 : Sub),
    cl_sub sub2
    -> cover_so_vars t sub1
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> lsubst_aux (sosub_aux sub1 t) sub2
       = sosub_aux (lsubst_aux_sosub sub2 sub1 ++ sub2sosub sub2) t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv cl socov disj1 disj2 disj3.

  - Case "sovar".
    allsimpl.
    rw @sosub_find_app.
    rw @sosub_find_lsubst_aux_sosub.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v,length ts)) as f;
      symmetry in Heqf; destruct f.

    + destruct s; simpl.
      applydup @sosub_find_some in Heqf; repnd.
      pose proof (simple_lsubst_aux_lsubst_aux_sub
                    n (combine l (map (sosub_aux sub1) ts)) sub2) as e.
      repeat (autodimp e hyp).

      * rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        rw disjoint_flat_map_r; introv i.
        pose proof (isprogram_sosub_aux_free_vars x sub1) as h.
        eapply subvars_disjoint_r;[exact h|]; clear h.
        rw disjoint_app_r; dands.
        { introv a b.
          rw disjoint_flat_map_r in disj0; apply disj0 in Heqf1; simpl in Heqf1.
          rw disjoint_app_r in Heqf1; repnd.
          apply disjoint_sym in Heqf1; apply Heqf1 in a.
          apply in_sovars2vars in b; exrepnd.
          apply in_remove_so_vars in b0; repnd.
          destruct a.
          rw lin_flat_map.
          exists x; dands; auto.
          apply so_free_vars_in_all_fo_vars in b1; auto.
        }
        { rw disjoint_flat_map_r in disj1; apply disj1 in Heqf1; simpl in Heqf1.
          rw disjoint_app_r in Heqf1; repnd; eauto with slow.
        }

      * rw <- e; clear e.
        rw @dom_sub_combine; allrw map_length; auto.
        f_equal.
        rw @lsubst_aux_sub_combine; rw map_map; unfold compose.
        f_equal.
        apply eq_maps; introv i.
        apply ind; auto.

        { allrw @cover_so_vars_sovar; repnd.
          apply socov; auto. }

        { rw disjoint_flat_map_l in disj0; apply disj0 in i; auto. }

        { rw disjoint_flat_map_l in disj3; apply disj3 in i; auto. }

    + rw @lsubst_aux_apply_list; simpl.
      rw @sosub_find_sub2sosub; boolvar; simpl.

      * rw length0 in e; subst; allsimpl.

        remember (sub_find sub2 v) as f2;
          symmetry in Heqf2; destruct f2; simpl; auto.
        rw @lsubst_aux_nil; auto.

      * provefalse.
        rw @cover_so_vars_sovar in socov; repnd.
        apply sosub_find_none in Heqf.
        autodimp socov0 hyp.
        rw null_iff_nil; rw <- length0; auto.

  - Case "soterm".
    simpl; f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i; destruct x; simpl; f_equal.
    allfold (vars2sovars l).
    rw @sosub_filter_app.
    rw @sosub_filter_lsubst_aux_sosub.
    rw @sosub_filter_sub2sosub.
    allsimpl.
    rw disjoint_flat_map_l in disj3; applydup disj3 in i as j; simpl in j.
    rw disjoint_app_l in j; repnd.

    pose proof (subvars_free_vars_sosub_sosub_filter sub1 (vars2sovars l)) as sv1.
    pose proof (subvars_bound_vars_sosub_filter sub1 (vars2sovars l)) as sv2.
    pose proof (lsubst_aux_sosub_sub_filter_if_disjoint
                  (sosub_filter sub1 (vars2sovars l)) sub2 l) as h.
    autodimp h hyp.
    { eapply subvars_disjoint_r;[|exact j0]; auto. }
    rw h.
    eapply ind; eauto.

    { apply implies_cl_sub_filter; auto. }

    { apply cover_so_vars_sosub_filter; auto.
      rw @cover_so_vars_soterm in socov.
      apply socov in i; auto. }

    { eapply subvars_disjoint_l;[exact sv1|].
      eapply subvars_disjoint_r;[exact sv2|auto]. }

    { eapply subvars_disjoint_r;[exact sv2|auto].
      rw disjoint_flat_map_l in disj2.
      apply disj2 in i; simpl in i; rw disjoint_app_l in i; sp. }

    { eapply subvars_disjoint_r;[exact sv1|auto]. }
Qed.

Lemma alphaeq_sub_preserves_cl_sub {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> cl_sub sub1
    -> cl_sub sub2.
Proof.
  introv aeq cl.
  applydup @alphaeq_sub_preserves_free_vars in aeq.
  rw (sub_free_vars_if_cl_sub sub1) in aeq0; auto.
  apply sub_free_vars_iff_cl_sub; auto.
Qed.
Hint Resolve alphaeq_sub_preserves_cl_sub : slow.

Lemma lsubst_aux_alpha_congr_cl_sub {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    cl_sub sub1
    -> alpha_eq t1 t2
    -> alphaeq_sub sub1 sub2
    -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  introv cl aeq1 aeq2.
  applydup @alphaeq_sub_implies_eq_doms in aeq2 as ed.
  pose proof (lsubst_aux_alpha_congr
                t1 t2
                (dom_sub sub1)
                (range sub1)
                (range sub2)) as h.
  allrw @length_dom; allrw @length_range.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw <- @sub_eta; rw ed in h; allrw <- @sub_eta.
  repeat (autodimp h hyp).
  - apply alphaeq_sub_implies_eq_lengths; auto.
  - rw @sub_free_vars_if_cl_sub; auto.
  - rw @sub_free_vars_if_cl_sub; auto.
    apply alphaeq_sub_preserves_cl_sub in aeq2; auto.
  - apply alphaeq_sub_implies_alpha_eq; auto.
Qed.

Lemma covered_sosub_alphaeq_sub {o} :
  forall (sub1 : @SOSub o) (sub2 sub3 : @Sub o),
    covered_sosub sub1 sub2
    -> alphaeq_sub sub2 sub3
    -> covered_sosub sub1 sub3.
Proof.
  introv cov aeq.
  allunfold @covered_sosub.
  apply alphaeq_sub_implies_eq_doms in aeq; rw <- aeq; auto.
Qed.

Lemma subvars_bound_vars_lsubst_aux {o} :
  forall (t : @NTerm o) (sub : @Sub o),
    subvars
      (bound_vars (lsubst_aux t sub))
      (bound_vars t ++ sub_bound_vars sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as f; symmetry in Heqf; destruct f; simpl; auto.
    apply sub_find_some in Heqf.
    rw @sub_bound_vars_is_flat_map_bound_vars_range.
    eapply implies_subvars_flat_map_r; eauto.
    apply in_range_iff; eexists; eauto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    apply subvars_flat_map; introv i.
    destruct x; simpl.
    pose proof (ind n l i (sub_filter sub l)) as sv.
    allrw subvars_prop; introv k; allrw in_app_iff.
    dorn k.
    + left; rw lin_flat_map; exists (bterm l n); simpl; dands; auto; rw in_app_iff; sp.
    + apply sv in k; allrw in_app_iff; dorn k.
      * left; rw lin_flat_map; exists (bterm l n); simpl; dands; auto; rw in_app_iff; sp.
      * right; pose proof (subvars_sub_bound_vars_sub_filter sub l) as h.
        rw subvars_prop in h; apply h in k; sp.
Qed.

Lemma subvars_bound_vars_bterm_lsubst_bterm_aux {o} :
  forall (bt : @BTerm o) (sub : @Sub o),
    subvars
      (bound_vars_bterm (lsubst_bterm_aux bt sub))
      (bound_vars_bterm bt ++ sub_bound_vars sub).
Proof.
  introv.
  pose proof (subvars_bound_vars_lsubst_aux (oterm Exc [bt]) sub) as h;
    simpl in h; allrw app_nil_r; sp.
Qed.

Lemma subvars_bound_vars_sk_lsubst_aux_sk {o} :
  forall (sk : @sosub_kind o) (sub : @Sub o),
    subvars
      (bound_vars_sk (lsubst_aux_sk sub sk))
      (bound_vars_sk sk ++ sub_bound_vars sub).
Proof.
  introv.
  destruct sk; simpl.
  pose proof (subvars_bound_vars_bterm_lsubst_bterm_aux (bterm l n) sub) as h.
  simpl in h; sp.
Qed.

Lemma subvars_bound_vars_sosub_lsubst_aux_sosub {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o),
    subvars
      (bound_vars_sosub (lsubst_aux_sosub sub2 sub1))
      (bound_vars_sosub sub1 ++ sub_bound_vars sub2).
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; allsimpl.
  pose proof (IHsub1 sub2) as sv.
  allrw subvars_prop; introv i; rw in_app_iff in i; dorn i.
  - pose proof (subvars_bound_vars_sk_lsubst_aux_sk s sub2) as h.
    rw subvars_prop in h; apply h in i; allrw in_app_iff; dorn i; tcsp.
  - apply sv in i; allrw in_app_iff; tcsp.
Qed.

Lemma sosub_free_vars_sosub_change_bvars_alpha {o} :
  forall (sub : @SOSub o) vars,
    free_vars_sosub (sosub_change_bvars_alpha vars sub)
    = free_vars_sosub sub.
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; rw IHsub; simpl.
  rw @free_vars_sk_change_bvars_alpha; auto.
Qed.

Lemma sodom_app {o} :
  forall (sub1 sub2 : @SOSub o),
    sodom (sub1 ++ sub2) = sodom sub1 ++ sodom sub2.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; rw IHsub1; auto.
Qed.

Lemma cover_so_vars_app_l {o} :
  forall (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    cover_so_vars t sub1
    -> cover_so_vars t (sub1 ++ sub2).
Proof.
  introv cov.
  allunfold @cover_so_vars.
  allrw subsovars_prop; introv i; apply cov in i.
  rw @sodom_app.
  rw filter_out_fo_vars_app; rw in_app_iff; sp.
Qed.
Hint Resolve cover_so_vars_app_l : slow.

Lemma sodom_lsubst_aux_sosub {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o),
    sodom (lsubst_aux_sosub sub2 sub1) = sodom sub1.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; destruct s; simpl; rw IHsub1; auto.
Qed.

Lemma implies_cover_so_vars_lsubst_aux_sosub {o} :
  forall (t : @SOTerm o) (sub1 : @SOSub o) (sub2 : @Sub o),
    cover_so_vars t sub1
    -> cover_so_vars t (lsubst_aux_sosub sub2 sub1).
Proof.
  introv cov.
  allunfold @cover_so_vars.
  rw @sodom_lsubst_aux_sosub; auto.
Qed.
Hint Resolve implies_cover_so_vars_lsubst_aux_sosub : slow.

Lemma sosub_change_bvars_alpha_app {o} :
  forall (sub1 sub2 : @SOSub o) vars,
    sosub_change_bvars_alpha vars (sub1 ++ sub2)
    = sosub_change_bvars_alpha vars sub1
      ++ sosub_change_bvars_alpha vars sub2.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; allsimpl.
  rw IHsub1; auto.
Qed.

Lemma sosub_change_bvars_alpha_sub2sosub {o} :
  forall (sub : @Sub o) vars,
    sosub_change_bvars_alpha vars (sub2sosub sub)
    = sub2sosub (sub_change_bvars_alpha vars sub).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; simpl; rw IHsub; f_equal; f_equal.
  unfold sk_change_bvars_alpha; simpl.
  rw @var_ren_nil_l; rw @lsubst_aux_nil; auto.
Qed.

Lemma lsubst_aux_alphabt_congr_cl {o} :
  forall (bt1 bt2 : @BTerm o) (sub1 sub2 : @Sub o),
    cl_sub sub1
    -> alpha_eq_bterm bt1 bt2
    -> alphaeq_sub sub1 sub2
    -> alpha_eq_bterm (lsubst_bterm_aux bt1 sub1) (lsubst_bterm_aux bt2 sub2).
Proof.
  introv cl aeq1 aeq2.
  applydup @alphaeq_sub_implies_eq_lengths in aeq2.
  applydup @alphaeq_sub_preserves_cl_sub in aeq2 as cl2; auto.
  applydup @alphaeq_sub_implies_eq_doms in aeq2 as doms.
  pose proof (lsubst_aux_alphabt_congr
                bt1 bt2
                (dom_sub sub1)
                (range sub1)
                (range sub2)) as h.
  allrw @length_dom; allrw @length_range.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  repeat (autodimp h hyp).
  { rw @sub_free_vars_if_cl_sub; auto. }
  { rw @sub_free_vars_if_cl_sub; auto. }
  { apply alphaeq_sub_implies_alpha_eq; auto. }
  allrw <- @sub_eta.
  rw doms in h.
  allrw <- @sub_eta; auto.
Qed.

Lemma lsubst_aux_alphaeq_sk_congr_cl {o} :
  forall (sk1 sk2 : @sosub_kind o) (sub1 sub2 : @Sub o),
    cl_sub sub1
    -> alphaeq_sk sk1 sk2
    -> alphaeq_sub sub1 sub2
    -> alphaeq_sk (lsubst_aux_sk sub1 sk1) (lsubst_aux_sk sub2 sk2).
Proof.
  introv cl aeq1 aeq2.
  pose proof (lsubst_aux_alphabt_congr_cl (sk2bterm sk1) (sk2bterm sk2) sub1 sub2) as h.
  repeat (autodimp h hyp).
  { apply alphaeq_sk_iff_alphaeq_bterm2; auto. }
  apply alphaeq_sk_iff_alphaeq_bterm2.
  destruct sk1, sk2; allsimpl; auto.
Qed.

Lemma alphaeq_sosub_lsubst_aux_sosub {o} :
  forall (sub1 sub2 : @SOSub o) (sub3 sub4 : @Sub o),
    cl_sub sub3
    -> alphaeq_sub sub3 sub4
    -> alphaeq_sosub sub1 sub2
    -> alphaeq_sosub (lsubst_aux_sosub sub3 sub1) (lsubst_aux_sosub sub4 sub2).
Proof.
  induction sub1; destruct sub2; introv cl aeq1 aeq2; allsimpl; auto.
  - inversion aeq2; sp.
  - inversion aeq2; sp.
  - destruct a, p; allsimpl.
    inversion aeq2; subst; clear aeq2.
    constructor; auto.
    destruct s, s0; simpl.
    apply lsubst_aux_alphaeq_sk_congr_cl; auto.
Qed.
Hint Resolve alphaeq_sosub_lsubst_aux_sosub : slow.

Lemma sosub_change_bvars_alpha_lsubst_aux_sosub {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o) vars,
    cl_sub sub2
    -> alphaeq_sosub
         (sosub_change_bvars_alpha vars (lsubst_aux_sosub sub2 sub1))
         (lsubst_aux_sosub
            (sub_change_bvars_alpha vars sub2)
            (sosub_change_bvars_alpha vars sub1)).
Proof.
  introv cl.
  sosub_change sub'.
  sosub_change sub1'.
  sub_change sub2'.

  apply alphaeq_sosub_sym in h.
  eapply alphaeq_sosub_trans;[eauto|].

  apply alphaeq_sosub_lsubst_aux_sosub; auto.
Qed.

Lemma alphaeq_sosub_sub2sosub {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sosub (sub2sosub sub1) (sub2sosub sub2)
    <=> alphaeq_sub sub1 sub2.
Proof.
  induction sub1; destruct sub2; split; intro k; allsimpl; auto;
  try (complete (inversion k)).
  - destruct p; inversion k.
  - destruct a; inversion k.
  - destruct a, p; inversion k; subst; clear k.
    allrw IHsub1.
    constructor; auto.
    allunfold @alphaeq_sk; allsimpl.
    allrw @alphaeqbt_eq.
    allrw @alphaeqbt_nilv2; auto.
    apply alphaeq_eq; auto.
  - destruct a, p; inversion k; subst; clear k.
    constructor; allrw; auto.
    unfold alphaeq_sk; simpl.
    apply alphaeqbt_eq.
    apply alphaeqbt_nilv2; auto.
    apply alphaeq_eq; auto.
Qed.

Lemma implies_alphaeq_sosub_sub2sosub {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> alphaeq_sosub (sub2sosub sub1) (sub2sosub sub2).
Proof.
  introv aeq.
  apply alphaeq_sosub_sub2sosub; auto.
Qed.
Hint Resolve implies_alphaeq_sosub_sub2sosub : slow.

Lemma subvars_bound_vars_lsubst_aux2 {o} :
  forall (t : @NTerm o) sub,
    subvars (bound_vars t) (bound_vars (lsubst_aux t sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.
  rw flat_map_map; unfold compose.
  apply subvars_flat_map2; introv i; destruct x; simpl.
  apply subvars_app_lr; auto.
  eapply ind; eauto.
Qed.

Lemma subvars_bound_vars_sk_lsubst_aux_sk2 {o} :
  forall (sk : @sosub_kind o) (sub : @Sub o),
    subvars
      (bound_vars_sk sk)
      (bound_vars_sk (lsubst_aux_sk sub sk)).
Proof.
  introv.
  destruct sk; unfold bound_vars_sk, lsubst_aux_sk; simpl.
  apply subvars_app_lr; auto.
  apply subvars_bound_vars_lsubst_aux2.
Qed.

Lemma subvars_bound_vars_sosub_lsubst_aux_sosub2 {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o),
    subvars
      (bound_vars_sosub sub1)
      (bound_vars_sosub (lsubst_aux_sosub sub2 sub1)).
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; simpl.
  apply subvars_app_lr; auto.
  apply subvars_bound_vars_sk_lsubst_aux_sk2.
Qed.

Lemma covered_sosub_if_alphaeq_sosub {o} :
  forall (sub1 sub1' : @SOSub o) sub2,
    covered_sosub sub1 sub2
    -> alphaeq_sosub sub1 sub1'
    -> covered_sosub sub1' sub2.
Proof.
  introv cov aeq.
  allunfold @covered_sosub.
  apply alphaeq_sosub_preserves_free_vars in aeq; rw <- aeq; auto.
Qed.
Hint Resolve covered_sosub_if_alphaeq_sosub : slow.

Lemma fo_bound_vars_subvars_all_fo_vars {o} :
  forall t : @SOTerm o,
    subvars (fo_bound_vars t) (all_fo_vars t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; simpl.

  - Case "sovar".
    apply subvars_cons_r.
    apply subvars_flat_map2; auto.

  - Case "soterm".
    apply subvars_flat_map2; introv i; destruct x; simpl.
    apply subvars_app_lr; auto.
    eapply ind; eauto.
Qed.

Lemma covered_sosub_if_alphaeq_sub {o} :
  forall (sub1 : @SOSub o) sub2 sub2',
    covered_sosub sub1 sub2
    -> alphaeq_sub sub2 sub2'
    -> covered_sosub sub1 sub2'.
Proof.
  introv cov aeq.
  allunfold @covered_sosub.
  apply alphaeq_sub_implies_eq_doms in aeq; rw <- aeq; auto.
Qed.
Hint Resolve covered_sosub_if_alphaeq_sub : slow.

(* !!MOVE to sovar_alpha. *)
Hint Resolve alphaeq_sosub_app : slow.

Lemma free_vars_sosub_lsubst_aux_sosub_if_cl {o} :
  forall (sub1 : @SOSub o) (sub2 : @Sub o),
    cl_sub sub2
    -> free_vars_sosub (lsubst_aux_sosub sub2 sub1)
       = remove_nvars (dom_sub sub2) (free_vars_sosub sub1).
Proof.
  induction sub1; introv cl; allsimpl; auto.

  - rw remove_nvars_nil_r; auto.

  - destruct a; simpl.
    rw remove_nvars_app_r; f_equal; tcsp.
    destruct s; simpl.
    rw remove_nvars_comm.
    rw @free_vars_lsubst_aux_cl; eauto with slow.
    rw <- @dom_sub_sub_filter.
    rw <- remove_nvars_comp; auto.
Qed.

Lemma lsubst_aux_sosub_aeq {o} :
  forall (t : @SOTerm o) (sub1 : SOSub) (sub2 : Sub),
    cl_sub sub2
    -> cover_so_vars t sub1
    -> alpha_eq
         (lsubst_aux (sosub sub1 t) sub2)
         (sosub (lsubst_aux_sosub sub2 sub1 ++ sub2sosub sub2) t).
Proof.
  introv cl cs.

  pose proof (unfold_sosub (lsubst_aux_sosub sub2 sub1 ++ sub2sosub sub2) t) as h.
  pose proof (unfold_sosub sub1 t) as k.
  exrepnd.

  rw h1; rw k1.

  pose proof (lsubst_aux_alpha_congr_cl_sub
                (sosub_aux sub' t')
                (sosub_aux sub' t')
                sub2
                (sub_change_bvars_alpha
                   (all_fo_vars t'
                                ++ free_vars_sosub sub'
                   )
                   sub2)) as k.
  sub_change sub2'.
  repeat (autodimp k hyp).
  eapply alpha_eq_trans;[exact k|].

  allrw disjoint_app_l; repnd.

  rw @lsubst_aux_sosub_aux_aeq; eauto 3 with slow.

  apply alphaeq_eq.
  apply sosub_aux_alpha_congr2; eauto with slow.

  - rw @free_vars_sosub_app.
    rw @free_vars_sosub_sub2sosub_cl_sub; eauto with slow.
    rw app_nil_r.
    rw @free_vars_sosub_lsubst_aux_sosub_if_cl; eauto with slow.
    apply disjoint_remove_nvars2; eauto with slow.

  - rw @free_vars_sosub_app.
    rw @free_vars_sosub_sub2sosub_cl_sub; eauto with slow.
    rw app_nil_r.
    rw @free_vars_sosub_lsubst_aux_sosub_if_cl; eauto with slow.
    rw @bound_vars_sosub_app.
    rw @bound_vars_sosub_sub2sosub.
    rw disjoint_app_r; dands; eauto with slow.

    + rw disjoint_app_l; dands; auto.

      * eapply subvars_disjoint_l;[apply subvars_bound_vars_sosub_lsubst_aux_sosub|].
        apply disjoint_app_l; dands; eauto with slow.

        { apply disjoint_sym; apply disjoint_remove_nvars2; auto. }

        { apply disjoint_sym; apply disjoint_remove_nvars2; auto. }

      * apply disjoint_sym; apply disjoint_remove_nvars2; auto.

    + eapply subvars_disjoint_r;[apply fovars_subvars_all_fo_vars|].
      rw disjoint_app_l; dands; eauto with slow.
      eapply subvars_disjoint_l;[apply subvars_bound_vars_sosub_lsubst_aux_sosub|].
      apply disjoint_app_l; dands; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[apply fovars_subvars_all_fo_vars|].
    eauto with slow.

  - eapply cover_so_vars_if_so_alphaeq;[|exact h2].
    eapply cover_so_vars_if_alphaeq_sosub;[|exact h0].
    eauto with slow.

  - eapply alphaeq_sosub_trans;[|exact h0]; eauto with slow.
Qed.

Lemma sosub_aux_trim_aux {o} :
  forall (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    (forall v, LIn v (so_free_vars t) -> LIn v (sodom sub2) -> LIn v (sodom sub1))
    -> sosub_aux (sub1 ++ sub2) t = sosub_aux sub1 t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv sv; allsimpl.

  - Case "sovar".
    rw @sosub_find_app.
    allrw subsovars_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f; symmetry in Heqf; destruct f.

    + destruct s; f_equal; f_equal.
      apply eq_maps; introv i.
      apply ind; auto.
      introv k1 k2.
      apply sv; auto.
      right; rw lin_flat_map.
      exists x; sp.

    + remember (sosub_find sub2 (v, length ts)) as g; symmetry in Heqg; destruct g.

      * provefalse.
        apply sosub_find_none in Heqf; sp.
        destruct s.
        apply sosub_find_some in Heqg; sp.
        eapply in_sodom_if in Heqg0; eauto.

      * f_equal.
        apply eq_maps; introv i.
        apply ind; auto.
        introv k1 k2.
        apply sv; auto.
        right; rw lin_flat_map.
        exists x; sp.

  - Case "soterm".
    f_equal; apply eq_maps; introv i; destruct x; simpl.
    f_equal.
    rw @sosub_filter_app.
    eapply ind; eauto.

    allrw @sodom_sosub_filter.
    introv k j.
    allrw in_remove_so_vars; repnd; dands; auto.
    pose proof (sv v) as h; repeat (autodimp h hyp).
    rw lin_flat_map.
    exists (sobterm l s); dands; auto.
    simpl.
    rw in_remove_so_vars; dands; auto.
Qed.

Lemma sosub_aux_trim {o} :
  forall (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    subsovars (so_free_vars t)(sodom sub1)
    -> sosub_aux (sub1 ++ sub2) t = sosub_aux sub1 t.
Proof.
  introv sv.
  apply sosub_aux_trim_aux.
  introv i j.
  rw subsovars_prop in sv.
  apply sv in i; auto.
Qed.

Lemma allvars_range_sosub_app {o} :
  forall (sub1 sub2 : @SOSub o),
    allvars_range_sosub (sub1 ++ sub2)
    = allvars_range_sosub sub1 ++ allvars_range_sosub sub2.
Proof.
  induction sub1; introv; allsimpl; auto.
  rw IHsub1; rw app_assoc; auto.
Qed.

Lemma alphaeq_sosub_app_l_implies {o} :
  forall (sub1 sub2 sub : @SOSub o),
    alphaeq_sosub (sub1 ++ sub2) sub
    -> {sub3 : SOSub
        & {sub4 : SOSub
        & sub = sub3 ++ sub4
        # alphaeq_sosub sub1 sub3
        # alphaeq_sosub sub2 sub4}}.
Proof.
  induction sub1; destruct sub; introv aeq; allsimpl;
  inversion aeq as [|? ? ? ? ? aeqsk aeqs]; subst; tcsp; clear aeq.

  - exists ([] : @SOSub o) ([] : @SOSub o); auto.

  - exists ([] : @SOSub o) ((v, sk2) :: sub); auto.

  - apply IHsub1 in aeqs; exrepnd; subst.
    exists ((v,sk2) :: sub3) sub4; auto.
Qed.

Lemma sosub_trim {o} :
  forall (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    cover_so_vars t sub1
    -> subsovars (so_free_vars t) (sodom sub1)
    -> alphaeq (sosub (sub1 ++ sub2) t) (sosub sub1 t).
Proof.
  introv cov sv.

  pose proof (unfold_sosub (sub1 ++ sub2) t) as h.
  pose proof (unfold_sosub sub1 t) as k.
  exrepnd.
  rw h1; rw k1.

  apply alphaeq_sosub_app_l_implies in h0; exrepnd; subst.

  rw @sosub_aux_trim; eauto with slow;
  [|apply so_alphaeq_preserves_free_vars in h2; rw <- h2;
    apply alphaeq_sosub_implies_eq_sodoms in h7; rw <- h7;
    auto].

  allrw @free_vars_sosub_app.
  allrw @bound_vars_sosub_app.
  allrw disjoint_app_r; repnd.
  allrw disjoint_app_l; repnd.

  apply sosub_aux_alpha_congr2; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[apply fovars_subvars_all_fo_vars|].
    eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[apply fovars_subvars_all_fo_vars|].
    eauto with slow.
Qed.

Lemma lsubst_aux_sosub_mk_abs_subst {o} :
  forall (sub : @Sub o) bs vars,
    lsubst_aux_sosub sub (mk_abs_subst vars bs)
    = mk_abs_subst vars (map (fun b => lsubst_bterm_aux b sub) bs).
Proof.
  induction bs; destruct vars; simpl; auto.
  - destruct s; simpl; auto.
  - destruct s; destruct a; simpl.
    boolvar; simpl; auto; subst.
    rw IHbs.
    f_equal.
Qed.

Lemma alpha_eq_lsubst_aux_mk_instance {o} :
  forall (rhs : @SOTerm o) vars bs sub,
    cl_sub sub
    -> socovered rhs vars
    -> matching_bterms vars bs
    -> alpha_eq
         (mk_instance vars (lsubst_bterms_aux bs sub) rhs)
         (lsubst_aux (mk_instance vars bs rhs) sub).
Proof.
  introv cl cov m.
  unfold mk_instance.
  pose proof (lsubst_aux_sosub_aeq
                rhs
                (mk_abs_subst vars bs)
                sub) as h.
  repeat (autodimp h hyp).

  - apply socovered_implies_cover_so_vars; auto.

  - apply alpha_eq_sym in h.
    eapply alpha_eq_trans;[|exact h]; clear h.

    pose proof (sosub_trim
                  rhs
                  (lsubst_aux_sosub sub (mk_abs_subst vars bs))
                  (sub2sosub sub))
      as aeq.
    repeat (autodimp aeq hyp).

    + apply implies_cover_so_vars_lsubst_aux_sosub; auto.
      apply socovered_implies_cover_so_vars; auto.

    + rw @sodom_lsubst_aux_sosub.
      rw <- @mk_abs_subst_some_prop2; auto.

    + apply alphaeq_sym in aeq.
      apply alphaeq_eq in aeq.
      eapply alpha_eq_trans;[|exact aeq]; clear aeq.
      rw @lsubst_aux_sosub_mk_abs_subst; auto.
Qed.

Lemma correct_abs_implies_socovered {o} :
  forall oa vars (rhs : @SOTerm o),
    correct_abs oa vars rhs
    -> socovered rhs vars.
Proof.
  introv c.
  unfold correct_abs in c; sp.
Qed.
Hint Resolve correct_abs_implies_socovered : slow.

Lemma compute_step_catch_if_diff {p} :
  forall (nc : NonCanonicalOp)
         (t : @NTerm p)
         (arg1bts btsr : list BTerm),
    nc <> NTryCatch
    -> compute_step_catch nc t arg1bts btsr
       = csuccess (oterm Exc arg1bts).
Proof.
  introv d.
  unfold compute_step_catch; destruct nc; sp.
Qed.

Lemma compute_step_fresh_if_isvalue_like {o} :
  forall lib v (t : @NTerm o),
    isvalue_like t
    -> compute_step lib (mk_fresh v t)
       = csuccess (pushdown_fresh v t).
Proof.
  introv isv.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; auto.
  - apply isexc_implies2 in isv; exrepnd; subst; auto.
Qed.

Lemma implies_isvalue_like_subst_aux {o} :
  forall (t : @NTerm o) v u,
    isvalue_like t
    -> isvalue_like (subst_aux t v u).
Proof.
  introv isv.
  unfold subst_aux.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; simpl; tcsp; eauto 3 with slow.
  - apply isexc_implies2 in isv; exrepnd; subst; simpl; tcsp.
Qed.
Hint Resolve implies_isvalue_like_subst_aux : slow.

Lemma compute_step_fresh_if_isnoncan_like {o} :
  forall lib v (t : @NTerm o),
    isnoncan_like t
    -> compute_step lib (mk_fresh v t)
       = let a := get_fresh_atom t in
         on_success (compute_step lib (subst t v (mk_utoken a)))
                    (fun u => mk_fresh v (subst_utokens u [(a,mk_var v)])).
Proof.
  introv isc.
  unfold isnoncan_like in isc; repndors.
  - apply isnoncan_implies in isc; exrepnd; subst; auto.
    rw @compute_step_eq_unfold; auto.
  - apply isabs_implies in isc; exrepnd; subst; auto.
    rw @compute_step_eq_unfold; auto.
Qed.

Lemma implies_isnoncan_like_subst_aux {o} :
  forall (t : @NTerm o) v u,
    isnoncan_like t
    -> isnoncan_like (subst_aux t v u).
Proof.
  introv isv.
  unfold subst_aux.
  unfold isnoncan_like in isv; repndors.
  - apply isnoncan_implies in isv; exrepnd; subst; simpl; tcsp.
  - apply isabs_implies in isv; exrepnd; subst; simpl; tcsp.
Qed.
Hint Resolve implies_isnoncan_like_subst_aux : slow.

Lemma cl_lsubst_trivial {o} :
  forall (t : @NTerm o) sub,
    disjoint (dom_sub sub) (free_vars t)
    -> cl_sub sub
    -> lsubst t sub = t.
Proof.
  introv d cl.
  apply lsubst_trivial4; auto.
  introv i.
  rw @cl_sub_eq2 in cl; apply cl in i; rw i; auto.
Qed.

Lemma cl_subst_trivial {o} :
  forall (t : @NTerm o) v u,
    !LIn v (free_vars t)
    -> closed u
    -> subst t v u = t.
Proof.
  introv d cl.
  unfold subst; apply cl_lsubst_trivial; simpl; eauto with slow.
  apply disjoint_singleton_l; auto.
Qed.

(* !! MOVE to list *)
Lemma remove_repeats_app :
  forall T (deq : Deq T) l1 l2,
    remove_repeats deq (l1 ++ l2)
    = diff deq l2 (remove_repeats deq l1) ++ remove_repeats deq l2.
Proof.
  induction l1; introv; allsimpl.
  - rw diff_nil; simpl; auto.
  - boolvar; allrw in_app_iff; repndors; tcsp;
    try (rw diff_cons_r); boolvar; allrw not_over_or; repnd; tcsp.
    rw IHl1; simpl; sp.
Qed.

Lemma get_utokens_sub_filter_subset {o} :
  forall (sub : @Sub o) l,
    subset (get_utokens_sub (sub_filter sub l)) (get_utokens_sub sub).
Proof.
  unfold get_utokens_sub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  apply range_sub_filter_subset in i1; auto.
Qed.

(* !!MOVE to list *)
Lemma diff_remove_repeats :
  forall T (deq : Deq T) l1 l2,
    diff deq l1 (remove_repeats deq l2)
    = remove_repeats deq (diff deq l1 l2).
Proof.
  induction l2; introv; simpl.
  - rw diff_nil; simpl; auto.
  - rw diff_cons_r; boolvar; simpl; boolvar; allrw diff_cons_r; boolvar; tcsp;
    allrw in_diff; try (complete (provefalse; tcsp)).
    rw IHl2; auto.
Qed.

(* !!MOVE to list *)
Lemma diff_flat_map_r :
  forall A B (deq : Deq B) (f : A -> list B) (l1 : list B) (l2 : list A),
    diff deq l1 (flat_map f l2)
    = flat_map (fun a => diff deq l1 (f a)) l2.
Proof.
  induction l2; simpl.
  - rw diff_nil; auto.
  - rw diff_app_r; f_equal; tcsp.
Qed.

(* !!MOVE to computation1 *)
Lemma get_utokens_lsubst_aux_diff {o} :
  forall (t : @NTerm o) sub atoms,
    subset (get_utokens_sub sub) atoms
    -> diff (get_patom_deq o) atoms (get_utokens (lsubst_aux t sub))
       = diff (get_patom_deq o) atoms (get_utokens t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv ss; simpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl;
    allrw diff_nil; auto.

    rw <- null_iff_nil.
    rw null_diff_subset.
    introv i.
    apply sub_find_some in Heqsf.
    apply ss.
    rw lin_flat_map.
    exists n; dands; auto.
    apply in_range_iff; eexists; eauto.

  - Case "oterm".
    allrw diff_app_r.
    f_equal.
    allrw diff_flat_map_r.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; simpl.
    apply (ind t l); auto.
    eapply subset_trans;[|exact ss].
    apply get_utokens_sub_filter_subset.
Qed.

(*
(* !!MOVE to computation1 *)
Lemma eq_fresh_atom1 {o} :
  forall lib (t : @NTerm o) v a,
    LIn a (atom_sub_range (ce_atom_sub lib))
    -> get_fresh_atom lib (subst_aux t v (mk_utoken a))
       = get_fresh_atom lib t.
Proof.
  introv i.
  unfold get_fresh_atom; simpl.

  assert (get_utoks_norep lib (subst_aux t v (mk_utoken a))
          = get_utoks_norep lib t) as e.

  {
    unfold get_utoks_norep.
    allrw remove_repeats_app.
    f_equal.
    allrw diff_remove_repeats.
    f_equal.
    apply get_utokens_lsubst_aux_diff.
    unfold get_utokens_sub; simpl.
    introv k; allsimpl; repndors; subst; tcsp.
    unfold get_utokens_ce; rw in_app_iff; tcsp.
  }

  rw e; auto.
Qed.
*)

(* !!MOVE to computation1 *)
Lemma find_atom_add {o} :
  forall (lib : @compenv o) v a x,
    find_atom (ce_atom_sub (add_atom_sub lib v a)) x
    = if deq_nvar x v
      then Some a
      else find_atom (ce_atom_sub lib) x.
Proof.
  introv; unfold ce_atom_sub, add_atom_sub; simpl; boolvar; tcsp.
Qed.

(* !!MOVE to computation1 *)
Fixpoint sub_aux_utok_sub {o} (usub : @utok_sub o) (sub : @Sub o) : utok_sub :=
  match usub with
    | nil => nil
    | (a,t) :: s => (a, lsubst_aux t sub) :: sub_aux_utok_sub s sub
  end.

(* !!MOVE to computation1 *)
Definition utok_sub_dom {o} (s : @utok_sub o) : list (get_patom_set o) :=
  map (fun x => fst x) s.

(* !!MOVE to computation1 *)
Definition utok_sub_range {o} (s : @utok_sub o) : list (@NTerm o) :=
  map (fun x => snd x) s.

(* !!MOVE to computation1 *)
Lemma implies_utok_sub_range {o} :
  forall (s : @utok_sub o) v t,
    LIn (v,t) s -> LIn t (utok_sub_range s).
Proof.
  induction s; introv i; allsimpl; tcsp.
  repndors; subst; tcsp.
  destruct a; allsimpl; tcsp.
  apply IHs in i; sp.
Qed.

(* !!MOVE to computation1 *)
Lemma utok_sub_dom_sub_aux_utok_sub {o} :
  forall (usub : @utok_sub o) sub,
    utok_sub_dom (sub_aux_utok_sub usub sub)
    = utok_sub_dom usub.
Proof.
  induction usub; introv; simpl; auto.
  destruct a; simpl; rw IHusub; auto.
Qed.

(* !!MOVE to computation1 *)
Lemma subst_utok_if_not_in {o} :
  forall usub g (bs : list (@BTerm o)),
    !LIn g (utok_sub_dom usub)
    -> subst_utok g bs usub = oterm (Can (NUTok g)) bs.
Proof.
  induction usub; introv ni; allsimpl; tcsp; GC.
  allrw not_over_or; repnd; allsimpl.
  unfold subst_utok; simpl; boolvar; subst; tcsp.
  fold (subst_utok g bs usub).
  rw IHusub; auto.
Qed.

Lemma in_utok_sub_eta {o} :
  forall a t (sub : @utok_sub o),
    LIn (a,t) sub
    -> (LIn a (utok_sub_dom sub) # LIn t (utok_sub_range sub)).
Proof.
  induction sub; introv i; allsimpl; tcsp.
  destruct a0; allsimpl; repndors; cpx.
Qed.

Lemma trivial_subst_utokens_aux {o} :
  forall (t : @NTerm o) usub,
    disjoint (get_utokens t) (utok_sub_dom usub)
    -> subst_utokens_aux t usub = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv disj; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm; allsimpl.

    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      allrw disjoint_cons_l; repnd.
      unfold subst_utok.
      remember (utok_sub_find usub g) as usf; symmetry in Hequsf; destruct usf.

      * apply utok_sub_find_some in Hequsf.
        apply in_utok_sub_eta in Hequsf; sp.

      * f_equal.
        apply eq_map_l; introv i; destruct x as [l t]; allsimpl.
        f_equal.
        disj_flat_map; allsimpl.
        eapply ind; eauto.

    + f_equal.
      allrw disjoint_app_l; repnd.
      apply eq_map_l; introv i; destruct x as [l t]; simpl.
      f_equal; apply (ind t l); auto.
      disj_flat_map; allsimpl; auto.
Qed.

Lemma trivial_subst_utokens {o} :
  forall (t : @NTerm o) usub,
    disjoint (get_utokens t) (utok_sub_dom usub)
    -> alpha_eq (subst_utokens t usub) t.
Proof.
  introv disj.
  pose proof (unfold_subst_utokens usub t) as h; exrepnd.
  rw h0.
  rw @trivial_subst_utokens_aux; eauto with slow.
  apply alphaeq_preserves_utokens in h1.
  rw <- h1; auto.
Qed.

(* !!MOVE to variable *)
Lemma disjoint_remove_nvars_weak_r :
  forall lva lvb lvc : list NVar,
    disjoint lva lvb -> disjoint lva (remove_nvars lvc lvb).
Proof.
  introv disj.
  apply disjoint_sym; apply disjoint_remove_nvars2; eauto with slow.
Qed.
Hint Resolve disjoint_remove_nvars_weak_r : slow.

Lemma lsubst_aux_subst_utokens_aux_disj {o} :
  forall (t : @NTerm o) sub usub,
    disjoint (get_utokens_sub sub) (utok_sub_dom usub)
    -> disjoint (free_vars_utok_sub usub) (dom_sub sub)
    -> lsubst_aux (subst_utokens_aux t usub) sub
       = subst_utokens_aux (lsubst_aux t sub) usub.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv disj1 disj2; auto.

  - Case "vterm".
    simpl.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
    apply sub_find_some in Heqsf.
    applydup @in_sub_eta in Heqsf; repnd.
    unfold get_utokens_sub in disj1.
    disj_flat_map.
    rw @trivial_subst_utokens_aux; auto.

  - Case "oterm".
    rw @lsubst_aux_oterm.
    repeat (rw @subst_utokens_aux_oterm).

    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find usub g) as usf; symmetry in Hequsf; destruct usf.

      * apply utok_sub_find_some in Hequsf.
        rw @lsubst_aux_trivial_cl_term; auto.
        introv i j.
        apply disjoint_sym in disj2; apply disj2 in j.
        rw @in_free_vars_utok_sub in j.
        destruct j; eexists; eexists; dands; eauto.

      * simpl; f_equal.
        unfold lsubst_bterms_aux.
        allrw map_map; allunfold @compose.
        apply eq_maps; introv i; destruct x as [l t]; allsimpl.
        f_equal.
        eapply ind; eauto with slow.

        { eapply subset_disjoint;[|exact disj1].
          apply get_utokens_sub_filter_subset. }

        { rw <- @dom_sub_sub_filter; eauto with slow. }

    + allsimpl; f_equal.
      unfold lsubst_bterms_aux.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i; destruct x as [l t]; simpl.
      f_equal; apply (ind t l); auto.

      { eapply subset_disjoint;[|exact disj1].
        apply get_utokens_sub_filter_subset. }

      { rw <- @dom_sub_sub_filter; eauto with slow. }
Qed.

Fixpoint swap_utok_sub {o} sw (sub : @utok_sub o) : utok_sub :=
  match sub with
    | [] => []
    | (a,t) :: s => (a,swap sw t) :: swap_utok_sub sw s
  end.

Fixpoint cswap_utok_sub {o} sw (sub : @utok_sub o) : utok_sub :=
  match sub with
    | [] => []
    | (a,t) :: s => (a,cswap sw t) :: cswap_utok_sub sw s
  end.

Lemma utok_sub_find_swap_utok_sub {o} :
  forall sw (usub : @utok_sub o) a,
    utok_sub_find (swap_utok_sub sw usub) a
    = match utok_sub_find usub a with
        | Some t => Some (swap sw t)
        | None => None
      end.
Proof.
  induction usub; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; subst; tcsp.
Qed.

Lemma utok_sub_find_cswap_utok_sub {o} :
  forall sw (usub : @utok_sub o) a,
    utok_sub_find (cswap_utok_sub sw usub) a
    = match utok_sub_find usub a with
        | Some t => Some (cswap sw t)
        | None => None
      end.
Proof.
  induction usub; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; subst; tcsp.
Qed.

Lemma swap_oterm {o} :
  forall op (bs : list (@BTerm o)) sw,
    swap sw (oterm op bs) = oterm op (map (swapbt sw) bs).
Proof. sp. Qed.

Lemma cswap_oterm {o} :
  forall op (bs : list (@BTerm o)) sw,
    cswap sw (oterm op bs) = oterm op (map (cswapbt sw) bs).
Proof. sp. Qed.

Lemma swap_subst_utokens_aux {o} :
  forall sw (t : @NTerm o) usub,
    swap sw (subst_utokens_aux t usub)
    = subst_utokens_aux (swap sw t) (swap_utok_sub sw usub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "oterm".
    allrw @swap_oterm.
    repeat (rw @subst_utokens_aux_oterm).

    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      allrw map_map; allunfold @compose.
      unfold subst_utok.
      rw @utok_sub_find_swap_utok_sub.
      remember (utok_sub_find usub g) as usf; symmetry in Hequsf; destruct usf; auto.

      simpl; f_equal.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i; destruct x as [l t]; allsimpl.
      f_equal.
      eapply ind; eauto with slow.

    + allsimpl; f_equal.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i; destruct x as [l t]; simpl.
      f_equal; apply (ind t l); auto.
Qed.

Lemma cswap_subst_utokens_aux {o} :
  forall sw (t : @NTerm o) usub,
    cswap sw (subst_utokens_aux t usub)
    = subst_utokens_aux (cswap sw t) (cswap_utok_sub sw usub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "oterm".
    allrw @cswap_oterm.
    repeat (rw @subst_utokens_aux_oterm).

    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      allrw map_map; allunfold @compose.
      unfold subst_utok.
      rw @utok_sub_find_cswap_utok_sub.
      remember (utok_sub_find usub g) as usf; symmetry in Hequsf; destruct usf; auto.

      simpl; f_equal.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i; destruct x as [l t]; allsimpl.
      f_equal.
      eapply ind; eauto with slow.

    + allsimpl; f_equal.
      allrw map_map; allunfold @compose.
      apply eq_maps; introv i; destruct x as [l t]; simpl.
      f_equal; apply (ind t l); auto.
Qed.

Inductive alphaeq_utok_sub {o} : @utok_sub o -> @utok_sub o -> Type :=
  | aequs_nil : alphaeq_utok_sub [] []
  | aequs_cons :
      forall a t1 t2 sub1 sub2,
        alphaeq t1 t2
        -> alphaeq_utok_sub sub1 sub2
        -> alphaeq_utok_sub ((a,t1) :: sub1) ((a,t2) :: sub2).
Hint Constructors alphaeq_utok_sub.

Lemma alphaeq_utok_sub_cons {o} :
  forall a (t1 t2 : @NTerm o) s1 s2,
    alphaeq_utok_sub ((a,t1) :: s1) ((a,t2) :: s2)
    <=> (alphaeq t1 t2 # alphaeq_utok_sub s1 s2).
Proof.
  introv; split; introv k.
  - inversion k; sp.
  - constructor; sp.
Qed.

Lemma map_combine_left :
  forall (T1 T2 T3 : tuniv)
         (f : T1 -> T3) (l1 : list T1) (l2 : list T2),
    map (fun x => (f (fst x), snd x)) (combine l1 l2)
    = combine (map f l1) l2.
Proof.
  induction l1; introv; allsimpl; auto.
  destruct l2; allsimpl; auto.
  rw IHl1; auto.
Qed.

Lemma disjoint_swapbvars3 :
  forall bvs vs vs1 vs2 : list NVar,
    disjoint vs1 vs2
    -> no_repeats vs2
    -> disjoint vs2 bvs
    -> disjoint (remove_nvars vs1 bvs) vs
    -> disjoint vs2 vs
    -> length vs1 = length vs2
    -> disjoint vs (swapbvars (mk_swapping vs1 vs2) bvs).
Proof.
  introv d1 norep d2 d3 d4 len i j.
  apply disjoint_sym in d3.
  applydup d3 in i as k.
  rw in_remove_nvars in k.
  rw in_swapbvars in j; exrepnd; subst.
  apply disjoint_sym in d2.
  applydup d2 in j1 as q.
  destruct (in_deq _ deq_nvar v' vs1) as [d|d].
  - pose proof (swapvar_in vs1 vs2 v') as h.
    repeat (autodimp h hyp).
    apply d4 in h; sp.
  - rw swapvar_not_in in i; auto.
    rw swapvar_not_in in k; auto.
Qed.

(*
Lemma alphaeq_swap_disj_free_vars {o} :
  forall (t : @NTerm o) vs1 vs2,
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint (free_vars t) vs1
    -> disjoint (allvars t) vs2
    -> disjoint vs1 vs2
    -> alphaeq (swap (mk_swapping vs1 vs2) t) t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv len norep d1 d2 d3; allsimpl; auto.

  - Case "vterm".
    allrw disjoint_singleton_l.
    rw swapvar_not_in; eauto with slow.

  - Case "sterm".
    constructor; introv.
    apply ind; auto.

  - Case "oterm".
    apply alphaeq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rw <- map_combine_left in i; rw in_map_iff in i; exrepnd; cpx.
    rw in_combine_same in i1; repnd; subst; allsimpl.
    destruct a as [l t]; allsimpl.
    pose proof (fresh_vars (length l)
                           ((swapbvars (mk_swapping vs1 vs2) l)
                              ++ l
                              ++ vs1
                              ++ vs2
                              ++ (free_vars t)
                              ++ (allvars (swap (mk_swapping vs1 vs2) t))
                              ++ (allvars t))) as fv; exrepnd.
    allrw disjoint_app_r; repnd.

    apply (aeqbt _ lvn); allsimpl; allrw length_swapbvars; auto;
    allrw disjoint_app_r; tcsp.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.

    rw @swap_swap.
    rw mk_swapping_app; auto.
    rw <- @swap_app_swap; eauto with slow.
    rw <- mk_swapping_app; auto.
    rw <- @swap_swap.
    apply (ind t _ l); allrw @size_swap; auto.

    + rw @free_vars_swap; eauto with slow.
      apply disjoint_sym.
      apply disjoint_swapbvars3; eauto with slow.

    + apply disjoint_sym.
      apply disjoint_allvars_swap; eauto with slow.
Qed.
 *)

Lemma alphaeq_cswap_disj_free_vars {o} :
  forall (t : @NTerm o) vs1 vs2,
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint (free_vars t) vs1
    -> disjoint (allvars t) vs2
    -> disjoint vs1 vs2
    -> alphaeq (cswap (mk_swapping vs1 vs2) t) t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
  introv len norep d1 d2 d3; allsimpl; eauto 3 with slow.

  - Case "vterm".
    allrw disjoint_singleton_l.
    rw swapvar_not_in; eauto with slow.

  - Case "oterm".
    apply alphaeq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rw <- map_combine_left in i; rw in_map_iff in i; exrepnd; cpx.
    rw in_combine_same in i1; repnd; subst; allsimpl.
    destruct a as [l t]; allsimpl.
    pose proof (fresh_vars (length l)
                           ((swapbvars (mk_swapping vs1 vs2) l)
                              ++ l
                              ++ vs1
                              ++ vs2
                              ++ (free_vars t)
                              ++ (allvars (cswap (mk_swapping vs1 vs2) t))
                              ++ (allvars t))) as fv; exrepnd.
    allrw disjoint_app_r; repnd.

    apply (aeqbt _ lvn); allsimpl; allrw length_swapbvars; auto;
    allrw disjoint_app_r; tcsp.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.

    rw @cswap_cswap.
    rw mk_swapping_app; auto.
    rw <- @cswap_app_cswap; eauto with slow.
    rw <- mk_swapping_app; auto.
    rw <- @cswap_cswap.
    apply (ind t _ l); allrw @osize_cswap; eauto 3 with slow.

    + rw @free_vars_cswap; eauto with slow.
      apply disjoint_sym.
      apply disjoint_swapbvars3; eauto with slow.

    + apply disjoint_sym.
      apply disjoint_allvars_cswap; eauto with slow.
Qed.

Fixpoint bound_vars_utok_sub {o} (sub : @utok_sub o) :=
  match sub with
    | [] => []
    | (_,t) :: s => bound_vars t ++ bound_vars_utok_sub s
  end.

(*
Lemma alphaeq_utok_sub_swap_utok_sub {o} :
  forall vs1 vs2 (s : @utok_sub o),
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> disjoint (free_vars_utok_sub s) vs1
    -> disjoint (free_vars_utok_sub s) vs2
    -> disjoint (bound_vars_utok_sub s) vs2
    -> alphaeq_utok_sub (swap_utok_sub (mk_swapping vs1 vs2) s) s.
Proof.
  induction s; introv len norep d0 d1 d2 d3; allsimpl; tcsp.
  destruct a; allsimpl.
  allrw disjoint_app_l; repnd.
  apply alphaeq_utok_sub_cons; dands; tcsp.
  apply alphaeq_swap_disj_free_vars; auto.
  apply disjoint_sym; apply disjoint_to_allvars_r.
  unfold all_vars; rw disjoint_app_r; dands; eauto with slow.
Qed.
 *)

Lemma alphaeq_utok_sub_cswap_utok_sub {o} :
  forall vs1 vs2 (s : @utok_sub o),
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> disjoint (free_vars_utok_sub s) vs1
    -> disjoint (free_vars_utok_sub s) vs2
    -> disjoint (bound_vars_utok_sub s) vs2
    -> alphaeq_utok_sub (cswap_utok_sub (mk_swapping vs1 vs2) s) s.
Proof.
  induction s; introv len norep d0 d1 d2 d3; allsimpl; tcsp.
  destruct a; allsimpl.
  allrw disjoint_app_l; repnd.
  apply alphaeq_utok_sub_cons; dands; tcsp.
  apply alphaeq_cswap_disj_free_vars; auto.
  apply disjoint_sym; apply disjoint_to_allvars_r.
  unfold all_vars; rw disjoint_app_r; dands; eauto with slow.
Qed.

Lemma alphaeq_utok_sub_trans {o} :
  forall (s1 s2 s3 : @utok_sub o),
    alphaeq_utok_sub s1 s2
    -> alphaeq_utok_sub s2 s3
    -> alphaeq_utok_sub s1 s3.
Proof.
  induction s1; destruct s2; destruct s3; introv a1 a2;
  inversion a1; inversion a2; subst; cpx; tcsp.
  constructor; eauto with slow.
Qed.
Hint Resolve alphaeq_utok_sub_trans : slow.

Lemma alphaeq_utok_sub_refl {o} :
  forall (s : @utok_sub o),
    alphaeq_utok_sub s s.
Proof.
  induction s; auto.
  destruct a.
  constructor; eauto with slow.
Qed.
Hint Resolve alphaeq_utok_sub_refl : slow.

Lemma alphaeq_utok_sub_sym {o} :
  forall (s1 s2 : @utok_sub o),
    alphaeq_utok_sub s1 s2
    -> alphaeq_utok_sub s2 s1.
Proof.
  induction s1; destruct s2; introv h;
  inversion h; subst; cpx; tcsp.
  constructor; eauto with slow.
Qed.
Hint Resolve alphaeq_utok_sub_sym : slow.

Lemma alphaeq_utok_sub_preserves_free_vars {o} :
  forall (s1 s2 : @utok_sub o),
    alphaeq_utok_sub s1 s2
    -> free_vars_utok_sub s1 = free_vars_utok_sub s2.
Proof.
  induction s1; destruct s2; introv h;
  inversion h; subst; cpx; tcsp; allsimpl.
  f_equal; tcsp.
  apply alphaeq_preserves_free_vars.
  apply alphaeq_eq; auto.
Qed.

Lemma alphaeq_utok_sub_implies_alphaeq_utok_sub_find {o} :
  forall (s1 s2 : @utok_sub o) a,
    alphaeq_utok_sub s1 s2
    -> (
         {t1 : NTerm
          & {t2 : NTerm
          & utok_sub_find s1 a = Some t1
          # utok_sub_find s2 a = Some t2
          # alphaeq t1 t2}}
         [+]
         (utok_sub_find s1 a = None # utok_sub_find s2 a = None)
       ).
Proof.
  induction s1; destruct s2; introv aeq; allsimpl; inversion aeq; subst; tcsp.
  boolvar; subst; tcsp.
  left; exists t1 t2; sp.
Qed.

Lemma alpha_eq_subst_utokens_aux {o} :
  forall (t1 t2 : @NTerm o) (s1 s2 : @utok_sub o),
    disjoint (free_vars_utok_sub s1) (bound_vars t1)
    -> disjoint (free_vars_utok_sub s2) (bound_vars t2)
    -> alpha_eq t1 t2
    -> alphaeq_utok_sub s1 s2
    -> alpha_eq (subst_utokens_aux t1 s1) (subst_utokens_aux t2 s2).
Proof.
  nterm_ind1s t1 as [v|f ind|op bs ind] Case; introv d1 d2 aeqt aeqs; auto.

  - Case "vterm".
    inversion aeqt; subst; clear aeqt.
    simpl; auto.

  - Case "sterm".
    inversion aeqt; subst; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeqt; exrepnd; subst.
    allrw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; destruct guo.

    + destruct op; allsimpl; tcsp; destruct c; allsimpl; tcsp; ginv.
      unfold subst_utok.
      applydup (alphaeq_utok_sub_implies_alphaeq_utok_sub_find s1 s2 g0) in aeqs.
      repndors; exrepnd; allrw.

      * apply alphaeq_eq; auto.

      * apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
        introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
        destruct a0 as [l1 t1].
        destruct a as [l2 t2]; allsimpl.
        applydup aeqt0 in i1; applydup in_combine in i1; repnd.
        allrw <- @alphaeqbt_eq.
        rw @alphaeqbt_all in i0.
        pose proof (i0 (allvars (subst_utokens_aux t1 s1)
                                ++ allvars (subst_utokens_aux t2 s2)
                                ++ free_vars_utok_sub s1
                                ++ bound_vars_utok_sub s1
                                ++ free_vars_utok_sub s2
                                ++ bound_vars_utok_sub s2
                   )) as a; clear i0.
        inversion a as [? ? ? ? ? len1 len2 disj norep aeq]; subst; clear a; allsimpl.
        apply (alphaeq_vs_implies_less _ _ _ []) in aeq; auto.
        allrw disjoint_app_r; repnd.
        apply (aeqbt _ vs); simpl; auto; allrw disjoint_app_r; auto.
        allrw @alphaeq_eq.
        allrw @cswap_subst_utokens_aux.
        disj_flat_map; allsimpl; allrw disjoint_app_r; repnd.
        pose proof (alphaeq_utok_sub_cswap_utok_sub l1 vs s1) as h1.
        repeat (autodimp h1 hyp); eauto 2 with slow.
        pose proof (alphaeq_utok_sub_cswap_utok_sub l2 vs s2) as h2.
        repeat (autodimp h2 hyp); eauto 2 with slow.
        applydup @alphaeq_utok_sub_preserves_free_vars in h1 as k1.
        applydup @alphaeq_utok_sub_preserves_free_vars in h2 as k2.
        apply (ind t1 _ l1); allrw @osize_cswap; eauto 4 with slow;
        try (rw k1); try (rw k2); rw @bound_vars_cswap;
        apply disjoint_swapbvars; eauto 2 with slow.

    + apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
      introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
      destruct a0 as [l1 t1]; destruct a as [l2 t2]; allsimpl.
      applydup aeqt0 in i1; applydup in_combine in i1; repnd.
      allrw <- @alphaeqbt_eq.
      rw @alphaeqbt_all in i0.
      pose proof (i0 (allvars (subst_utokens_aux t1 s1)
                              ++ allvars (subst_utokens_aux t2 s2)
                              ++ free_vars_utok_sub s1
                              ++ bound_vars_utok_sub s1
                              ++ free_vars_utok_sub s2
                              ++ bound_vars_utok_sub s2
                 )) as a; clear i0.
      inversion a as [? ? ? ? ? len1 len2 disj norep aeq]; subst; clear a; allsimpl.
      apply (alphaeq_vs_implies_less _ _ _ []) in aeq; auto.
      allrw disjoint_app_r; repnd.
      apply (aeqbt _ vs); simpl; auto; allrw disjoint_app_r; auto.
      allrw @alphaeq_eq.
      allrw @cswap_subst_utokens_aux.
      disj_flat_map; allsimpl; allrw disjoint_app_r; repnd.
      pose proof (alphaeq_utok_sub_cswap_utok_sub l1 vs s1) as h1.
      repeat (autodimp h1 hyp); eauto 2 with slow.
      pose proof (alphaeq_utok_sub_cswap_utok_sub l2 vs s2) as h2.
      repeat (autodimp h2 hyp); eauto 2 with slow.
      applydup @alphaeq_utok_sub_preserves_free_vars in h1 as k1.
      applydup @alphaeq_utok_sub_preserves_free_vars in h2 as k2.
      apply (ind t1 _ l1); allrw @osize_cswap; eauto 4 with slow;
      try (rw k1); try (rw k2); rw @bound_vars_cswap;
      apply disjoint_swapbvars; eauto 2 with slow.
Qed.

Lemma alpha_eq_subst_utokens {o} :
  forall (t1 t2 : @NTerm o) (s1 s2 : @utok_sub o),
    alpha_eq t1 t2
    -> alphaeq_utok_sub s1 s2
    -> alpha_eq (subst_utokens t1 s1) (subst_utokens t2 s2).
Proof.
  introv aeqt aeqs.
  pose proof (unfold_subst_utokens s1 t1) as h.
  pose proof (unfold_subst_utokens s2 t2) as k.
  exrepnd.
  rw h0; rw k0.
  apply alpha_eq_subst_utokens_aux; eauto with slow.
Qed.

Lemma lsubst_aux_subst_utokens_disj_cl {o} :
  forall (t : @NTerm o) sub usub,
    disjoint (get_utokens_sub sub) (utok_sub_dom usub)
    -> disjoint (free_vars_utok_sub usub) (dom_sub sub)
    -> disjoint (free_vars_utok_sub usub) (sub_bound_vars sub)
    -> cl_sub sub
    -> alpha_eq (lsubst_aux (subst_utokens t usub) sub)
                (subst_utokens (lsubst_aux t sub) usub).
Proof.
  introv d1 d2 d3 cl.
  pose proof (unfold_subst_utokens usub t) as h; exrepnd.
  rw h0.
  rw @lsubst_aux_subst_utokens_aux_disj; auto.
  pose proof (unfold_subst_utokens usub (lsubst_aux t sub)) as k; exrepnd.
  rw k0.
  apply alpha_eq_subst_utokens_aux; eauto with slow.

  - apply disjoint_sym.
    apply substitution.disjoint_bound_vars_lsubst_aux;
    allrw <- @sub_free_vars_is_flat_map_free_vars_range;
    allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
    eauto with slow.

    + rw @sub_free_vars_if_cl_sub; auto.

    + rw disjoint_app_l; dands; eauto with slow.

  - eapply alpha_eq_trans;[|exact k1].
    apply lsubst_aux_alpha_congr2; eauto with slow.

    + rw @sub_free_vars_if_cl_sub; auto.

    + rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma subst_aux_subst_utokens_disj_cl {o} :
  forall (t : @NTerm o) v u usub,
    disjoint (get_utokens u) (utok_sub_dom usub)
    -> !LIn v (free_vars_utok_sub usub)
    -> closed u
    -> disjoint (free_vars_utok_sub usub) (bound_vars u)
    -> alpha_eq (subst_aux (subst_utokens t usub) v u)
                (subst_utokens (subst_aux t v u) usub).
Proof.
  introv d1 ni cl d2.
  unfold subst_aux.
  apply lsubst_aux_subst_utokens_disj_cl; allsimpl;
  allrw app_nil_r; eauto with slow.
  - unfold get_utokens_sub; simpl; rw app_nil_r; auto.
  - rw disjoint_singleton_r; auto.
Qed.

(*
(* !!MOVE to computation1 *)
Lemma get_fresh_atom_not_in {o} :
  forall lib (t : @NTerm o),
    !LIn (get_fresh_atom lib t) (atom_sub_range (ce_atom_sub lib)).
Proof.
  introv i.
  unfold get_fresh_atom in i.
  destruct (fresh_atom o (get_utoks_norep lib t)); allsimpl.
  unfold get_utoks_norep in n.
  allrw remove_repeats_app; allrw in_app_iff; allrw not_over_or; repnd.
  allrw in_remove_repeats.
  unfold get_utokens_ce in n; allrw in_app_iff; allrw not_over_or; repnd; sp.
Qed.
*)

Fixpoint atom_sub_swap_vars {o} (sub : @atom_sub o) v1 v2 :=
  match sub with
    | [] => []
    | (v,a) :: s =>
      if deq_nvar v1 v
      then (v2,a) :: s
      else (v,a) :: atom_sub_swap_vars s v1 v2
  end.

Definition ce_atom_sub_swap_vars {o} (ce : @compenv o) v1 v2 :=
  mk_ce (ce_library ce) (atom_sub_swap_vars (ce_atom_sub ce) v1 v2).

Lemma find_atom_ce_atom_sub_swap_vars_not_in {o} :
  forall (lib : @compenv o) v1 v2 v,
    v <> v1
    -> v <> v2
    -> find_atom (ce_atom_sub (ce_atom_sub_swap_vars lib v1 v2)) v
       = find_atom (ce_atom_sub lib) v.
Proof.
  introv d1 d2.
  destruct lib; allsimpl.
  induction ce_atom_sub; simpl; auto.
  destruct a; allsimpl; boolvar; allsimpl; boolvar; tcsp.
Qed.

(**

  we say that [sub2] is compatible with [sub1] w.r.t. term [t] if its
  variables are the same as [sub1]'s except that we might have changed
  the ones that are shadowed and the ones that do not occur free in [t].

*)
Inductive atom_sub_compat {o}
          (t : @NTerm o)
: list NVar -> list NVar -> @atom_sub o -> @atom_sub o -> Type :=
| asc_nil : forall vs1 vs2, atom_sub_compat t vs1 vs2 [] []
| asc_cons1 : (* we leave the variable alone *)
    forall v a vs1 vs2 s1 s2,
      atom_sub_compat t (v :: vs1) (v :: vs2) s1 s2
      -> atom_sub_compat t vs1 vs2 ((v,a) :: s1) ((v,a) :: s2)
| asc_cons2 :  (* we change a variable that's either not free in t or shadowed *)
    forall v1 v2 a vs1 vs2 s1 s2,
      (!LIn v1 (free_vars t) [+] LIn v1 vs1)
      -> (!LIn v2 (free_vars t) [+] LIn v2 vs2)
      -> atom_sub_compat t (v1 :: vs1) (v2 :: vs2) s1 s2
      -> atom_sub_compat t vs1 vs2 ((v1,a) :: s1) ((v2,a) :: s2).
Hint Constructors atom_sub_compat.

Definition atom_sub_compatible {o} (t : @NTerm o) (sub1 sub2 : @atom_sub o) :=
  atom_sub_compat t [] [] sub1 sub2.

Lemma find_atom_ce_atom_sub_change_if_in_aux {o} :
  forall lib (t : @NTerm o) s v vs1 vs2,
    atom_sub_compat t vs1 vs2 (ce_atom_sub lib) s
    -> !LIn v vs1
    -> !LIn v vs2
    -> LIn v (free_vars t)
    -> find_atom (ce_atom_sub (ce_change_atom_sub lib s)) v
       = find_atom (ce_atom_sub lib) v.
Proof.
  introv.
  unfold ce_change_atom_sub; simpl.
  remember (ce_atom_sub lib) as sub; clear Heqsub lib.
  revert s vs1 vs2.
  induction sub; introv compat ni1 ni2 i; allsimpl.

  - inversion compat; subst; auto.

  - destruct a.
    inversion compat as [|? ? ? ? ? ? c|? ? ? ? ? ? ? o1 o2 c]; subst; clear compat.

    + simpl; boolvar; tcsp.
      eapply IHsub; eauto; simpl; tcsp.

    + simpl; boolvar; tcsp.
      eapply IHsub; eauto; simpl; tcsp.
Qed.

Lemma find_atom_ce_atom_sub_change_if_in {o} :
  forall lib (t : @NTerm o) s v,
    atom_sub_compatible t (ce_atom_sub lib) s
    -> LIn v (free_vars t)
    -> find_atom (ce_atom_sub (ce_change_atom_sub lib s)) v
       = find_atom (ce_atom_sub lib) v.
Proof.
  introv compat i.
  eapply find_atom_ce_atom_sub_change_if_in_aux; eauto; allsimpl; tcsp.
Qed.

Lemma atom_sub_compat_change_term_aux {o} :
  forall (t u : @NTerm o) s1 s2 vs1 vs2,
    subvars (free_vars u) (free_vars t)
    -> atom_sub_compat t vs1 vs2 s1 s2
    -> atom_sub_compat u vs1 vs2 s1 s2.
Proof.
  induction s1; introv sv compat;
  inversion compat as [|? ? ? ? ? ? c|? ? ? ? ? ? ? o1 o2 c]; subst; clear compat; tcsp.
  apply asc_cons2; auto; repndors; tcsp;
  rw subvars_prop in sv;
  left; intro k; apply sv in k; sp.
Qed.

Lemma atom_sub_compat_change_term {o} :
  forall (t u : @NTerm o) s1 s2,
    subvars (free_vars u) (free_vars t)
    -> atom_sub_compatible t s1 s2
    -> atom_sub_compatible u s1 s2.
Proof.
  introv sv compat.
  eapply atom_sub_compat_change_term_aux; eauto.
Qed.

Lemma compute_step_fresh_if_isvalue_like0 {o} :
  forall lib v (u t : @NTerm o) comp a,
    isvalue_like t
    -> compute_step_fresh lib NFresh u v [] t [] comp a
       = csuccess (pushdown_fresh v t).
Proof.
  introv isv.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; auto.
  - apply isexc_implies2 in isv; exrepnd; subst; auto.
Qed.

Lemma compute_step_fresh_if_isnoncan_like0 {o} :
  forall lib v (u t : @NTerm o) comp a,
    isnoncan_like t
    -> compute_step_fresh lib NFresh u v [] t [] comp a
       = on_success comp (fun u => mk_fresh v (subst_utokens u [(a,mk_var v)])).
Proof.
  introv isc.
  unfold isnoncan_like in isc; repndors.
  - apply isnoncan_implies in isc; exrepnd; subst; auto.
  - apply isabs_implies in isc; exrepnd; subst; auto.
Qed.

Lemma atom_sub_compat_remove_nvars {o} :
  forall s1 s2 (t u : @NTerm o) vs1 vs2 vs,
    subvars (remove_nvars vs (free_vars u)) (free_vars t)
    -> atom_sub_compat t vs1 vs2 s1 s2
    -> atom_sub_compat u (vs1 ++ vs) (vs2 ++ vs) s1 s2.
Proof.
  induction s1; introv sv compat;
  inversion compat as [|? ? ? ? ? ? c|? ? ? ? ? ? ? o1 o2 c]; subst; clear compat; tcsp.
  - apply asc_cons1.
    allrw app_comm_cons.
    eapply IHs1; eauto.
  - apply asc_cons2; allrw in_app_iff; tcsp.
    + clear o2.
      destruct (in_deq _ deq_nvar v1 vs); tcsp.
      repndors; tcsp.
      left; intro k.
      rw subvars_prop in sv; pose proof (sv v1) as h; autodimp h hyp.
      rw in_remove_nvars; sp.
    + clear o1.
      destruct (in_deq _ deq_nvar v2 vs); tcsp.
      repndors; tcsp.
      left; intro k.
      rw subvars_prop in sv; pose proof (sv v2) as h; autodimp h hyp.
      rw in_remove_nvars; sp.
    + allrw app_comm_cons.
      eapply IHs1; eauto.
Qed.

Lemma atom_sub_compat_remove_nvars0 {o} :
  forall s1 s2 (t u : @NTerm o) vs,
    subvars (remove_nvars vs (free_vars u)) (free_vars t)
    -> atom_sub_compat t [] [] s1 s2
    -> atom_sub_compat u vs vs s1 s2.
Proof.
  introv sv compat.
  apply (atom_sub_compat_remove_nvars s1 s2 t u [] [] vs); auto.
Qed.

Lemma atom_sub_range_if_compatible {o} :
  forall (s1 s2 : @atom_sub o) t vs1 vs2,
    atom_sub_compat t vs1 vs2 s1 s2
    -> atom_sub_range s1 = atom_sub_range s2.
Proof.
  induction s1; introv compat;
  inversion compat as [|? ? ? ? ? ? c|? ? ? ? ? ? ? o1 o2 c];
  subst; clear compat; allsimpl; tcsp; f_equal;
  eapply IHs1; eauto.
Qed.

(*
Lemma get_fresh_atom_ce_change_atom_sub {o} :
  forall lib s (t u : @NTerm o),
    atom_sub_compatible u (ce_atom_sub lib) s
    -> get_fresh_atom (ce_change_atom_sub lib s) t
       = get_fresh_atom lib t.
Proof.
  introv compat.
  unfold get_fresh_atom; simpl.
  unfold get_utoks_norep; simpl.
  unfold get_utokens_ce; simpl.
  rw (atom_sub_range_if_compatible (ce_atom_sub lib) s u [] []); auto.
Qed.
*)

Lemma ce_change_atom_add_atom_sub {o} :
  forall lib v1 v2 a (s : @atom_sub o),
    ce_change_atom_sub (add_atom_sub lib v1 a) ((v2,a) :: s)
    = add_atom_sub (ce_change_atom_sub lib s) v2 a.
Proof. sp. Qed.

Lemma cl_lsubst_aux_trivial2 {o} :
  forall (t : @NTerm o) (sub : Substitution),
    cl_sub sub
    -> free_vars (lsubst_aux t sub)
       = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl; allsimpl.

  - Case "vterm".
    remember (sub_find sub v) as sf; destruct sf; symmetry in Heqsf; allsimpl.
    + apply sub_find_some in Heqsf.
      rw @cl_sub_eq2 in cl; applydup cl in Heqsf.
      rw Heqsf0.
      rw remove_nvars_cons_r; boolvar.
      * rw remove_nvars_nil_r; auto.
      * destruct Heqb.
        apply in_sub_eta in Heqsf; sp.
    + apply sub_find_none2 in Heqsf.
      rw remove_nvars_cons_r; boolvar; tcsp.
      rw remove_nvars_nil_r; auto.

  - Case "sterm".
    allrw remove_nvars_nil_r; auto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    rw remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; allsimpl.
    rw (ind t l); eauto with slow.
    rw <- @dom_sub_sub_filter.
    rw <- remove_nvars_comp.
    rw remove_nvars_comm; auto.
Qed.

Lemma wf_term_utoken {o} :
  forall a, @wf_term o (mk_utoken a).
Proof.
  introv; apply nt_wf_eq.
  apply nt_wf_utoken.
Qed.
Hint Resolve wf_term_utoken : slow.

Lemma wf_utok_sub_nil {o} :
  @wf_utok_sub o [].
Proof.
  unfold wf_utok_sub; simpl; sp.
Qed.
Hint Resolve wf_utok_sub_nil : slow.

Lemma wf_utok_sub_cons {o} :
  forall a (t : @NTerm o) s,
    wf_term t -> wf_utok_sub s -> wf_utok_sub ((a,t) :: s).
Proof.
  introv w1 w2.
  unfold wf_utok_sub; introv k; allsimpl; repndors; cpx.
  apply w2 in k; auto.
Qed.
Hint Resolve wf_utok_sub_cons : slow.

Definition get_utokens_sosub {o} (sub : @SOSub o) :=
  get_utokens_bs (sorange sub).

Lemma get_utokens_so_swap {o} :
  forall s (t : @SOTerm o),
    get_utokens_so (so_swap s t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.

  - Case "soterm".
    apply app_if; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma get_utokens_so_soalphaeq {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> get_utokens_so t1 = get_utokens_so t2.
Proof.
  soterm_ind1s t1 as [v ts ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; simpl; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    apply ind in i0; auto.

  - Case "soterm".
    inversion aeq as [| ? ? ? len imp]; subst; clear aeq.
    simpl.
    apply app_if; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    destruct t1 as [l1 t1].
    destruct t2 as [l2 t2].
    simpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    repeat (autodimp h hyp).
    { rw @sosize_so_swap; auto. }
    pose proof (h (so_swap (mk_swapping l2 vs) t2)) as k; clear h.
    autodimp k hyp.
    allrw @get_utokens_so_swap; auto.
Qed.

Lemma get_utokens_sosub_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> get_utokens_sosub sub1 = get_utokens_sosub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq as [|? ? ? ? ? ask asu]; subst.
  unfold get_utokens_sosub; simpl.
  destruct sk1, sk2.
  fold (get_utokens_sosub sub1).
  fold (get_utokens_sosub sub2).
  rw (IHsub1 sub2); auto.
  apply app_if; auto.
  unfold alphaeq_sk in ask; allsimpl.
  inversion ask as [? ? ? ? ? len1 len2 disj norep a]; subst.
  apply alphaeq_eq in a.
  apply alphaeq_preserves_utokens in a.
  allrw @get_utokens_cswap; auto.
Qed.

Lemma get_utokens_lsubst_aux_subset {o} :
  forall (t : @NTerm o) sub,
    subset
      (get_utokens (lsubst_aux t sub))
      (get_utokens t ++ get_utokens_sub sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as f.
    symmetry in Heqf; destruct f; simpl; auto.
    apply sub_find_some in Heqf.
    apply subsetSingleFlatMap.
    apply in_range_iff; eexists; eauto.

  - Case "oterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    introv i.
    allrw lin_flat_map; exrepnd.
    destruct x0; allsimpl.
    apply (ind n l i1 (sub_filter sub l)) in i0.
    allrw in_app_iff; dorn i0.
    + left.
      rw lin_flat_map.
      exists (bterm l n); simpl; sp.
    + right.
      apply get_utokens_sub_filter_subset in i0; auto.
Qed.

Lemma get_utokens_apply_list {o} :
  forall ts (t : @NTerm o),
    get_utokens (apply_list t ts) = get_utokens t ++ flat_map get_utokens ts.
Proof.
  induction ts; simpl; introv; allrw app_nil_r; auto.
  rw IHts; simpl; allrw app_nil_r.
  rw app_assoc; auto.
Qed.

Lemma get_cutokens_onil {o} :
  forall (t : @NTerm o),
    get_cutokens t = oapp (get_cutokens t) onil.
Proof.
  destruct t as [v|f ind|op bs ind]; introv; allsimpl; eauto 3 with slow.
  rw @oappl_app_as_oapp.
  rw @oapp_assoc.
  f_equal.
  unfold oapp, onil.
  rw <- @oappl_nil.
  rw @oappl_cons_oappl2; simpl.
  rw @oappl_cons_oappl; allrw app_nil_r; auto.
Qed.

Lemma get_cutokens_apply_list {o} :
  forall ts (t : @NTerm o),
    get_cutokens (apply_list t ts) = oapp (get_cutokens t) (oappl (map get_cutokens ts)).
Proof.
  induction ts; simpl; introv; allrw app_nil_r; autorewrite with slow.
  - apply get_cutokens_onil.
  - rw IHts; simpl.
    unfold oapp.
    rw @oappl_cons_oappl; simpl.
    rw @oappl_cons_oappl3; simpl.
    rw @oappl_cons_oappl2; simpl.
    allrw app_nil_r; auto.
Qed.

Definition get_utokens_bs {o} (bs : list (@BTerm o)) :=
  flat_map get_utokens_b bs.

Lemma sorange_sosub_filter_subset {o} :
  forall (sub : @SOSub o) l,
    subset (sorange (sosub_filter sub l)) (sorange sub).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; boolvar; simpl.
  - apply subset_cons1; auto.
  - apply subset_cons2; auto.
Qed.

Lemma get_utokens_sosub_filter_subset {o} :
  forall (sub : @SOSub o) l,
    subset (get_utokens_sosub (sosub_filter sub l)) (get_utokens_sosub sub).
Proof.
  unfold get_utokens_sosub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  apply sorange_sosub_filter_subset in i1; auto.
Qed.

Lemma get_utokens_sosub_aux_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens (sosub_aux sub t))
      (get_utokens_so t ++ get_utokens_sosub sub).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as f.
    symmetry in Heqf; destruct f; simpl; auto.
    + destruct s.
      apply sosub_find_some in Heqf; repnd.
      introv i.
      apply get_utokens_lsubst_aux_subset in i.
      allrw in_app_iff.
      dorn i.
      * right.
        rw lin_flat_map.
        exists (bterm l n); simpl; dands; auto.
        apply in_sorange.
        exists v; simpl; auto.
      * rw lin_flat_map in i; exrepnd.
        rw @range_combine in i1; allrw map_length; auto.
        rw in_map_iff in i1; exrepnd; subst.
        apply ind in i0; auto.
        allrw in_app_iff; dorn i0; tcsp.
        left.
        rw lin_flat_map; eexists; eauto.
    + apply sosub_find_none in Heqf; repnd.
      rw @get_utokens_apply_list; simpl.
      introv i.
      rw lin_flat_map in i; exrepnd.
      rw in_map_iff in i1; exrepnd; subst.
      apply ind in i0; auto.
      allrw in_app_iff; dorn i0; tcsp.
      left.
      rw lin_flat_map; eexists; eauto.

  - Case "soterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    introv i.
    allrw lin_flat_map; exrepnd.
    destruct x0; allsimpl.
    apply (ind s l i1 (sosub_filter sub (vars2sovars l))) in i0.
    allrw in_app_iff; dorn i0.
    + left.
      rw lin_flat_map.
      exists (sobterm l s); simpl; sp.
    + right.
      apply get_utokens_sosub_filter_subset in i0; auto.
Qed.

Lemma get_utokens_sosub_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens (sosub sub t))
      (get_utokens_so t ++ get_utokens_sosub sub).
Proof.
  introv.
  pose proof (unfold_sosub sub t) as h; exrepnd.
  rw h1.
  apply get_utokens_so_soalphaeq in h2; rw h2.
  rw (get_utokens_sosub_alphaeq_sosub sub sub'); eauto with slow.
  apply get_utokens_sosub_aux_subset.
Qed.

Lemma get_utokens_mk_instance {o} :
  forall vars bs (rhs : @SOTerm o),
    matching_bterms vars bs
    -> subset
         (get_utokens (mk_instance vars bs rhs))
         (get_utokens_so rhs ++ get_utokens_bs bs).
Proof.
  introv m i.
  unfold mk_instance in i.
  apply get_utokens_sosub_subset in i; allrw in_app_iff; repndors; tcsp.
  unfold get_utokens_sosub in i.
  rw @sorange_mk_abs_subst in i; auto.
Qed.

Lemma subset_eqset_r :
  forall T (s1 s2 s3 : list T),
    eqset s1 s2
    -> subset s3 s1
    -> subset s3 s2.
Proof.
  introv eqs ss i.
  apply ss in i; apply eqs in i; auto.
Qed.
Hint Resolve subset_eqset_r : slow.

Lemma utok_sub_find_none {o} :
  forall (sub : @utok_sub o) a,
    utok_sub_find sub a = None
    -> !LIn a (utok_sub_dom sub).
Proof.
  induction sub; simpl; tcsp; introv k.
  destruct a; boolvar; allsimpl; subst; ginv; tcsp.
  apply IHsub in k; tcsp.
Qed.

(*
Definition get_utokens_c_ut {p} (c : @CanonicalOp p) : list (get_patom_set p) :=
  match c with
    | NUTok u => [u]
    | _ => []
  end.

Definition get_utokens_en_ot {o} (en : @exc_name o) : list (get_patom_set o) :=
  match en with
    | None => []
    | Some a => [a]
  end.

Definition get_utokens_nc_ot {p} (c : @NonCanonicalOp p) : list (get_patom_set p) :=
  match c with
    | NTryCatch en => get_utokens_en en
    | _ => []
  end.

Definition get_utokens_o_ut {p} (o : @Opid p) : list (get_patom_set p) :=
  match o with
    | Can c => get_utokens_c_ut c
    | _ => []
  end.

Definition get_utokens_o_ot {p} (o : @Opid p) : list (get_patom_set p) :=
  match o with
    | NCan nc => get_utokens_nc_ot nc
    | Exc en => get_utokens_en_ot en
    | _ => []
  end.

Fixpoint get_utokens_ut {p} (t : @NTerm p) : list (get_patom_set p) :=
  match t with
    | vterm _ => []
    | oterm o bterms => (get_utokens_o_ut o) ++ (flat_map get_utokens_b_ut bterms)
  end
with get_utokens_b_ut {p} (bt : @BTerm p) : list (get_patom_set p) :=
       match bt with
         | bterm _ t => get_utokens_ut t
       end.

Fixpoint get_utokens_ot {p} (t : @NTerm p) : list (get_patom_set p) :=
  match t with
    | vterm _ => []
    | oterm o bterms => (get_utokens_o_ot o) ++ (flat_map get_utokens_b_ot bterms)
  end
with get_utokens_b_ot {p} (bt : @BTerm p) : list (get_patom_set p) :=
       match bt with
         | bterm _ t => get_utokens_ot t
       end.

Definition get_utokens_ut_sub {o} (sub : @Sub o) :=
  flat_map get_utokens_ut (range sub).

Definition get_utokens_ot_sub {o} (sub : @Sub o) :=
  flat_map get_utokens_ot (range sub).

Lemma get_utokens_ut_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    eqset (get_utokens_ut (lsubst_aux t sub))
          (get_utokens_ut t ++ get_utokens_ut_sub (sub_keep_first sub (free_vars t))).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    rw @sub_keep_singleton.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
    unfold get_utokens_ut_sub; simpl; allrw app_nil_r; auto.

  - Case "oterm".
    rw <- app_assoc.
    apply eqset_app_if; auto.
    allrw flat_map_map; unfold compose.
    introv; allrw in_app_iff; allrw lin_flat_map; split; intro k; exrepnd.
    + destruct x0 as [l t]; allsimpl.
      pose proof (ind t l k1 (sub_filter sub l)) as h; clear ind.
      apply h in k0; clear h; allrw in_app_iff; repndors.
      * left; eexists; eauto.
      * right.
        allrw lin_flat_map; exrepnd.
        exists x0; dands; auto.
        allrw @in_range_iff; exrepnd.
        exists v.
        allrw @in_sub_keep_first; repnd; dands; auto.
        { allrw @sub_find_sub_filter_eq; boolvar; ginv; auto. }
        { allrw lin_flat_map; allrw @sub_find_sub_filter_eq; boolvar; ginv.
          eexists; dands; eauto; allsimpl; allrw in_remove_nvars; sp. }
    + repndors; exrepnd.
      * destruct x0 as [l t]; allsimpl.
        eexists; dands; eauto; allsimpl.
        pose proof (ind t l k1 (sub_filter sub l)) as h; clear ind.
        apply h; clear h; rw in_app_iff; sp.
      * allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw lin_flat_map; exrepnd.
        destruct x1 as [l t]; allsimpl.
        allrw in_remove_nvars; repnd.
        eexists; dands; eauto; allsimpl.
        pose proof (ind t l k2 (sub_filter sub l)) as h; clear ind.
        apply h; clear h; rw in_app_iff; sp.
        right.
        allrw lin_flat_map.
        exists x0; dands; auto.
        rw @in_range_iff.
        exists v.
        rw @in_sub_keep_first; dands; auto.
        rw @sub_find_sub_filter_eq; boolvar; tcsp.
Qed.

Lemma get_utokens_ot_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    eqset (get_utokens_ot (lsubst_aux t sub))
          (get_utokens_ot t ++ get_utokens_ot_sub (sub_keep_first sub (free_vars t))).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    rw @sub_keep_singleton.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
    unfold get_utokens_ot_sub; simpl; allrw app_nil_r; auto.

  - Case "oterm".
    rw <- app_assoc.
    apply eqset_app_if; auto.
    allrw flat_map_map; unfold compose.
    introv; allrw in_app_iff; allrw lin_flat_map; split; intro k; exrepnd.
    + destruct x0 as [l t]; allsimpl.
      pose proof (ind t l k1 (sub_filter sub l)) as h; clear ind.
      apply h in k0; clear h; allrw in_app_iff; repndors.
      * left; eexists; eauto.
      * right.
        allrw lin_flat_map; exrepnd.
        exists x0; dands; auto.
        allrw @in_range_iff; exrepnd.
        exists v.
        allrw @in_sub_keep_first; repnd; dands; auto.
        { allrw @sub_find_sub_filter_eq; boolvar; ginv; auto. }
        { allrw lin_flat_map; allrw @sub_find_sub_filter_eq; boolvar; ginv.
          eexists; dands; eauto; allsimpl; allrw in_remove_nvars; sp. }
    + repndors; exrepnd.
      * destruct x0 as [l t]; allsimpl.
        eexists; dands; eauto; allsimpl.
        pose proof (ind t l k1 (sub_filter sub l)) as h; clear ind.
        apply h; clear h; rw in_app_iff; sp.
      * allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw lin_flat_map; exrepnd.
        destruct x1 as [l t]; allsimpl.
        allrw in_remove_nvars; repnd.
        eexists; dands; eauto; allsimpl.
        pose proof (ind t l k2 (sub_filter sub l)) as h; clear ind.
        apply h; clear h; rw in_app_iff; sp.
        right.
        allrw lin_flat_map.
        exists x0; dands; auto.
        rw @in_range_iff.
        exists v.
        rw @in_sub_keep_first; dands; auto.
        rw @sub_find_sub_filter_eq; boolvar; tcsp.
Qed.

Lemma get_utokens_ut_swap {o} :
  forall s (t : @NTerm o),
    get_utokens_ut (swap s t) = get_utokens_ut t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_utokens_ot_swap {o} :
  forall s (t : @NTerm o),
    get_utokens_ot (swap s t) = get_utokens_ot t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma alphaeq_preserves_utokens_ut {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_utokens_ut t1 = get_utokens_ut t2.
Proof.
  nterm_ind1s t1 as [v1|op1 bs1 ind1] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply f_equal.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    applydup aeq0 in i as k.
    apply alphaeqbt_eq in k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    applydup in_combine in i; repnd.
    pose proof (ind1 t1
                     (swap (mk_swapping l1 vs) t1)
                     l1) as h;
      repeat (autodimp h hyp); allrw @size_swap; auto.
    pose proof (h (swap (mk_swapping l2 vs) t2)) as x; clear h.
    apply alphaeq_eq in a.
    autodimp x hyp.
    allrw @get_utokens_ut_swap; auto.
Qed.

Lemma alphaeq_preserves_utokens_ot {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_utokens_ot t1 = get_utokens_ot t2.
Proof.
  nterm_ind1s t1 as [v1|op1 bs1 ind1] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply f_equal.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    applydup aeq0 in i as k.
    apply alphaeqbt_eq in k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    applydup in_combine in i; repnd.
    pose proof (ind1 t1
                     (swap (mk_swapping l1 vs) t1)
                     l1) as h;
      repeat (autodimp h hyp); allrw @size_swap; auto.
    pose proof (h (swap (mk_swapping l2 vs) t2)) as x; clear h.
    apply alphaeq_eq in a.
    autodimp x hyp.
    allrw @get_utokens_ot_swap; auto.
Qed.

Lemma get_utokens_ut_lsubst {o} :
  forall (t : @NTerm o) sub,
    eqset (get_utokens_ut (lsubst t sub))
          (get_utokens_ut t ++ get_utokens_ut_sub (sub_keep_first sub (free_vars t))).
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  applydup @alphaeq_preserves_utokens_ut in h1; rw h3.
  apply alphaeq_preserves_free_vars in h1; rw h1.
  apply get_utokens_ut_lsubst_aux.
Qed.

Lemma get_utokens_ot_lsubst {o} :
  forall (t : @NTerm o) sub,
    eqset (get_utokens_ot (lsubst t sub))
          (get_utokens_ot t ++ get_utokens_ot_sub (sub_keep_first sub (free_vars t))).
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  applydup @alphaeq_preserves_utokens_ot in h1; rw h3.
  apply alphaeq_preserves_free_vars in h1; rw h1.
  apply get_utokens_ot_lsubst_aux.
Qed.

Lemma get_utokens_ut_subst {o} :
  forall (t : @NTerm o) v u,
    eqset (get_utokens_ut (subst t v u))
          (get_utokens_ut t ++ if memvar v (free_vars t) then get_utokens_ut u else []).
Proof.
  introv.
  unfold subst.
  pose proof (get_utokens_ut_lsubst t [(v,u)]) as h.
  eapply eqset_trans;[exact h|].
  apply eqset_app_if; auto.
  simpl; boolvar; simpl; auto.
  unfold get_utokens_ut_sub; simpl; allrw app_nil_r; auto.
Qed.

Lemma get_utokens_ot_subst {o} :
  forall (t : @NTerm o) v u,
    eqset (get_utokens_ot (subst t v u))
          (get_utokens_ot t ++ if memvar v (free_vars t) then get_utokens_ot u else []).
Proof.
  introv.
  unfold subst.
  pose proof (get_utokens_ot_lsubst t [(v,u)]) as h.
  eapply eqset_trans;[exact h|].
  apply eqset_app_if; auto.
  simpl; boolvar; simpl; auto.
  unfold get_utokens_ot_sub; simpl; allrw app_nil_r; auto.
Qed.

Fixpoint get_utokens_so_ut {p} (t : @SOTerm p) : list (get_patom_set p) :=
  match t with
    | sovar _ ts => flat_map get_utokens_so_ut ts
    | soterm op bs => (get_utokens_o_ut op) ++ (flat_map get_utokens_b_so_ut bs)
  end
with get_utokens_b_so_ut {p} (bt : @SOBTerm p) : list (get_patom_set p) :=
       match bt with
         | sobterm _ t => get_utokens_so_ut t
       end.

Fixpoint get_utokens_so_ot {p} (t : @SOTerm p) : list (get_patom_set p) :=
  match t with
    | sovar _ ts => flat_map get_utokens_so_ot ts
    | soterm op bs => (get_utokens_o_ot op) ++ (flat_map get_utokens_b_so_ot bs)
  end
with get_utokens_b_so_ot {p} (bt : @SOBTerm p) : list (get_patom_set p) :=
       match bt with
         | sobterm _ t => get_utokens_so_ot t
       end.

Definition get_utokens_bs_ut {p} (bts : list (@BTerm p)) : list (get_patom_set p) :=
  flat_map get_utokens_b_ut bts.

Definition get_utokens_bs_ot {p} (bts : list (@BTerm p)) : list (get_patom_set p) :=
  flat_map get_utokens_b_ot bts.

Definition get_utokens_sosub_ut {o} (sub : @SOSub o) :=
  get_utokens_bs_ut (sorange sub).

Definition get_utokens_sosub_ot {o} (sub : @SOSub o) :=
  get_utokens_bs_ot (sorange sub).

Lemma get_utokens_so_ut_swap {o} :
  forall s (t : @SOTerm o),
    get_utokens_so_ut (so_swap s t) = get_utokens_so_ut t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.

  - Case "soterm".
    apply app_if; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma get_utokens_so_ot_swap {o} :
  forall s (t : @SOTerm o),
    get_utokens_so_ot (so_swap s t) = get_utokens_so_ot t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.

  - Case "soterm".
    apply app_if; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma get_utokens_so_ut_soalphaeq {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> get_utokens_so_ut t1 = get_utokens_so_ut t2.
Proof.
  soterm_ind1s t1 as [v ts ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; simpl; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    apply ind in i0; auto.

  - Case "soterm".
    inversion aeq as [| ? ? ? len imp]; subst; clear aeq.
    simpl.
    apply app_if; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    destruct t1 as [l1 t1].
    destruct t2 as [l2 t2].
    simpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    repeat (autodimp h hyp).
    { rw @sosize_so_swap; auto. }
    pose proof (h (so_swap (mk_swapping l2 vs) t2)) as k; clear h.
    autodimp k hyp.
    allrw @get_utokens_so_ut_swap; auto.
Qed.

Lemma get_utokens_so_ot_soalphaeq {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> get_utokens_so_ot t1 = get_utokens_so_ot t2.
Proof.
  soterm_ind1s t1 as [v ts ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; simpl; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    apply ind in i0; auto.

  - Case "soterm".
    inversion aeq as [| ? ? ? len imp]; subst; clear aeq.
    simpl.
    apply app_if; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    destruct t1 as [l1 t1].
    destruct t2 as [l2 t2].
    simpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    repeat (autodimp h hyp).
    { rw @sosize_so_swap; auto. }
    pose proof (h (so_swap (mk_swapping l2 vs) t2)) as k; clear h.
    autodimp k hyp.
    allrw @get_utokens_so_ot_swap; auto.
Qed.

Lemma get_utokens_sosub_ut_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> get_utokens_sosub_ut sub1 = get_utokens_sosub_ut sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq as [|? ? ? ? ? ask asu]; subst.
  unfold get_utokens_sosub_ut; simpl.
  destruct sk1, sk2.
  fold (get_utokens_sosub_ut sub1).
  fold (get_utokens_sosub_ut sub2).
  rw (IHsub1 sub2); auto.
  apply app_if; auto.
  unfold alphaeq_sk in ask; allsimpl.
  inversion ask as [? ? ? ? ? len1 len2 disj norep a]; subst.
  apply alphaeq_eq in a.
  apply alphaeq_preserves_utokens_ut in a.
  allrw @get_utokens_ut_swap; auto.
Qed.

Lemma get_utokens_sosub_ot_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> get_utokens_sosub_ot sub1 = get_utokens_sosub_ot sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq as [|? ? ? ? ? ask asu]; subst.
  unfold get_utokens_sosub_ot; simpl.
  destruct sk1, sk2.
  fold (get_utokens_sosub_ot sub1).
  fold (get_utokens_sosub_ot sub2).
  rw (IHsub1 sub2); auto.
  apply app_if; auto.
  unfold alphaeq_sk in ask; allsimpl.
  inversion ask as [? ? ? ? ? len1 len2 disj norep a]; subst.
  apply alphaeq_eq in a.
  apply alphaeq_preserves_utokens_ot in a.
  allrw @get_utokens_ot_swap; auto.
Qed.

Lemma get_utokens_ut_apply_list {o} :
  forall ts (t : @NTerm o),
    get_utokens_ut (apply_list t ts) = get_utokens_ut t ++ flat_map get_utokens_ut ts.
Proof.
  induction ts; simpl; introv; allrw app_nil_r; auto.
  rw IHts; simpl; allrw app_nil_r.
  rw app_assoc; auto.
Qed.

Lemma get_utokens_ot_apply_list {o} :
  forall ts (t : @NTerm o),
    get_utokens_ot (apply_list t ts) = get_utokens_ot t ++ flat_map get_utokens_ot ts.
Proof.
  induction ts; simpl; introv; allrw app_nil_r; auto.
  rw IHts; simpl; allrw app_nil_r.
  rw app_assoc; auto.
Qed.

Lemma get_utokens_sosub_ut_filter_subset {o} :
  forall (sub : @SOSub o) l,
    subset (get_utokens_sosub_ut (sosub_filter sub l)) (get_utokens_sosub_ut sub).
Proof.
  unfold get_utokens_sosub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  apply sorange_sosub_filter_subset in i1; auto.
Qed.

Lemma get_utokens_sosub_ot_filter_subset {o} :
  forall (sub : @SOSub o) l,
    subset (get_utokens_sosub_ot (sosub_filter sub l)) (get_utokens_sosub_ot sub).
Proof.
  unfold get_utokens_sosub; introv i.
  allrw lin_flat_map; exrepnd.
  exists x0; dands; auto.
  apply sorange_sosub_filter_subset in i1; auto.
Qed.

Lemma get_utokens_ut_sosub_aux_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens_ut (sosub_aux sub t))
      (get_utokens_so_ut t ++ get_utokens_sosub_ut sub).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as f.
    symmetry in Heqf; destruct f; simpl; auto.
    + destruct s.
      apply sosub_find_some in Heqf; repnd.
      introv i.
      apply get_utokens_ut_lsubst_aux in i.
      allrw in_app_iff.
      repndors.
      * right.
        rw lin_flat_map.
        exists (bterm l n); simpl; dands; auto.
        apply in_sorange.
        exists v; simpl; auto.
      * rw lin_flat_map in i; exrepnd.
        allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allapply @sub_find_some.
        allapply in_combine; repnd.
        rw in_map_iff in i1; exrepnd; subst.
        apply ind in i0; auto.
        allrw in_app_iff; dorn i0; tcsp.
        left.
        rw lin_flat_map; eexists; eauto.
    + apply sosub_find_none in Heqf; repnd.
      rw @get_utokens_ut_apply_list; simpl.
      introv i.
      rw lin_flat_map in i; exrepnd.
      rw in_map_iff in i1; exrepnd; subst.
      apply ind in i0; auto.
      allrw in_app_iff; dorn i0; tcsp.
      left.
      rw lin_flat_map; eexists; eauto.

  - Case "soterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    introv i.
    allrw lin_flat_map; exrepnd.
    destruct x0; allsimpl.
    apply (ind s l i1 (sosub_filter sub (vars2sovars l))) in i0.
    allrw in_app_iff; dorn i0.
    + left.
      rw lin_flat_map.
      exists (sobterm l s); simpl; sp.
    + right.
      apply get_utokens_sosub_ut_filter_subset in i0; auto.
Qed.

Lemma get_utokens_ot_sosub_aux_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens_ot (sosub_aux sub t))
      (get_utokens_so_ot t ++ get_utokens_sosub_ot sub).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as f.
    symmetry in Heqf; destruct f; simpl; auto.
    + destruct s.
      apply sosub_find_some in Heqf; repnd.
      introv i.
      apply get_utokens_ot_lsubst_aux in i.
      allrw in_app_iff.
      repndors.
      * right.
        rw lin_flat_map.
        exists (bterm l n); simpl; dands; auto.
        apply in_sorange.
        exists v; simpl; auto.
      * rw lin_flat_map in i; exrepnd.
        allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allapply @sub_find_some.
        allapply in_combine; repnd.
        rw in_map_iff in i1; exrepnd; subst.
        apply ind in i0; auto.
        allrw in_app_iff; dorn i0; tcsp.
        left.
        rw lin_flat_map; eexists; eauto.
    + apply sosub_find_none in Heqf; repnd.
      rw @get_utokens_ot_apply_list; simpl.
      introv i.
      rw lin_flat_map in i; exrepnd.
      rw in_map_iff in i1; exrepnd; subst.
      apply ind in i0; auto.
      allrw in_app_iff; dorn i0; tcsp.
      left.
      rw lin_flat_map; eexists; eauto.

  - Case "soterm".
    rw <- app_assoc.
    apply subset_app_lr; auto.
    rw flat_map_map; unfold compose.
    introv i.
    allrw lin_flat_map; exrepnd.
    destruct x0; allsimpl.
    apply (ind s l i1 (sosub_filter sub (vars2sovars l))) in i0.
    allrw in_app_iff; dorn i0.
    + left.
      rw lin_flat_map.
      exists (sobterm l s); simpl; sp.
    + right.
      apply get_utokens_sosub_ot_filter_subset in i0; auto.
Qed.

Lemma get_utokens_ut_sosub_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens_ut (sosub sub t))
      (get_utokens_so_ut t ++ get_utokens_sosub_ut sub).
Proof.
  introv.
  pose proof (unfold_sosub sub t) as h; exrepnd.
  rw h1.
  apply get_utokens_so_ut_soalphaeq in h2; rw h2.
  rw (get_utokens_sosub_ut_alphaeq_sosub sub sub'); eauto with slow.
  apply get_utokens_ut_sosub_aux_subset.
Qed.

Lemma get_utokens_ot_sosub_subset {o} :
  forall (t : @SOTerm o) sub,
    subset
      (get_utokens_ot (sosub sub t))
      (get_utokens_so_ot t ++ get_utokens_sosub_ot sub).
Proof.
  introv.
  pose proof (unfold_sosub sub t) as h; exrepnd.
  rw h1.
  apply get_utokens_so_ot_soalphaeq in h2; rw h2.
  rw (get_utokens_sosub_ot_alphaeq_sosub sub sub'); eauto with slow.
  apply get_utokens_ot_sosub_aux_subset.
Qed.

Lemma get_utokens_ut_mk_instance {o} :
  forall vars bs (rhs : @SOTerm o),
    matching_bterms vars bs
    -> subset
         (get_utokens_ut (mk_instance vars bs rhs))
         (get_utokens_so_ut rhs ++ get_utokens_bs_ut bs).
Proof.
  introv m i.
  unfold mk_instance in i.
  apply get_utokens_ut_sosub_subset in i; allrw in_app_iff; repndors; tcsp.
  unfold get_utokens_sosub_ut in i.
  rw @sorange_mk_abs_subst in i; auto.
Qed.

Lemma get_utokens_ot_mk_instance {o} :
  forall vars bs (rhs : @SOTerm o),
    matching_bterms vars bs
    -> subset
         (get_utokens_ot (mk_instance vars bs rhs))
         (get_utokens_so_ot rhs ++ get_utokens_bs_ot bs).
Proof.
  introv m i.
  unfold mk_instance in i.
  apply get_utokens_ot_sosub_subset in i; allrw in_app_iff; repndors; tcsp.
  unfold get_utokens_sosub_ot in i.
  rw @sorange_mk_abs_subst in i; auto.
Qed.

Lemma get_utokens_o_eqset_ut_ot {o} :
  forall (op : @Opid o),
    eqset (get_utokens_o op) (get_utokens_o_ut op ++ get_utokens_o_ot op).
Proof.
  introv; dopid op as [can|ncan|exc|abs] Case.
  - destruct can; allsimpl; tcsp.
  - destruct ncan; allsimpl; tcsp.
  - destruct exc; allsimpl; tcsp.
  - destruct abs; allsimpl; tcsp.
Qed.

Lemma get_utokens_eqset_ut_ot {o} :
  forall (t : @NTerm o),
    eqset (get_utokens t) (get_utokens_ut t ++ get_utokens_ot t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; allsimpl; tcsp.
  allrw in_app_iff; split; intro k; repndors; tcsp.
  - apply get_utokens_o_eqset_ut_ot in k; allrw in_app_iff; repndors; tcsp.
  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    apply h in k0; allrw in_app_iff; repndors; tcsp.
    + left; right; eexists; eauto.
    + right; right; eexists; eauto.
  - left; apply get_utokens_o_eqset_ut_ot; allrw in_app_iff; tcsp.
  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    right; eexists; dands; eauto.
    apply h; allrw in_app_iff; repndors; tcsp.
  - left; apply get_utokens_o_eqset_ut_ot; allrw in_app_iff; tcsp.
  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    right; eexists; dands; eauto.
    apply h; allrw in_app_iff; repndors; tcsp.
Qed.

Lemma get_utokens_so_eqset_ut_ot {o} :
  forall (t : @SOTerm o),
    eqset (get_utokens_so t) (get_utokens_so_ut t ++ get_utokens_so_ot t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl; tcsp;
  allrw in_app_iff; split; intro k; repndors; tcsp.
  - allrw lin_flat_map; exrepnd.
    applydup ind in k1 as h; apply h in k0.
    allrw in_app_iff; repndors; tcsp.
    + left; eexists; eauto.
    + right; eexists; eauto.

  - allrw lin_flat_map; exrepnd; eexists; dands; eauto.
    apply ind in k1; apply k1.
    allrw in_app_iff; sp.

  - allrw lin_flat_map; exrepnd; eexists; dands; eauto.
    apply ind in k1; apply k1.
    allrw in_app_iff; sp.

  - apply get_utokens_o_eqset_ut_ot in k; allrw in_app_iff; repndors; tcsp.

  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    apply h in k0; allrw in_app_iff; repndors; tcsp.
    + left; right; eexists; eauto.
    + right; right; eexists; eauto.

  - left; apply get_utokens_o_eqset_ut_ot; allrw in_app_iff; tcsp.

  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    right; eexists; dands; eauto.
    apply h; allrw in_app_iff; repndors; tcsp.

  - left; apply get_utokens_o_eqset_ut_ot; allrw in_app_iff; tcsp.

  - allrw lin_flat_map; exrepnd.
    destruct x0 as [l t]; allsimpl.
    pose proof (ind t l k1) as h; clear ind.
    right; eexists; dands; eauto.
    apply h; allrw in_app_iff; repndors; tcsp.
Qed.

Definition no_utokens_ut {o} (t : @SOTerm o) :=
  get_utokens_so_ut t = [].

Definition no_utokens_ot {o} (t : @SOTerm o) :=
  get_utokens_so_ot t = [].

Lemma no_utokens_implies_ut_ot {o} :
  forall (t : @SOTerm o),
    no_utokens t
    -> (no_utokens_ut t # no_utokens_ot t).
Proof.
  introv nut.
  unfold no_utokens in nut.
  unfold no_utokens_ut, no_utokens_ot.
  allrw <- null_iff_nil.
  allunfold @null.
  dands; introv i; pose proof (nut x) as h; destruct h;
  apply get_utokens_so_eqset_ut_ot; allrw in_app_iff; sp.
Qed.

Definition get_utokens_ut_utok_ren {o} (sub : @utok_sub o) :=
  flat_map get_utokens_ut (utok_sub_range sub).

Definition get_utokens_ot_utok_ren {o} (sub : @utok_sub o) :=
  flat_map get_utokens_ot (utok_sub_range sub).

Lemma get_utok_none_ut {o} :
  forall (op : @Opid o),
    get_utok op = None
    -> get_utokens_o_ut op = [].
Proof.
  introv e.
  dopid op as [can|ncan|exc|abs] Case; allsimpl; auto.
  destruct can; auto; ginv.
Qed.

Lemma get_utokens_ut_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_ut (subst_utokens_aux t sub))
           (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens_ut t) ++ get_utokens_ut_utok_ren sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv.

  - Case "vterm".
    allsimpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf.

      * apply utok_sub_find_some in Heqsf.
        apply in_utok_sub_eta in Heqsf; repnd.
        introv j.
        rw in_app_iff; right.
        rw lin_flat_map.
        exists n; dands; auto.

      * apply utok_sub_find_none in Heqsf.
        simpl; rw subset_cons_l; dands.

        { rw in_app_iff; left.
          rw in_diff; simpl; sp.
        }

        { apply subset_flat_map; introv j.
          rw in_map_iff in j; exrepnd; subst.
          destruct a as [l t]; allsimpl.
          pose proof (ind t l j1) as h.
          introv i; apply h in i.
          allrw in_app_iff; allrw in_diff; repndors; exrepnd; tcsp.
          allsimpl.
          left; dands; tcsp.
          destruct (get_patom_deq o g x); tcsp.
          right.
          rw lin_flat_map; eexists; dands; eauto.
        }

    + rw diff_app_r.
      allapply @get_utok_none_ut; allrw; simpl.
      allrw diff_nil; simpl.
      allrw flat_map_map; unfold compose.
      apply subset_flat_map; introv i.
      destruct x as [l t]; allsimpl.
      introv j.
      eapply ind in j; eauto.
      allrw in_app_iff; repndors; tcsp.
      left.
      rw diff_flat_map_r.
      rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma get_utokens_ut_subst_utokens_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_ut (subst_utokens t sub))
           (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens_ut t) ++ get_utokens_ut_utok_ren sub).
Proof.
  introv i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0 in i.
  apply alphaeq_preserves_utokens_ut in h1; rw h1.
  apply get_utokens_ut_subst_utokens_aux_subset; auto.
Qed.

Lemma get_utokens_ot_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_ot (subst_utokens_aux t sub))
           (get_utokens_ot t ++ get_utokens_ot_utok_ren sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv.

  - Case "vterm".
    allsimpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf.

      * apply utok_sub_find_some in Heqsf.
        apply in_utok_sub_eta in Heqsf; repnd.
        introv j.
        rw in_app_iff; right.
        rw lin_flat_map.
        exists n; dands; auto.

      * apply utok_sub_find_none in Heqsf.
        simpl; allrw flat_map_map; unfold compose.
        apply subset_flat_map; introv i j.
        destruct x as [l t]; allsimpl.
        eapply ind in j; eauto.
        allrw in_app_iff; repndors; tcsp.
        left; rw lin_flat_map; eexists; dands; eauto.

    + rw <- app_assoc.
      apply subset_app_lr; auto.
      simpl; allrw flat_map_map; unfold compose.
      apply subset_flat_map; introv i j.
      destruct x as [l t]; allsimpl.
      eapply ind in j; eauto.
      allrw in_app_iff; repndors; tcsp.
      left; rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma get_utokens_ot_subst_utokens_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_ot (subst_utokens t sub))
           (get_utokens_ot t ++ get_utokens_ot_utok_ren sub).
Proof.
  introv i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0 in i.
  apply alphaeq_preserves_utokens_ot in h1; rw h1.
  apply get_utokens_ot_subst_utokens_aux_subset; auto.
Qed.

Lemma get_utokens_ut_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    get_utokens_ut (pushdown_fresh v t)
    = get_utokens_ut t.
Proof.
  destruct t as [v|op bs]; introv; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x as [l t]; simpl.
  unfold mk_fresh_bterm; simpl; boolvar; allsimpl; auto.
  allrw app_nil_r; auto.
Qed.

Lemma get_utokens_ot_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    get_utokens_ot (pushdown_fresh v t)
    = get_utokens_ot t.
Proof.
  destruct t as [v|op bs]; introv; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x as [l t]; simpl.
  unfold mk_fresh_bterm; simpl; boolvar; allsimpl; auto.
  allrw app_nil_r; auto.
Qed.
*)

Definition get_utokens_utok_ren {o} (sub : @utok_sub o) :=
  flat_map get_utokens (utok_sub_range sub).

Lemma get_utok_none {o} :
  forall (op : @Opid o),
    get_utok op = None
    -> get_utokens_o op = [].
Proof.
  introv e.
  dopid op as [can|ncan|exc|abs] Case; allsimpl; auto.
  destruct can; auto; ginv.
Qed.

Lemma get_utokens_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens (subst_utokens_aux t sub))
           (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens t) ++ get_utokens_utok_ren sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "vterm".
    allsimpl; auto.

  - Case "sterm".
    simpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf.

      * apply utok_sub_find_some in Heqsf.
        apply in_utok_sub_eta in Heqsf; repnd.
        introv j.
        rw in_app_iff; right.
        rw lin_flat_map.
        exists n; dands; auto.

      * apply utok_sub_find_none in Heqsf.
        simpl; rw subset_cons_l; dands.

        { rw in_app_iff; left.
          rw in_diff; simpl; sp.
        }

        { apply subset_flat_map; introv j.
          rw in_map_iff in j; exrepnd; subst.
          destruct a as [l t]; allsimpl.
          pose proof (ind t l j1) as h.
          introv i; apply h in i.
          allrw in_app_iff; allrw in_diff; repndors; exrepnd; tcsp.
          allsimpl.
          left; dands; tcsp.
          destruct (get_patom_deq o g x); tcsp.
          right.
          rw lin_flat_map; eexists; dands; eauto.
        }

    + rw diff_app_r.
      allapply @get_utok_none; allrw; simpl.
      allrw diff_nil; simpl.
      allrw flat_map_map; unfold compose.
      apply subset_flat_map; introv i.
      destruct x as [l t]; allsimpl.
      introv j.
      eapply ind in j; eauto.
      allrw in_app_iff; repndors; tcsp.
      left.
      rw diff_flat_map_r.
      rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma get_utokens_subst_utokens_subset {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens (subst_utokens t sub))
           (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens t) ++ get_utokens_utok_ren sub).
Proof.
  introv i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0 in i.
  apply alphaeq_preserves_utokens in h1; rw h1.
  apply get_utokens_subst_utokens_aux_subset; auto.
Qed.

Fixpoint oremove {T} (deq : Deq T) (x : T) (o : OList T) :=
  match o with
    | OLO v => if deq x v then onil else o
    | OLL l => oappl (map (oremove deq x) l)
    | OLS f => OLS (fun n => oremove deq x (f n))
  end.

Fixpoint odiff {T} (deq : Deq T) (l : list T) (o : OList T) :=
  match l with
    | [] => o
    | x :: l => odiff deq l (oremove deq x o)
  end.

Definition get_cutokens_utok_ren {o} (sub : @utok_sub o) :=
  oappl (map get_cutokens (utok_sub_range sub)).

Lemma get_cutokens_cswap {o} :
  forall s (t : @NTerm o),
    get_cutokens (cswap s t) = get_cutokens t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  f_equal; f_equal.
  rw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma alphaeq_preserves_cutokens {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_cutokens t1 = get_cutokens t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; clear aeq; allsimpl; auto.

  - Case "sterm".
    inversion aeq as [|? ? imp|]; subst; clear aeq; allsimpl; auto.
    f_equal.
    apply functional_extensionality; introv; apply ind1; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply f_equal; f_equal.
    apply eq_maps3; auto.
    intros b1 b2 i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    applydup aeq0 in i as k.
    apply alphaeqbt_eq in k.
    inversion k as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    applydup in_combine in i; repnd.
    pose proof (ind1 t1
                     (cswap (mk_swapping l1 vs) t1)
                     l1) as h;
      repeat (autodimp h hyp); allrw @osize_cswap; eauto 3 with slow.
    pose proof (h (cswap (mk_swapping l2 vs) t2)) as x; clear h.
    apply alphaeq_eq in a.
    autodimp x hyp.
    allrw @get_cutokens_cswap; auto.
Qed.

Lemma disjoint_eqset_r :
  forall T (s s1 s2 : list T),
    eqset s1 s2
    -> disjoint s s1
    -> disjoint s s2.
Proof.
  introv eqs d i j.
  apply d in i; rw eqs in i; sp.
Qed.
Hint Resolve disjoint_eqset_r : slow.

Lemma disjoint_eqset_l :
  forall T (s s1 s2 : list T),
    eqset s1 s2
    -> disjoint s1 s
    -> disjoint s2 s.
Proof.
  introv eqs d i j.
  rw <- eqs in i.
  apply d in i; sp.
Qed.
Hint Resolve disjoint_eqset_l : slow.

Lemma implies_subvars_app_l :
  forall vs1 vs2 vs,
    subvars vs1 vs
    -> subvars vs2 vs
    -> subvars (vs1 ++ vs2) vs.
Proof.
  introv sv1 ss2; apply subvars_app_l; sp.
Qed.
Hint Resolve implies_subvars_app_l : slow.

Lemma implies_subset_app :
  forall (T : tuniv) (l1 l2 l3 : list T),
    subset l1 l3
    -> subset l2 l3
    -> subset (l1 ++ l2) l3.
Proof.
  introv s1 s2; allrw subset_app; sp.
Qed.
Hint Resolve implies_subset_app : slow.

(* !!MOVE *)
Hint Resolve subset_cons1 : slow.
Hint Resolve subset_cons2 : slow.
Hint Resolve subvars_app_lr : slow.
Hint Resolve subset_app_lr : slow.

(* !!MOVE to UsefulTypes *)
Lemma not_over_not :
  forall a,
    decidable a -> (!!a <=> a).
Proof.
  introv d; split; intro k; tcsp.
  destruct d; sp.
Qed.

Lemma free_vars_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    free_vars (pushdown_fresh v t)
    = remove_nvars [v] (free_vars t).
Proof.
  destruct t as [v|f|op bs]; introv; simpl; allrw app_nil_r; auto.
  rw remove_nvars_flat_map; unfold compose.
  unfold mk_fresh_bterms.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  unfold maybe_new_var.
  boolvar; allrw app_nil_r.
  - rw remove_nvars_comm.
    allrw remove_nvars_app_l; simpl.
    rw remove_nvars_cons_l_weak;[|apply newvar_prop].
    apply remove_nvars_if_eqvars; rw eqvars_prop; introv; split; intro k; allsimpl; tcsp.
    repndors; subst; tcsp.
  - rw remove_nvars_comm; auto.
Qed.

(*
Lemma get_markers_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    get_markers (pushdown_fresh v t)
    = get_markers t.
Proof.
  destruct t as [v|f|op bs]; introv; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x as [l t]; simpl.
  unfold mk_fresh_bterm; simpl; boolvar; allsimpl; auto.
  allrw app_nil_r; auto.
Qed.
*)

Lemma get_utokens_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    get_utokens (pushdown_fresh v t)
    = get_utokens t.
Proof.
  destruct t as [v|f|op bs]; introv; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x as [l t]; simpl.
  unfold mk_fresh_bterm; simpl; boolvar; allsimpl; auto.
  allrw app_nil_r; auto.
Qed.

Lemma oappl_get_cutokens_singleton {o} :
  forall (t : @NTerm o), oappl [get_cutokens t] = get_cutokens t.
Proof.
  introv.
  rewrite @get_cutokens_onil at 2.
  unfold oapp.
  unfold onil.
  rw <- @oappl_nil.
  rw @oappl_cons_oappl2; simpl; auto.
Qed.
Hint Rewrite @oappl_get_cutokens_singleton : slow.

Lemma get_cutokens_pushdown_fresh {o} :
  forall (t : @NTerm o) v,
    get_cutokens (pushdown_fresh v t)
    = get_cutokens t.
Proof.
  destruct t as [v|f|op bs]; introv; simpl; auto.
  f_equal; f_equal.
  unfold mk_fresh_bterms; rw map_map; unfold compose.
  apply eq_maps; introv i; destruct x as [l t]; simpl.
  autorewrite with slow; auto.
Qed.

Lemma nt_wf_fresh {o} :
  forall v (t : @NTerm o),
    nt_wf (mk_fresh v t) <=> nt_wf t.
Proof.
  introv; split; intro k.
  - inversion k as [|?|? ? imp e]; subst; allsimpl.
    pose proof (imp (bterm [v] t)) as h; autodimp h hyp.
    inversion h; subst; auto.
  - constructor; simpl; auto.
    introv h; repndors; tcsp; subst.
    constructor; auto.
Qed.

Lemma nt_wf_pushdown_fresh {o} :
  forall v (t : @NTerm o),
    nt_wf (pushdown_fresh v t) <=> nt_wf t.
Proof.
  destruct t as [x|f|op bs]; simpl; split; intro k; auto.
  - apply nt_wf_fresh; auto.
  - inversion k as [|?|? ? imp e]; subst.
    constructor.
    + intros b i.
      pose proof (imp (mk_fresh_bterm v b)) as h.
      autodimp h hyp.
      * rw in_map_iff; eexists; dands; eauto.
      * destruct b as [l t]; allsimpl.
        inversion h as [? ? x]; subst.
        apply nt_wf_fresh in x; auto.
    + rw <- e.
      unfold mk_fresh_bterms.
      rw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t].
      unfold mk_fresh_bterm; simpl; boolvar; auto.
  - inversion k as [|?|? ? imp e]; subst.
    constructor.
    + intros b i.
      rw in_map_iff in i; exrepnd; subst.
      pose proof (imp a) as h.
      autodimp h hyp.
      destruct a as [l t]; simpl.
      constructor.
      apply nt_wf_fresh; auto.
      inversion h; subst; auto.
    + rw <- e.
      unfold mk_fresh_bterms.
      rw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t].
      unfold mk_fresh_bterm; simpl; boolvar; auto.
Qed.

Lemma alpha_eq_bterm_oterm {o} :
  forall vs1 vs2 op bs (t : @NTerm o),
    alpha_eq_bterm (bterm vs1 (oterm op bs)) (bterm vs2 t)
    -> {bs' : list BTerm & t = oterm op bs'}.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; allsimpl; subst; clear aeq.
  allrw disjoint_app_r; repnd.
  repeat (rw @lsubst_lsubst_aux2 in a; tcsp; eauto with slow).
  simpl in a.
  inversion a as [|?|? ? ? len imp x e]; subst; clear a.
  destruct t; allsimpl; ginv.
  - remember (sub_find (var_ren vs2 lv) n) as sf.
    destruct sf; allsimpl; symmetry in Heqsf; subst; ginv.
    apply sub_find_varsub in Heqsf; exrepnd; ginv.
  - exists l; auto.
Qed.

Lemma implies_alpha_eq_mk_fresh_sub {o} :
  forall v v1 v2 (t1 t2 : @NTerm o),
    !LIn v (all_vars t1 ++ all_vars t2)
    -> alpha_eq (lsubst t1 (var_ren [v1] [v])) (lsubst t2 (var_ren [v2] [v]))
    -> alpha_eq (mk_fresh v1 t1) (mk_fresh v2 t2).
Proof.
  introv ni aeq.
  unfold mk_fresh.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; cpx.
  apply (al_bterm _ _ [v]); simpl; auto.
  apply disjoint_singleton_l; auto.
Qed.

Lemma lsubst_sub_disjoint_var_ren {o} :
  forall vs1 vs2 (sub : @Sub o),
    disjoint vs2 (dom_sub sub)
    -> lsubst_sub (var_ren vs1 vs2) sub = var_ren vs1 vs2.
Proof.
  induction vs1; introv d; allsimpl.
  - rw @var_ren_nil_l; auto.
  - destruct vs2; simpl; auto.
    allrw disjoint_cons_l; repnd.
    rw @var_ren_cons.
    try (fold (@var_ren o vs1 vs2)).
    rw IHvs1; auto; f_equal; f_equal.
    unfold lsubst; simpl.
    rw @sub_find_none_if; auto.
Qed.

Lemma var_ren_app {o} :
  forall vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> @var_ren o (vs1 ++ vs2) (vs3 ++ vs4)
       = var_ren vs1 vs3 ++ var_ren vs2 vs4.
Proof.
  induction vs1; introv len; allsimpl; cpx.
  destruct vs3; allsimpl; cpx.
  rw @var_ren_cons.
  f_equal.
  rw IHvs1; auto.
Qed.

Lemma sub_free_vars_var_ren {o} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> @sub_free_vars o (var_ren vs1 vs2) = vs2.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  f_equal.
  try (fold (@var_ren o vs1 vs2)).
  apply IHvs1; auto.
Qed.

Lemma move_alpha_eq_bterm_down {o} :
  forall l1 l2 op1 op2 bs1 bs2 vs1 vs2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 (oterm op1 bs1)) (bterm l2 (oterm op2 bs2))
    -> LIn (bterm vs1 t1, bterm vs2 t2) (combine bs1 bs2)
    -> alpha_eq_bterm (bterm (vs1 ++ l1) t1) (bterm (vs2 ++ l2) t2).
Proof.
  introv aeq i.
  apply alphaeq_bterm3_if
  with (lva := vs1 ++ vs2
                   ++ free_vars t1
                   ++ free_vars t2
                   ++ bound_vars t1
                   ++ bound_vars t2
       )
    in aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst; allsimpl; cpx; clear aeq.
  apply alpha_eq_if3 in a.

  allrw app_nil_r.
  allrw disjoint_app_r; repnd; allsimpl.
  apply alpha_eq_oterm_implies_combine in a; exrepnd; ginv.
  allrw map_length.
  rw <- @map_combine in a0.
  pose proof (a0 (lsubst_bterm_aux (bterm vs1 t1) (var_ren l1 lv))
                 (lsubst_bterm_aux (bterm vs2 t2) (var_ren l2 lv)))
       as h; clear a0.
  autodimp h hyp.
  { rw in_map_iff; eexists; dands; eauto. }

  simpl in h.
  apply alphaeq_bterm3_if
  with (lva := l1 ++ l2
                  ++ lv
                  ++ free_vars t1
                  ++ free_vars t2
                  ++ bound_vars t1
                  ++ bound_vars t2
       )
    in h.
  inversion h as [? ? ? ? ? disj' len3 len4 norep2 a]; subst; allsimpl; cpx; clear h.
  apply alpha_eq_if3 in a.

  allrw disjoint_app_r; repnd; allsimpl.
  apply (al_bterm _ _ (lv0 ++ lv)); auto.

  - allrw disjoint_app_r.
    allrw disjoint_app_l.
    dands; eauto with slow.

  - allrw length_app; f_equal; try omega.

  - allrw length_app; f_equal; try omega.

  - apply no_repeats_app; dands; eauto with slow.

  - repeat (rw @lsubst_aux_lsubst_aux_sub_filter_var_ren in a; eauto 3 with slow; try omega).

    rw @lsubst_aux_app in a;
      allrw <- @sub_free_vars_is_flat_map_free_vars_range;
      allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
      allrw @sub_bound_vars_var_ren; auto;
      try (apply disjoint_bv_vars; auto).

    rw @lsubst_aux_app in a;
      allrw <- @sub_free_vars_is_flat_map_free_vars_range;
      allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
      allrw @sub_bound_vars_var_ren; auto;
      try (apply disjoint_bv_vars; auto).

    rw @lsubst_sub_disjoint_var_ren in a; allrw @dom_sub_var_ren; auto.
    rw @lsubst_sub_disjoint_var_ren in a; allrw @dom_sub_var_ren; auto; try omega.

    unfold lsubst.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range;
      allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
      allrw @sub_bound_vars_var_ren.
    repeat (rw @sub_free_vars_var_ren; allrw length_app; try omega).
    boolvar; allrw disjoint_app_r; repnd;
    try (complete (destruct n; dands; eauto with slow)).

    rw @var_ren_app; auto.
    rw @var_ren_app; auto; try omega.
Qed.

Lemma split_list_r :
  forall T (l : list T) n,
    n <= length l
    -> {l1 : list T
        & {l2 : list T
        & length l2 = n
        # l = l1 ++ l2}}.
Proof.
  induction l using rev_list_indT; introv e; allsimpl.
  - destruct n; try omega.
    exists ([] : list T) ([] : list T); simpl; auto.
  - destruct n; cpx.
    + exists (snoc l a) ([] : list T); simpl; allrw app_nil_r; auto.
    + pose proof (IHl n) as h; autodimp h hyp; try omega; exrepnd; subst.
      exists l1 (snoc l2 a).
      rw length_snoc.
      rw <- snoc_append_l; dands; auto.
Qed.

Lemma free_vars_lsubst_aux_subset {o} :
  forall (t : @NTerm o) (sub : Sub),
    subset (free_vars (lsubst_aux t sub))
           (remove_nvars (dom_sub sub) (free_vars t) ++ sub_free_vars sub).
Proof.
  introv.
  pose proof (free_vars_lsubst_aux_subvars t sub) as h.
  rw subvars_eq in h; auto.
Qed.

Lemma implies_alpha_eq_mk_fresh {o} :
  forall v (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv aeq.
  unfold mk_fresh.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; cpx.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma subset_bound_vars_lsubst_aux {o} :
  forall (t : @NTerm o) (sub : Sub),
    subset (bound_vars (lsubst_aux t sub))
           (bound_vars t ++ sub_bound_vars sub).
Proof.
  introv.
  pose proof (subvars_bound_vars_lsubst_aux t sub) as h.
  rw subvars_eq in h; auto.
Qed.

Lemma subset_sub_bound_vars_sub_filter {o} :
  forall (sub : @Sub o) (l : list NVar),
    subset (sub_bound_vars (sub_filter sub l)) (sub_bound_vars sub).
Proof.
  introv.
  pose proof (subvars_sub_bound_vars_sub_filter sub l) as h.
  rw subvars_eq in h; auto.
Qed.

Lemma subset_sub_free_vars_sub_filter {o} :
  forall (sub : @Sub o) (l : list NVar),
    subset (sub_free_vars (sub_filter sub l)) (sub_free_vars sub).
Proof.
  introv.
  pose proof (subvars_sub_free_vars_sub_filter sub l) as h.
  rw subvars_eq in h; auto.
Qed.

Definition alpha_eq_option {o} (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => alpha_eq t1 t2
    | None, None => True
    | _,_ => False
  end.

Definition ext_alpha_eq_subs {o} vs (sub1 sub2 : @Sub o) :=
  forall v,
    LIn v vs
    -> alpha_eq_option (sub_find sub1 v) (sub_find sub2 v).

Lemma ext_alpha_eq_subs_flat_map {o} :
  forall l (t : @NTerm o) bs (sub1 sub2 : @Sub o),
    LIn (bterm l t) bs
    -> ext_alpha_eq_subs (flat_map free_vars_bterm bs) sub1 sub2
    -> ext_alpha_eq_subs (remove_nvars l (free_vars t)) sub1 sub2.
Proof.
  introv i ext j.
  pose proof (ext v) as h.
  repeat (autodimp h hyp).
  rw lin_flat_map; eexists; dands; eauto; simpl.
Qed.

Lemma ext_alpha_eq_subst_remove_nvars_if_disjoint {o} :
  forall (sub1 sub2 : @Sub o) vs vs',
    disjoint vs' (dom_sub sub1)
    -> disjoint vs' (dom_sub sub2)
    -> ext_alpha_eq_subs (remove_nvars vs' vs) sub1 sub2
    -> ext_alpha_eq_subs vs sub1 sub2.
Proof.
  introv d1 d2 ext i.
  destruct (in_deq _ deq_nvar v vs').
  - applydup d1 in l.
    applydup d2 in l.
    repeat (rw @sub_find_none_if; auto); simpl; auto.
  - apply ext; rw in_remove_nvars; sp.
Qed.

Lemma ext_alpha_eq_subst_sub_filter {o} :
  forall (sub1 sub2 : @Sub o) vs l1 l2,
    disjoint vs l1
    -> disjoint vs l2
    -> ext_alpha_eq_subs vs sub1 sub2
    -> ext_alpha_eq_subs vs (sub_filter sub1 l1) (sub_filter sub2 l2).
Proof.
  introv d1 d2 ext i.
  allrw @sub_find_sub_filter_eq; boolvar; allsimpl; tcsp.
  - apply d1 in i; sp.
  - apply d2 in i; sp.
Qed.

Lemma ext_alpha_eq_subs_nil_l_is_disjoint {o} :
  forall l (sub : @Sub o),
    ext_alpha_eq_subs l [] sub
    <=> disjoint l (dom_sub sub).
Proof.
  induction sub; allsimpl; split; intro k; tcsp.
  - introv i; simpl; auto.
  - destruct a; allsimpl.
    apply disjoint_cons_r; dands; tcsp.
    + apply IHsub; introv i; simpl.
      applydup k in i; allsimpl; boolvar; tcsp.
    + intro h.
      applydup k in h; allsimpl; boolvar; tcsp.
  - destruct a; allsimpl.
    allrw disjoint_cons_r; repnd.
    introv i; allsimpl.
    rw <- IHsub in k0; applydup k0 in i; allsimpl; boolvar; tcsp.
Qed.

Lemma ext_alpha_eq_subs_sym {o} :
  forall l (sub1 sub2 : @Sub o),
    ext_alpha_eq_subs l sub1 sub2
    -> ext_alpha_eq_subs l sub2 sub1.
Proof.
  introv ext i.
  apply ext in i.
  remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1; tcsp;
  remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2; tcsp.
  allsimpl; eauto with slow.
Qed.
Hint Resolve ext_alpha_eq_subs_sym : slow.

Lemma ext_alpha_eq_subs_refl {o} :
  forall l (sub : @Sub o),
    ext_alpha_eq_subs l sub sub.
Proof.
  introv i.
  remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.
Qed.
Hint Resolve ext_alpha_eq_subs_refl : slow.

Definition sub_allvars {o} (sub : @Sub o) :=
  flat_map allvars (range sub).

Lemma dom_sub_swap_sub {o} :
  forall sw (sub : @Sub o),
    dom_sub (swap_sub sw sub) = swapbvars sw (dom_sub sub).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; allsimpl; f_equal; auto.
Qed.

Lemma dom_sub_cswap_sub {o} :
  forall sw (sub : @Sub o),
    dom_sub (cswap_sub sw sub) = swapbvars sw (dom_sub sub).
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; allsimpl; f_equal; auto.
Qed.

Lemma disjoint_swapbvars_remove_nvars :
  forall vs1 vs2 l,
    disjoint vs2 l
    -> disjoint vs2 (swapbvars (mk_swapping vs1 vs2) (remove_nvars vs1 l)).
Proof.
  induction l; introv d; allsimpl.
  - allrw remove_nvars_nil_r; simpl; auto.
  - allrw disjoint_cons_r; repnd.
    rw remove_nvars_cons_r; boolvar; tcsp.
    simpl.
    rw disjoint_cons_r; dands; auto.
    rw swapvar_not_in; auto.
Qed.

Lemma sub_find_swap_sub_if_not_in {o} :
  forall (sub : @Sub o) vs1 vs2 v,
    !LIn v vs2
    -> disjoint vs1 vs2
    -> disjoint vs2 (dom_sub sub)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> sub_find (swap_sub (mk_swapping vs1 vs2) sub) v
       = match sub_find (sub_filter sub vs1) v with
             | Some t => Some (swap (mk_swapping vs1 vs2) t)
             | None => None
         end.
Proof.
  induction sub; introv ni d1 d2 nr len; allsimpl; auto.
  allrw disjoint_cons_r; repnd; allsimpl.
  allsimpl; boolvar; tcsp;
  allrw @sub_find_sub_filter_eq; boolvar; tcsp;
  simpl; boolvar; tcsp.
  - pose proof (swapvar_implies3 vs1 vs2 a0) as h; repeat (autodimp h hyp); tcsp.
  - pose proof (swapvar_implies3 vs1 vs2 a0) as h; repeat (autodimp h hyp); tcsp.
  - rw swapvar_not_in in Heqb0; tcsp.
  - rw swapvar_not_in in Heqb0; tcsp.
Qed.

Lemma sub_find_cswap_sub_if_not_in {o} :
  forall (sub : @Sub o) vs1 vs2 v,
    !LIn v vs2
    -> disjoint vs1 vs2
    -> disjoint vs2 (dom_sub sub)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> sub_find (cswap_sub (mk_swapping vs1 vs2) sub) v
       = match sub_find (sub_filter sub vs1) v with
             | Some t => Some (cswap (mk_swapping vs1 vs2) t)
             | None => None
         end.
Proof.
  induction sub; introv ni d1 d2 nr len; allsimpl; auto.
  allrw disjoint_cons_r; repnd; allsimpl.
  allsimpl; boolvar; tcsp;
  allrw @sub_find_sub_filter_eq; boolvar; tcsp;
  simpl; boolvar; tcsp.
  - pose proof (swapvar_implies3 vs1 vs2 a0) as h; repeat (autodimp h hyp); tcsp.
  - pose proof (swapvar_implies3 vs1 vs2 a0) as h; repeat (autodimp h hyp); tcsp.
  - rw swapvar_not_in in Heqb0; tcsp.
  - rw swapvar_not_in in Heqb0; tcsp.
Qed.

Lemma alpha_eq_lsubst_aux_if_ext_eq {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    alpha_eq t1 t2
    -> ext_alpha_eq_subs (free_vars t1) sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv aeq ext d1 d2; allsimpl.

  - Case "vterm".
    inversion aeq; subst; allsimpl.
    pose proof (ext v1) as h.
    remember (sub_find sub1 v1) as sf1; symmetry in Heqsf1; destruct sf1;
    remember (sub_find sub2 v1) as sf2; symmetry in Heqsf2; destruct sf2;
    allsimpl; tcsp.

  - Case "sterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    allsimpl.
    applydup aeq0 in i1.
    applydup in_combine in i1; repnd; disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.
    apply alphaeqbt_eq in i0.
    rw @alphaeqbt_all in i0.
    pose proof (i0 (allvars (lsubst_aux t1 (sub_filter sub1 l1))
                            ++ allvars (lsubst_aux t2 (sub_filter sub2 l2))
                            ++ dom_sub sub1
                            ++ dom_sub sub2
                            ++ dom_sub (sub_filter sub1 l1)
                            ++ dom_sub (sub_filter sub2 l2)
                            ++ free_vars t1
                            ++ free_vars t2
                            ++ sub_allvars sub1
                            ++ sub_allvars sub2
               )) as h; clear i0.
    inversion h as [? ? ? ? ? len1 len2 disj1 norep1 a]; subst; clear h.
    allrw disjoint_app_r; repnd.
    apply (alphaeq_vs_implies_less _ _ _ []) in a; auto.
    apply alphaeq_eq in a.
    apply alphaeqbt_eq.
    apply (aeqbt _ vs); auto; allrw disjoint_app_r; dands; auto.
    apply alphaeq_eq.
    repeat (rw @lsubst_aux_cswap_cswap; eauto 3 with slow);[].
    eapply ind1; eauto; allrw @osize_cswap; eauto 3 with slow.

    + eapply ext_alpha_eq_subs_flat_map in ext; eauto.
      apply (ext_alpha_eq_subst_remove_nvars_if_disjoint _ _ _ vs);
        try (complete (rw @dom_sub_cswap_sub;
                       rw <- @dom_sub_sub_filter;
                       apply disjoint_swapbvars_remove_nvars; auto)).
      introv i; allrw in_remove_nvars; repnd.
      repeat (rw @sub_find_cswap_sub_if_not_in; eauto with slow).
      repeat (rw @sub_find_sub_filter_eq).
      boolvar; GC; allsimpl; tcsp.

      * provefalse.
        rw @free_vars_cswap in i0; eauto with slow.
        rw in_swapbvars in i0; exrepnd; subst.
        destruct (in_deq _ deq_nvar v' vs).
        { apply disj11 in l; sp. }
        destruct (in_deq _ deq_nvar v' l1).
        { pose proof (swapvar_in l1 vs v') as h; repeat (autodimp h hyp); eauto with slow. }
        rw swapvar_not_in in Heqb; auto.

      * provefalse.
        apply alphaeq_preserves_free_vars in a; rw a in i0.
        rw @free_vars_cswap in i0; eauto with slow.
        rw in_swapbvars in i0; exrepnd; subst.
        destruct (in_deq _ deq_nvar v' vs).
        { apply disj12 in l; sp. }
        destruct (in_deq _ deq_nvar v' l2).
        { pose proof (swapvar_in l2 vs v') as h; repeat (autodimp h hyp); eauto with slow. }
        rw swapvar_not_in in Heqb0; auto.

      * rw @free_vars_cswap in i0; eauto with slow.
        rw in_swapbvars in i0; exrepnd; subst.
        destruct (in_deq _ deq_nvar v' vs).
        { apply disj11 in l; sp. }
        destruct (in_deq _ deq_nvar v' l1).
        { pose proof (swapvar_in l1 vs v') as h; repeat (autodimp h hyp); eauto with slow; tcsp. }
        rw swapvar_not_in in Heqb; auto.
        rw swapvar_not_in in Heqb0; auto.
        rw swapvar_not_in in i; auto.
        rw swapvar_not_in; auto; GC.
        pose proof (ext v') as h.
        autodimp h hyp.
        { rw in_remove_nvars; sp. }
        remember (sub_find sub1 v') as sf1; symmetry in Heqsf1; destruct sf1;
        remember (sub_find sub2 v') as sf2; symmetry in Heqsf2; destruct sf2;
        allsimpl; tcsp.
        allapply @sub_find_some.
        rw @sub_free_vars_is_flat_map_free_vars_range in i7.
        rw @sub_free_vars_is_flat_map_free_vars_range in i6.
        allapply @in_sub_eta; repnd.
        unfold sub_allvars in disj0, disj13.
        disj_flat_map; allsimpl.
        pose proof (alphaeq_cswap_disj_free_vars n l1 vs) as h1.
        repeat (autodimp h1 hyp); eauto 3 with slow.
        pose proof (alphaeq_cswap_disj_free_vars n0 l2 vs) as h2.
        repeat (autodimp h2 hyp); eauto 3 with slow.
        allrw @alphaeq_eq; eauto 4 with slow.

    + rw @bound_vars_cswap.
      rw @sub_free_vars_cswap_sub; eauto with slow.
      apply disjoint_swap; eauto with slow.
      eapply subvars_disjoint_r;
        [apply subvars_sub_free_vars_sub_filter|]; auto.

    + rw @bound_vars_cswap.
      rw @sub_free_vars_cswap_sub; eauto with slow.
      apply disjoint_swap; eauto with slow.
      eapply subvars_disjoint_r;
        [apply subvars_sub_free_vars_sub_filter|]; auto.
Qed.

Lemma alpha_eq_lsubst_if_ext_eq {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    alpha_eq t1 t2
    -> ext_alpha_eq_subs (free_vars t1) sub1 sub2
    -> alpha_eq (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv aeq ext.
  pose proof (unfold_lsubst sub1 t1) as h; exrepnd; rw h0.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd; rw k0.
  apply alpha_eq_lsubst_aux_if_ext_eq; eauto with slow.
  apply alphaeq_preserves_free_vars in h1; rw <- h1; auto.
Qed.

Lemma disjoint_bv_sub_sub_filter {o} :
  forall t (sub : @Sub o) vs,
    disjoint_bv_sub t sub
    -> disjoint_bv_sub t (sub_filter sub vs).
Proof.
  introv d.
  allunfold @disjoint_bv_sub; allunfold @sub_range_sat.
  introv i.
  apply in_sub_filter in i; repnd.
  eapply d; eauto.
Qed.

Lemma lsubst_sub_disjoint {o} :
  forall (sub1 sub2 : @Sub o),
    disjoint (sub_free_vars sub1) (dom_sub sub2)
    -> disjoint (sub_free_vars sub2) (sub_bound_vars sub1)
    -> lsubst_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv d1 d2; allsimpl; auto.
  destruct a as [v t]; allsimpl.
  allrw disjoint_app_r.
  allrw disjoint_app_l.
  repnd.
  rw IHsub1; auto.
  f_equal; f_equal.
  apply lsubst_trivial3; auto.
  introv i.
  allrw @sub_free_vars_is_flat_map_free_vars_range.
  apply in_sub_eta in i; repnd.
  disj_flat_map.
  dands; auto.
  apply disjoint_sym in d0; apply d0 in i0; auto.
Qed.

Lemma maybe_new_var_in_implies {o} :
  forall v l (t : @NTerm o),
    LIn (maybe_new_var v l t) (free_vars t)
    -> (!LIn v l # maybe_new_var v l t = v).
Proof.
  introv i.
  allunfold @maybe_new_var; boolvar; tcsp.
  apply newvar_prop in i; sp.
Qed.

Lemma maybe_new_var_diff_implies {o} :
  forall v l (t : @NTerm o),
    v <> maybe_new_var v l t
    -> (LIn v l # maybe_new_var v l t = newvar t).
Proof.
  introv i.
  allunfold @maybe_new_var; boolvar; tcsp.
Qed.

Lemma implies_alpha_eq_pushdown_fresh {o} :
  forall v1 v2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm [v1] t1) (bterm [v2] t2)
    -> alpha_eq (pushdown_fresh v1 t1) (pushdown_fresh v2 t2).
Proof.
  destruct t1 as [x1|f1|op1 bs1]; destruct t2 as [x2|f2|op2 bs2];
  simpl; introv aeq; auto;
  try (complete (provefalse;
                 inversion aeq as [? ? ? ? ? ? ? ? ? a]; subst; allsimpl; cpx;
                 unfold lsubst in a; allsimpl; boolvar; inversion a)).

  - constructor; simpl; auto.
    introv i.
    destruct n; cpx.

  - inversion aeq as [? ? ? ? ? ? ? ? ? a]; subst; allsimpl; cpx.

  - applydup @alpha_eq_bterm_oterm in aeq; exrepnd; ginv.
    apply alpha_eq_oterm_combine; dands.

    + unfold mk_fresh_bterms; allrw map_length.
      inversion aeq as [? ? ? ? ? ? ? ? ? a]; subst; allsimpl; cpx.
      unfold lsubst in a; boolvar; allsimpl; inversion a; allrw map_length; auto.

    + introv i.
      unfold mk_fresh_bterms in i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      destruct a0 as [l1 t1].
      destruct a as [l2 t2].
      unfold mk_fresh_bterm.

      eapply move_alpha_eq_bterm_down in aeq;[|exact i1].

      apply alphaeq_bterm3_if
      with (lva := (maybe_new_var v1 l1 t1)
                     :: (maybe_new_var v2 l2 t2)
                     :: (remove_nvars [maybe_new_var v1 l1 t1] (free_vars t1))
                     ++ (remove_nvars [maybe_new_var v2 l2 t2] (free_vars t2))
           ) in aeq.
      inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst; allsimpl; cpx; clear aeq.
      apply alpha_eq_if3 in a.

      allrw length_app; allsimpl.
      allrw (plus_comm (length l1) 1).
      allrw (plus_comm (length l2) 1).
      allsimpl.

      pose proof (split_list_r _ lv 1) as h.
      autodimp h hyp; try omega; exrepnd; subst; allsimpl; cpx.
      allrw length_app; allsimpl.
      allrw (plus_comm (length l0) 1); allsimpl; cpx.

      allrw disjoint_app_l; allrw disjoint_singleton_l.
      allunfold @all_vars; allsimpl.
      allrw disjoint_app_r; repnd; allrw app_nil_r.
      allrw disjoint_cons_r; allrw disjoint_app_r.
      allrw in_app_iff; allsimpl; allrw in_app_iff.
      allrw not_over_or; repnd.
      allrw no_repeats_app; allrw disjoint_singleton_r; repnd.

      apply (al_bterm _ _ l0); allsimpl; auto.
      { unfold all_vars; simpl; allrw app_nil_r.
        allrw disjoint_app_r; allrw disjoint_cons_r; dands; auto. }

      pose proof (lsubst_lsubst_aux (mk_fresh (maybe_new_var v1 l1 t1) t1) (var_ren l1 l0)) as e.
      autodimp e hyp.
      { simpl; rw <- @sub_free_vars_is_flat_map_free_vars_range; rw app_nil_r.
        rw @sub_free_vars_var_ren; allrw length_app; try omega; eauto with slow.
        rw disjoint_cons_l; dands; eauto with slow. }
      rw e; clear e.

      pose proof (lsubst_lsubst_aux (mk_fresh (maybe_new_var v2 l2 t2) t2) (var_ren l2 l0)) as e.
      autodimp e hyp.
      { simpl; rw <- @sub_free_vars_is_flat_map_free_vars_range; allrw app_nil_r.
        rw @sub_free_vars_var_ren; allrw length_app; try omega; eauto with slow.
        rw disjoint_cons_l; dands; eauto with slow. }
      rw e; clear e.

      simpl; fold_terms.

      apply (implies_alpha_eq_mk_fresh_sub x).
      { unfold all_vars; allrw in_app_iff; allrw not_over_or.
        dands; intro k.
        - apply free_vars_lsubst_aux_subset in k.
          allrw in_app_iff.
          allrw in_remove_nvars; allsimpl; allrw not_over_or.
          allrw <- @dom_sub_sub_filter.
          rw @dom_sub_var_ren in k; auto.
          allrw in_remove_nvars.
          repndors; repnd; tcsp.
          apply in_sub_free_vars in k; exrepnd.
          apply in_sub_filter in k0; allsimpl; allrw not_over_or; repnd; GC.
          apply in_var_ren in k2; exrepnd; subst; allsimpl; repndors; subst; tcsp.
        - apply subset_bound_vars_lsubst_aux in k.
          rw in_app_iff in k; repndors; tcsp.
          apply subset_sub_bound_vars_sub_filter in k.
          rw @sub_bound_vars_var_ren in k; allsimpl; sp.
        - apply free_vars_lsubst_aux_subset in k.
          rw in_app_iff in k.
          allrw in_remove_nvars; allsimpl; allrw not_over_or.
          allrw <- @dom_sub_sub_filter.
          rw @dom_sub_var_ren in k; auto; try omega.
          allrw in_remove_nvars.
          repndors; repnd; tcsp.
          apply in_sub_free_vars in k; exrepnd.
          apply in_sub_filter in k0; allsimpl; allrw not_over_or; repnd; GC.
          apply in_var_ren in k2; exrepnd; subst; allsimpl; repndors; subst; tcsp.
        - apply subset_bound_vars_lsubst_aux in k.
          rw in_app_iff in k; repndors; tcsp.
          apply subset_sub_bound_vars_sub_filter in k.
          rw @sub_bound_vars_var_ren in k; allsimpl; sp.
      }

      pose proof (lsubst_lsubst_aux (lsubst_aux t1 (sub_filter (var_ren l1 l0) [maybe_new_var v1 l1 t1])) (var_ren [maybe_new_var v1 l1 t1] [x])) as e.
      autodimp e hyp.
      { simpl.
        apply disjoint_singleton_r; intro k.
        apply subset_bound_vars_lsubst_aux in k; rw in_app_iff in k.
        repndors; tcsp.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      rw e; clear e.

      pose proof (lsubst_lsubst_aux (lsubst_aux t2 (sub_filter (var_ren l2 l0) [maybe_new_var v2 l2 t2])) (var_ren [maybe_new_var v2 l2 t2] [x])) as e.
      autodimp e hyp.
      { simpl.
        apply disjoint_singleton_r; intro k.
        apply subset_bound_vars_lsubst_aux in k; rw in_app_iff in k.
        repndors; tcsp.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      rw e; clear e.

      pose proof (lsubst_aux_app
                    t1
                    (sub_filter (var_ren l1 l0) [maybe_new_var v1 l1 t1])
                    (var_ren [maybe_new_var v1 l1 t1] [x])) as h1.
      simpl in h1.
      repeat (autodimp h1 hyp).
      { apply disjoint_singleton_r.
        intro k.
        allrw <- @sub_bound_vars_is_flat_map_bound_vars_range.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      { apply disjoint_bv_sub_sub_filter.
        apply disjoint_bv_vars; auto. }
      { apply disjoint_bv_vars; auto.
        apply disjoint_singleton_l; auto. }
      rw h1; clear h1.

      pose proof (lsubst_aux_app
                    t2
                    (sub_filter (var_ren l2 l0) [maybe_new_var v2 l2 t2])
                    (var_ren [maybe_new_var v2 l2 t2] [x])) as h2.
      simpl in h2.
      repeat (autodimp h2 hyp).
      { apply disjoint_singleton_r.
        intro k.
        allrw <- @sub_bound_vars_is_flat_map_bound_vars_range.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      { apply disjoint_bv_sub_sub_filter.
        apply disjoint_bv_vars; auto. }
      { apply disjoint_bv_vars; auto.
        apply disjoint_singleton_l; auto. }
      rw h2; clear h2.

      pose proof (lsubst_sub_disjoint
                    (sub_filter (var_ren l1 l0) [maybe_new_var v1 l1 t1])
                    (@var_ren o [maybe_new_var v1 l1 t1] [x])) as h1.
      allsimpl.
      repeat (autodimp h1 hyp).
      { apply disjoint_singleton_r; intro k.
        apply subset_sub_free_vars_sub_filter in k.
        rw @sub_free_vars_var_ren in k; auto. }
      { apply disjoint_singleton_l; intro k.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      rw h1; clear h1.

      pose proof (lsubst_sub_disjoint
                    (sub_filter (var_ren l2 l0) [maybe_new_var v2 l2 t2])
                    (@var_ren o [maybe_new_var v2 l2 t2] [x])) as h2.
      allsimpl.
      repeat (autodimp h2 hyp).
      { apply disjoint_singleton_r; intro k.
        apply subset_sub_free_vars_sub_filter in k.
        rw @sub_free_vars_var_ren in k; auto; try omega. }
      { apply disjoint_singleton_l; intro k.
        apply subset_sub_bound_vars_sub_filter in k.
        rw @sub_bound_vars_var_ren in k; allsimpl; sp. }
      rw h2; clear h2.

      apply (alpha_eq_trans _ (lsubst_aux t1 (var_ren (l1 ++ [v1]) (l0 ++ [x])))).

      { apply alpha_eq_lsubst_aux_if_ext_eq; auto.
        - rw @var_ren_app; auto.
          unfold ext_alpha_eq_subs; simpl; introv i.
          allrw @sub_find_app; allrw @sub_find_sub_filter_eq; allrw memvar_singleton.
          boolvar; simpl; boolvar; simpl; tcsp.
          + apply maybe_new_var_in_implies in i; repnd.
            rw i.
            rw @sub_find_none_if; auto.
            rw @dom_sub_var_ren; auto.
          + apply maybe_new_var_in_implies in i; repnd; sp.
          + apply maybe_new_var_diff_implies in Heqb; repnd.
            remember (sub_find (var_ren l1 l0) v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
            apply sub_find_none2 in Heqsf.
            rw @dom_sub_var_ren in Heqsf; auto.
          + remember (sub_find (var_ren l1 l0) v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
        - rw @sub_free_vars_app.
          rw @sub_free_vars_var_ren; simpl; auto.
          rw disjoint_app_r; rw disjoint_singleton_r; dands; auto.
          eapply subvars_disjoint_r;[apply subvars_sub_free_vars_sub_filter|].
          rw @sub_free_vars_var_ren; eauto with slow.
        - rw @sub_free_vars_var_ren; allrw length_app; allsimpl; auto.
          rw disjoint_app_r; rw disjoint_singleton_r; dands; eauto with slow.
      }

      apply (alpha_eq_trans _ (lsubst_aux t2 (var_ren (l2 ++ [v2]) (l0 ++ [x])))); auto.

      { apply alpha_eq_lsubst_aux_if_ext_eq; auto.
        - rw @var_ren_app; auto; try omega.
          unfold ext_alpha_eq_subs; simpl; introv i.
          allrw @sub_find_app; allrw @sub_find_sub_filter_eq; allrw memvar_singleton.
          boolvar; simpl; boolvar; simpl; tcsp.
          + apply maybe_new_var_in_implies in i; repnd.
            rw i.
            rw @sub_find_none_if; simpl; auto.
            rw @dom_sub_var_ren; auto; try omega.
          + apply maybe_new_var_in_implies in i; repnd; sp.
          + apply maybe_new_var_diff_implies in Heqb; repnd.
            remember (sub_find (var_ren l2 l0) v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
            apply sub_find_none2 in Heqsf.
            rw @dom_sub_var_ren in Heqsf; auto; try omega.
          + remember (sub_find (var_ren l2 l0) v) as sf; symmetry in Heqsf; destruct sf; simpl; auto.
        - rw @sub_free_vars_var_ren; allrw length_app; allsimpl; try omega.
          rw disjoint_app_r; rw disjoint_singleton_r; dands; eauto with slow.
        - rw @sub_free_vars_app.
          rw @sub_free_vars_var_ren; simpl; auto.
          rw disjoint_app_r; rw disjoint_singleton_r; dands; auto.
          eapply subvars_disjoint_r;[apply subvars_sub_free_vars_sub_filter|].
          rw @sub_free_vars_var_ren; eauto with slow; try omega.
      }
Qed.

Lemma wf_atom_eq {p} :
  forall a b c d : @NTerm p,
    wf_term (mk_atom_eq a b c d) <=> (wf_term a # wf_term b # wf_term c # wf_term d).
Proof.
  introv; allrw <- @nt_wf_eq.
  split; intro k.

  - inversion k as [|?|? ? imp e]; subst; allsimpl.
    allunfold @num_bvars; allsimpl; GC.
    pose proof (imp (nobnd a)) as i1.
    pose proof (imp (nobnd b)) as i2.
    pose proof (imp (nobnd c)) as i3.
    pose proof (imp (nobnd d)) as i4.
    autodimp i1 hyp.
    autodimp i2 hyp.
    autodimp i3 hyp.
    autodimp i4 hyp.
    allrw @bt_wf_iff; sp.

  - repnd.
    constructor; allunfold @num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Lemma wf_int_eq {p} :
  forall a b c d : @NTerm p,
    wf_term (mk_int_eq a b c d) <=> (wf_term a # wf_term b # wf_term c # wf_term d).
Proof.
  introv; allrw <- @nt_wf_eq.
  split; intro k.

  - inversion k as [|?|? ? imp e]; subst; allsimpl.
    allunfold @num_bvars; allsimpl; GC.
    pose proof (imp (nobnd a)) as i1.
    pose proof (imp (nobnd b)) as i2.
    pose proof (imp (nobnd c)) as i3.
    pose proof (imp (nobnd d)) as i4.
    autodimp i1 hyp.
    autodimp i2 hyp.
    autodimp i3 hyp.
    autodimp i4 hyp.
    allrw @bt_wf_iff; sp.

  - repnd.
    constructor; allunfold @num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Lemma co_wf_true {o} :
  forall op (c : @CanonicalOp o) bs,
    co_wf op c bs = true -> co_wf_def op c bs.
Proof.
  introv w.
  unfold co_wf in w.
  unfold co_wf_def.
  gpdest c; destruct bs, op; ginv;
  try (complete (eexists; dands; eauto)).
Qed.

Lemma ca_wf_true {o} :
  forall (c : @CanonicalOp o) bs,
    ca_wf c bs = true -> ca_wf_def c bs.
Proof.
  introv w.
  unfold ca_wf in w.
  unfold ca_wf_def.
  destruct c, bs; ginv;
  try (complete (eexists; dands; eauto)).
Qed.

Lemma eapply_wf_true {o} :
  forall (t : @NTerm o),
    eapply_wf t = true -> eapply_wf_def t.
Proof.
  introv w.
  unfold eapply_wf in w.
  unfold eapply_wf_def.
  destruct t as [v|f|op bs]; allsimpl; tcsp; ginv.
  - left; eexists; eauto.
  - destruct op; allsimpl; tcsp; ginv;[].
    destruct c; allsimpl; tcsp; ginv;[|].
    { destruct bs as [|b bs]; allsimpl; tcsp.
      destruct b as [l t]; allsimpl.
      destruct l as [|v l]; allsimpl; tcsp.
      destruct l as [|? l]; allsimpl; tcsp.
      destruct bs as [|? bs]; allsimpl; tcsp; ginv.
      right; right; eexists; eexists; unfold mk_lam; dands; eauto. }
    { destruct bs; allsimpl; ginv; fold_terms.
      right; left; eexists; eauto. }
Qed.

Lemma co_wf_false_implies_not {o} :
  forall op (c : @CanonicalOp o) bs,
    co_wf op c bs = false -> !co_wf_def op c bs.
Proof.
  introv w.
  destruct (co_wf_dec op c bs) as [d|d]; auto.
  unfold co_wf_def in d; exrepnd; subst; repndors; exrepnd; subst;
  unfold co_wf in w; rw d1 in w; ginv.
Qed.

Lemma ca_wf_false_implies_not {o} :
  forall (c : @CanonicalOp o) bs,
    ca_wf c bs = false -> !ca_wf_def c bs.
Proof.
  introv w.
  destruct (ca_wf_dec c bs) as [d|d]; auto.
  unfold ca_wf_def in d; exrepnd; subst; repndors; exrepnd; subst.
  unfold ca_wf in w; ginv.
Qed.

Lemma eapply_wf_false_implies_not {o} :
  forall (t : @NTerm o),
    eapply_wf t = false -> !eapply_wf_def t.
Proof.
  introv w.
  destruct (eapply_wf_dec t) as [d|d]; auto.
  unfold eapply_wf_def in d; exrepnd; subst; repndors; exrepnd; subst;
  unfold eapply_wf in w; ginv.
Qed.

Lemma co_wf_def_implies_true {o} :
  forall op (c : @CanonicalOp o) bs,
    co_wf_def op c bs -> co_wf op c bs = true.
Proof.
  introv w.
  unfold co_wf_def in w.
  exrepnd; repndors; exrepnd; subst; unfold co_wf; rw w1; auto.
Qed.

Lemma ca_wf_def_implies_true {o} :
  forall (c : @CanonicalOp o) bs,
    ca_wf_def c bs -> ca_wf c bs = true.
Proof.
  introv w.
  unfold ca_wf_def in w; exrepnd; subst; simpl; auto.
Qed.

Lemma eapply_wf_def_implies_true {o} :
  forall (t : @NTerm o),
    eapply_wf_def t -> eapply_wf t = true.
Proof.
  introv w.
  unfold eapply_wf_def in w.
  exrepnd; repndors; exrepnd; subst; unfold eapply_wf; tcsp.
Qed.

Lemma co_wf_def_len_implies {o} :
  forall op (c : @CanonicalOp o) bs1 bs2,
    length bs1 = length bs2
    -> co_wf_def op c bs1
    -> co_wf_def op c bs2.
Proof.
  introv len w.
  allunfold @co_wf_def.
  exrepnd; repndors; exrepnd; subst; allsimpl; cpx; rw w1;
  eexists; dands; eauto.
Qed.

Lemma ca_wf_def_len_implies {o} :
  forall (c : @CanonicalOp o) bs1 bs2,
    length bs1 = length bs2
    -> ca_wf_def c bs1
    -> ca_wf_def c bs2.
Proof.
  introv len w.
  allunfold @ca_wf_def.
  exrepnd; repndors; exrepnd; subst; allsimpl; cpx;
  eexists; dands; eauto.
Qed.

Lemma eapply_wf_def_len_implies {o} :
  forall (c : @CanonicalOp o) bs1 bs2,
    map num_bvars bs1 = map num_bvars bs2
    -> eapply_wf_def (oterm (Can c) bs1)
    -> eapply_wf_def (oterm (Can c) bs2).
Proof.
  introv len w.
  allunfold @eapply_wf_def.
  exrepnd; repndors; exrepnd; subst; allsimpl; cpx; ginv;[|].
  { allunfold @mk_nseq; ginv; allsimpl.
    destruct bs2; allsimpl; ginv; fold_terms.
    right; left; exists f; auto. }
  { allunfold @mk_lam; ginv.
    allsimpl; cpx.
    destruct bs2 as [|b1 bs2]; allsimpl; ginv;[].
    destruct bs2 as [|? bs2]; allsimpl; ginv.
    destruct b1 as [l t]; allsimpl; ginv.
    destruct l as [|x l]; allsimpl; ginv.
    destruct l as [|? l]; allsimpl; ginv.
    allunfold @num_bvars; allsimpl; GC.
    right; right; eexists; eexists; dands; eauto. }
Qed.
Hint Resolve eapply_wf_def_len_implies : slow.

(* !!MOVE *)
Hint Rewrite map_length : slow.

Lemma compute_step_seq_apply_success {o} :
  forall (t : @NTerm o) f bs u,
    compute_step_seq_apply t f bs = csuccess u
    -> {arg : NTerm
        & bs = [nobnd arg]
        # u = mk_eapply (mk_ntseq f) arg }.
Proof.
  introv comp.
  destruct bs; allsimpl; ginv.
  destruct b.
  destruct l; allsimpl; ginv.
  destruct bs; allsimpl; ginv.
  unfold nobnd.
  eexists; dands; eauto.
Qed.

Lemma compute_step_eapply1_success {o} :
  forall bs (t : @NTerm o) cstep arg1 ncr u,
    compute_step_eapply1 bs t cstep arg1 ncr = csuccess u
    -> {arg2 : NTerm
        & {l : list BTerm
        & bs = nobnd arg2 :: l
        # ((iscan arg2 # compute_step_eapply2 t arg1 arg2 l = csuccess u)
           [+]
           (isexc arg2 # u = arg2)
           [+]
           {x : NTerm
            & cstep = csuccess x
            # isnoncan_like arg2
            # u = oterm (NCan ncr) (nobnd arg1 :: nobnd x :: l) } ) }}.
Proof.
  introv comp.
  destruct bs as [|b l]; allsimpl; ginv.
  destruct b as [vs arg2].
  destruct vs; ginv.
  exists arg2 l; dands; auto.
  destruct arg2 as [|f|op bs2]; ginv.
  - left; dands; simpl; auto.
  - dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.
    + right; right.
      destruct cstep; allsimpl; ginv.
      eexists; dands; eauto.
    + right; left; dands; auto.
    + right; right.
      destruct cstep; allsimpl; ginv.
      eexists; dands; eauto.
Qed.

Ltac dcwf_aux1 h :=
  match goal with
    | [ H : context[if co_wf ?op ?c ?bs then _ else _] |- _ ] => remember (co_wf op c bs) as h
    | [ H : context[if ca_wf ?c ?bs     then _ else _] |- _ ] => remember (ca_wf c bs) as h
    | [ H : context[if eapply_wf ?t     then _ else _] |- _ ] => remember (eapply_wf t) as h

    | [ |- context[if co_wf ?op ?c ?bs then _ else _] ] => remember (co_wf op c bs) as h
    | [ |- context[if ca_wf ?c ?bs     then _ else _] ] => remember (ca_wf c bs) as h
    | [ |- context[if eapply_wf ?t     then _ else _] ] => remember (eapply_wf t) as h
  end.

Ltac dcwf_aux2 :=
  match goal with
    | [ H : context[co _ _ _ _ _ _ _ _] |- _ ] => unfold co, co_aux in H
    | [ H : context[ca _ _ _ _ _ _ _ _] |- _ ] => unfold ca, ca_aux in H
    | [ H : context[compute_step_eapply _ _ _ _ _] |- _ ] => unfold compute_step_eapply, compute_step_eapply1 in H

    | [ |- context[co _ _ _ _ _ _ _ _] ] => unfold co, co_aux
    | [ |- context[ca _ _ _ _ _ _ _ _] ] => unfold ca, ca_aux
    | [ |- context[compute_step_eapply _ _ _ _ _] ] => unfold compute_step_eapply, compute_step_eapply1
  end.

Ltac dcwf_aux3 h :=
  match goal with
    | [ K : h = co_wf ?op ?c ?bs |- _ ] =>
      symmetry in K;
        destruct h;
        [apply co_wf_true in K
        |try (apply co_wf_false_implies_not in K; destruct K;
              first[complete auto
                   |eapply co_wf_def_len_implies;[|eauto];
                    try (autorewrite with slow);
                    complete auto])
        ]
    | [ K : h = ca_wf ?c ?bs |- _ ] =>
      symmetry in K;
        destruct h;
        [apply ca_wf_true in K
        |try (apply ca_wf_false_implies_not in K; destruct K;
              first[complete auto
                   |eapply ca_wf_def_len_implies;[|eauto];
                    try (autorewrite with slow);
                    complete auto])
        ]
    | [ K : h = eapply_wf ?t |- _ ] =>
      symmetry in K;
        destruct h;
        [apply eapply_wf_true in K
        |try (apply eapply_wf_false_implies_not in K; destruct K;
              first[complete auto
                   |eapply eapply_wf_def_len_implies;[|eauto];
                    try (autorewrite with slow);
                    complete auto])
        ]
  end.

Ltac dcwf h :=
  first [dcwf_aux1 h
        |dcwf_aux2; dcwf_aux1 h
        ];
  dcwf_aux3 h;
  try (complete ginv).

Lemma compute_step_eapply_success {o} :
  forall bs (t : @NTerm o) cstep arg1 ncr u,
    compute_step_eapply bs t cstep arg1 ncr = csuccess u
    -> {arg2 : NTerm
        & {l : list BTerm
        & bs = nobnd arg2 :: l
        # eapply_wf_def arg1
        # ((iscan arg2 # compute_step_eapply2 t arg1 arg2 l = csuccess u)
           [+]
           (isexc arg2 # u = arg2)
           [+]
           {x : NTerm
            & cstep = csuccess x
            # isnoncan_like arg2
            # u = oterm (NCan ncr) (nobnd arg1 :: nobnd x :: l) } ) }}.
Proof.
  introv comp.
  unfold compute_step_eapply in comp.
  dcwf h.
  apply compute_step_eapply1_success in comp; exrepnd; subst.
  eexists; eexists; dands; eauto.
Qed.

Lemma compute_step_eapply2_success {o} :
  forall (t : @NTerm o) arg1 arg2 bs u,
    compute_step_eapply2 t arg1 arg2 bs = csuccess u
    -> (bs = []
        # ({v : NVar
            & {b : NTerm
            & arg1 = mk_lam v b
            # u = apply_bterm (bterm [v] b) [arg2] }}
           [+]
           {f : nseq
            & {n : nat
            & arg1 = mk_nseq f
            # arg2 = mk_nat n
            # u = mk_nat (f n) }}
           [+]
           {f : ntseq
            & {n : nat
            & arg1 = mk_ntseq f
            # arg2 = mk_nat n
            # u = f n }})).
Proof.
  introv comp.
  destruct bs; allsimpl; ginv;[].
  dands; auto;[].
  destruct arg1 as [|f1|op1 bs1]; allsimpl; ginv;[|].
  - destruct arg2 as [|f2|op2 bs2]; allsimpl; ginv.
    destruct op2 as [can2|ncan2|exc2|abs2]; allsimpl; ginv;[].
    destruct can2; allsimpl; ginv.
    destruct bs2; allsimpl; ginv.
    boolvar; ginv.
    right; right.
    eexists; eexists; dands; eauto.
    unfold mk_nat.
    rw Znat.Z2Nat.id; auto.
  - destruct op1 as [can1|ncan1|exc1|abs1]; allsimpl; ginv;[].
    destruct can1; allsimpl; ginv;[|].
    { destruct bs1 as [|b bs1]; allsimpl; ginv;[].
      destruct b as [vs b].
      destruct vs as [|v vs]; ginv.
      destruct vs; ginv.
      destruct bs1; ginv.
      left; fold_terms.
      eexists; eexists; dands; eauto. }
    { destruct bs1 as [|b bs1]; allsimpl; ginv;[].
      destruct arg2 as [v|f|op bs]; allsimpl; ginv;[].
      dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv;[].
      destruct can; allsimpl; ginv;[].
      destruct bs; allsimpl; ginv.
      boolvar; ginv.
      right; left.
      fold_terms.
      exists n (Z.to_nat z); dands; auto.
      unfold mk_nat.
      rw Znat.Z2Nat.id; auto. }
Qed.

Definition get_cutokens_sub {o} (sub : @Sub o) :=
  oappl (map get_cutokens (range sub)).

Lemma oapp_oappl {T} :
  forall l (o : OList T),
    oeqset (oapp (oappl l) o) (OLL (l ++ [o])).
Proof.
  introv.
  eapply oeqset_trans;
    [apply oeqset_oapp_if;
      [apply oeqset_oappl_OLL|apply oeqset_refl]
    |].
  apply oapp_OLL_left.
Qed.

Lemma get_cutokens_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    oeqset (get_cutokens (lsubst_aux t sub))
           (oapp (get_cutokens t) (get_cutokens_sub (sub_keep_first sub (free_vars t)))).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    rw @sub_keep_singleton.
    unfold oatoml.
    eapply oeqset_trans;[|apply oeqset_sym;apply oapp_nil_l].
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
    + unfold get_cutokens_sub; simpl; allrw app_nil_r; auto.
      rw @oappl_get_cutokens_singleton; eauto 3 with slow.
    + unfold get_cutokens_sub; simpl; eauto 3 with slow.

  - Case "sterm".
    allrw @sub_keep_first_nil_r; simpl.
    unfold get_cutokens_sub; simpl; auto.
    eapply oeqset_trans;[|apply oeqset_oapp_sym].
    eapply oeqset_trans;[|apply oeqset_sym;apply oapp_nil_l].
    eauto 3 with slow.

  - Case "oterm".
    unfold oatoml.
    allrw map_map; unfold compose.
    eapply oeqset_trans;[apply oeqset_oappl_OLL|].
    eapply oeqset_trans;[|apply oeqset_sym;apply oapp_oappl].
    rw <- app_assoc.
    apply oeqset_app_if; eauto 3 with slow.
    apply implies_oeqset_OLL_OLL2; introv i j; allsimpl.

    + rw in_map_iff in i; exrepnd; subst.
      destruct a as [l t]; allsimpl.
      eapply ind in j;[|eauto].
      apply in_olist_oapp in j.
      apply in_olist_OLL_app.
      rw @in_olist_OLL_singleton.
      rw @in_olist_OLL_map.

      repndors;[left; eexists; eauto|].

      right.
      allunfold @get_cutokens_sub.
      allrw @oeqset_oappl_OLL.
      allrw @in_olist_OLL_map.
      exrepnd.
      eexists;dands;[|eauto].
      allrw @in_range_iff; exrepnd.
      allrw @in_sub_keep_first; repnd; dands; auto.
      allrw @sub_find_sub_filter_eq; boolvar; ginv; auto.
      exists v.
      rw @in_sub_keep_first; dands; auto.
      rw lin_flat_map.
      eexists; dands; eauto; allsimpl; allrw in_remove_nvars; sp.

    + allrw in_app_iff; allrw in_single_iff.
      apply in_olist_OLL_map.
      repndors.

      * allrw in_map_iff; exrepnd; subst.
        destruct a as [l t]; allsimpl.
        eexists; dands; eauto; simpl.
        eapply ind; eauto.
        apply in_olist_oapp; sp.

      * subst; allsimpl.
        allunfold @get_cutokens_sub.
        allrw @oeqset_oappl_OLL.
        allrw @in_olist_OLL_map; exrepnd.
        allrw @in_range_iff; exrepnd.
        allrw @in_sub_keep_first; repnd; dands; auto.
        allrw lin_flat_map; exrepnd.
        destruct x0 as [l t]; allsimpl.
        allrw in_remove_nvars; repnd.
        eexists;dands;eauto;simpl.
        eapply ind; eauto.
        apply in_olist_oapp.
        right.
        allrw @oeqset_oappl_OLL.
        apply in_olist_OLL_map.
        eexists; dands; eauto.
        apply in_range_iff.
        exists v.
        apply in_sub_keep_first; dands; auto.
        rw @sub_find_sub_filter_eq; boolvar; tcsp.
Qed.

Lemma get_cutokens_lsubst {o} :
  forall (t : @NTerm o) sub,
    oeqset (get_cutokens (lsubst t sub))
           (oapp (get_cutokens t) (get_cutokens_sub (sub_keep_first sub (free_vars t)))).
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  applydup @alphaeq_preserves_cutokens in h1; rw h3.
  apply alphaeq_preserves_free_vars in h1; rw h1.
  apply get_cutokens_lsubst_aux.
Qed.

Lemma get_cutokens_subst {o} :
  forall (t : @NTerm o) v u,
    oeqset (get_cutokens (subst t v u))
           (oapp (get_cutokens t)
                 (if memvar v (free_vars t) then get_cutokens u else onil)).
Proof.
  introv.
  unfold subst.
  pose proof (get_cutokens_lsubst t [(v,u)]) as h.
  eapply oeqset_trans;[exact h|].
  apply oeqset_oapp_if; eauto 3 with slow.
  simpl; boolvar; simpl; unfold get_cutokens_sub; simpl; eauto 3 with slow.
  rw @oappl_get_cutokens_singleton; eauto 3 with slow.
Qed.

Definition get_cutokens_sosub {o} (sub : @SOSub o) :=
  get_cutokens_bs (sorange sub).

Lemma get_cutokens_so_swap {o} :
  forall s (t : @SOTerm o),
    get_cutokens_so (so_swap s t) = get_cutokens_so t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; auto.

  - Case "soterm".
    f_equal; f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma get_cutokens_so_soalphaeq {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> get_cutokens_so t1 = get_cutokens_so t2.
Proof.
  soterm_ind1s t1 as [v ts ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "sovar".
    inversion aeq as [? ? ? len imp|]; subst; simpl; auto.
    f_equal.
    apply eq_maps3; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    apply ind in i0; auto.

  - Case "soterm".
    inversion aeq as [| ? ? ? len imp]; subst; clear aeq.
    simpl.
    f_equal; f_equal.
    apply eq_maps3; auto.
    introv i.
    applydup imp in i.
    applydup in_combine in i; repnd.
    destruct a as [l1 t1].
    destruct c as [l2 t2].
    simpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl.
    pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    repeat (autodimp h hyp).
    { rw @sosize_so_swap; auto. }
    pose proof (h (so_swap (mk_swapping l2 vs) t2)) as k; clear h.
    autodimp k hyp.
    allrw @get_cutokens_so_swap; auto.
Qed.

Lemma get_cutokens_sosub_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> get_cutokens_sosub sub1 = get_cutokens_sosub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp;
  inversion aeq as [|? ? ? ? ? ask asu]; subst.
  unfold get_cutokens_sosub, get_cutokens_bs, oatoml; simpl.
  f_equal.
  destruct sk1, sk2; simpl.

  pose proof (IHsub1 sub2 asu) as h; clear IHsub1.
  unfold get_cutokens_sosub, get_cutokens_bs, oatoml in h.
  inversion h as [q]; clear h; rw q; clear q.
  f_equal.

  unfold alphaeq_sk in ask; allsimpl.
  inversion ask as [? ? ? ? ? len1 len2 disj norep a]; subst.
  apply alphaeq_eq in a.
  apply alphaeq_preserves_cutokens in a.
  allrw @get_cutokens_cswap; auto.
Qed.

Lemma implies_osubset_oappl_left {T} :
  forall o (l : list (OList T)),
    (forall x, LIn x l -> osubset x o)
    -> osubset (oappl l) o.
Proof.
  introv h.
  eapply osubset_trans;[apply oeqset_implies_osubset;apply oeqset_oappl_OLL|].
  apply osubset_singleton_OLL_l; auto.
Qed.

Lemma osubset_oapp_left {T} :
  forall (o o1 o2 : OList T),
    osubset o1 o
    -> osubset o2 o
    -> osubset (oapp o1 o2) o.
Proof.
  introv h1 h2 i.
  apply in_olist_oapp in i.
  repndors.
  - apply h1 in i; auto.
  - apply h2 in i; auto.
Qed.

Lemma implies_osubseto_app_r {T} :
  forall o (l1 l2 : list (OList T)),
    osubset o (OLL l1)[+]osubset o (OLL l2) -> osubset o (OLL (l1 ++ l2)).
Proof.
  introv h i.
  apply in_olist_OLL_app.
  repndors;[left|right]; apply h; auto.
Qed.

Lemma implies_osubset_oappl_right {T} :
  forall l (o : OList T),
    {x : OList T & LIn x l # osubset o x}
    -> osubset o (oappl l).
Proof.
  unfold osubset; introv h i.
  apply oeqset_oappl_OLL.
  eapply implies_osubset_singleton_OLL_r; eauto.
Qed.

Lemma osubset_get_cutokens_sub_filter {o} :
  forall (sub : @Sub o) l,
    osubset (get_cutokens_sub (sub_filter sub l)) (get_cutokens_sub sub).
Proof.
  introv.
  allunfold @get_cutokens_sub.
  apply implies_osubset_oappl_left; introv i.
  apply implies_osubset_oappl_right.
  eexists;dands;[|eauto 3 with slow].
  allrw in_map_iff; exrepnd; subst.
  eexists;dands;[|eauto].
  allrw @in_range_iff; exrepnd.
  allrw @in_sub_filter; repnd.
  eexists; eauto.
Qed.
Hint Resolve osubset_get_cutokens_sub_filter : slow.

Lemma get_cutokens_lsubst_aux_subset {o} :
  forall (t : @NTerm o) sub,
    osubset
      (get_cutokens (lsubst_aux t sub))
      (oapp (get_cutokens t) (get_cutokens_sub sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as f.
    unfold oatoml; simpl.
    eapply osubset_trans;
      [|apply oeqset_implies_osubset; apply oeqset_sym; apply oapp_nil_l].
    symmetry in Heqf; destruct f; simpl; eauto 3 with slow.
    + apply sub_find_some in Heqf.
      apply implies_osubset_oappl_right.
      eexists; dands;[|eauto 3 with slow].
      rw in_map_iff.
      eexists; dands; auto.
      apply in_range_iff; eexists; eauto.
    + apply osubset_nil_l.

  - Case "sterm".
    apply implies_osubset_oapp; left; eauto 3 with slow.

  - Case "oterm".
    eapply osubset_trans;
      [|apply oeqset_implies_osubset;apply oeqset_sym;apply oapp_oappl].
    allrw map_map; unfold compose.
    apply implies_osubset_oappl_left.
    introv i; allrw in_app_iff; repndors.
    { apply implies_osubset_singleton_OLL_r.
      eexists;dands;[|eauto 3 with slow].
      allrw in_app_iff; sp. }
    allrw in_map_iff; exrepnd; subst.
    destruct a as [l t]; allsimpl.
    eapply osubset_trans;[eapply ind;eauto|].
    apply osubset_oapp_left.

    { apply implies_osubseto_app_r; left.
      apply implies_osubseto_app_r; right.
      apply implies_osubset_singleton_OLL_r.
      eexists;dands;[|eauto 3 with slow].
      rw in_map_iff; eexists; dands; eauto. }

    { apply implies_osubseto_app_r; right.
      eapply osubset_trans;
        [|apply oeqset_implies_osubset;apply oeqset_sym;apply oeqset_singleton_l];
        eauto 3 with slow. }
Qed.

Lemma osubset_oappl_app_r {T} :
  forall (o : OList T) l1 l2,
    osubset o (oappl l1)[+]osubset o (oappl l2) -> osubset o (oappl (l1 ++ l2)).
Proof.
  introv h; repndors; eapply osubset_trans;eauto;
  apply implies_osubset_oappl_left; introv i;
  apply implies_osubset_oappl_right; eexists; dands; eauto 3 with slow;
  rw in_app_iff; sp.
Qed.

Lemma osubset_oappl_app_l {T} :
  forall (o : OList T) l1 l2,
    osubset (oappl l1) o
    -> osubset (oappl l2) o
    -> osubset (oappl (l1 ++ l2)) o.
Proof.
  introv h1 h2.
  eapply osubset_trans;[apply oeqset_implies_osubset;apply oeqset_oappl_OLL|].
  eapply osubset_trans in h1;[|apply oeqset_implies_osubset;apply oeqset_sym;apply oeqset_oappl_OLL].
  eapply osubset_trans in h2;[|apply oeqset_implies_osubset;apply oeqset_sym;apply oeqset_oappl_OLL].
  introv i; apply in_olist_OLL_app in i; repndors;[apply h1|apply h2]; auto.
Qed.

Lemma in_olist_oappl_app {T} :
  forall x (l1 l2 : list (OList T)),
    in_olist x (oappl (l1 ++ l2)) <=> (in_olist x (oappl l1) [+] in_olist x (oappl l2)).
Proof.
  introv.
  rw @oappl_app_as_oapp.
  rw @in_olist_oapp; sp.
Qed.

Lemma in_olist_oappl {T} :
  forall x (l : list (OList T)),
    in_olist x (oappl l) <=> in_olist x (OLL l).
Proof.
  induction l; simpl; tcsp.
  rw @oeqset_oappl_cons.
  rw @in_olist_oapp; rw IHl.
  rw @in_olist_OLL_cons; sp.
Qed.

Lemma osubset_get_cutokens_sosub_filter {o} :
  forall (sub : @SOSub o) l,
    osubset (get_cutokens_sosub (sosub_filter sub l)) (get_cutokens_sosub sub).
Proof.
  unfold get_cutokens_sosub, get_cutokens_bs, oatoml; introv i.
  allrw @in_olist_OLL_map; exrepnd.
  eexists; dands; eauto.
  apply sorange_sosub_filter_subset in i1; auto.
Qed.

Lemma get_cutokens_sosub_aux_subset {o} :
  forall (t : @SOTerm o) sub,
    osubset
      (get_cutokens (sosub_aux sub t))
      (oapp (get_cutokens_so t) (get_cutokens_sosub sub)).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; allsimpl.

  - Case "sovar".
    remember (sosub_find sub (v,length ts)) as f.
    symmetry in Heqf; destruct f; simpl; auto.
    + destruct s.
      apply sosub_find_some in Heqf; repnd.
      eapply osubset_trans;
        [|apply oeqset_implies_osubset;apply oeqset_sym;apply oapp_oappl].
      introv i.
      apply get_cutokens_lsubst_aux_subset in i.
      apply in_olist_OLL_app.
      allrw @in_olist_oapp.
      allrw @in_olist_OLL_singleton.
      repndors.
      * right.
        unfold get_cutokens_sosub, get_cutokens_bs, oatoml.
        apply in_olist_OLL_map.
        exists (bterm l n); simpl; dands; auto.
        apply in_sorange.
        exists v; simpl; auto.
      * unfold get_cutokens_sub, get_cutokens_bs, oatoml in i.
        allrw @oeqset_oappl_OLL.
        apply in_olist_OLL_map in i; exrepnd.
        rw @range_combine in i1; allrw map_length; auto.
        rw in_map_iff in i1; exrepnd; subst.
        apply ind in i0; auto.
        allrw @in_olist_oapp; repndors; tcsp.
        left.
        apply in_olist_OLL_map.
        eexists; dands; eauto.
    + apply sosub_find_none in Heqf; repnd.
      rw @get_cutokens_apply_list; simpl.
      unfold oatoml.
      eapply osubset_trans;[apply oeqset_implies_osubset;apply oapp_nil_l|].
      allrw map_map; unfold compose.
      apply implies_osubset_oappl_left; introv i.
      rw in_map_iff in i; exrepnd; subst.
      eapply osubset_trans;[apply ind;auto|].
      apply osubset_oapp_if; eauto 3 with slow.
      apply implies_osubset_oappl_right.
      eexists;dands;[|eauto 3 with slow].
      rw in_map_iff; eexists; eauto.

  - Case "soterm".
    allrw map_map; unfold compose.
    unfold oapp.
    rw @oappl_cons_oappl.
    rw <- app_assoc.
    apply osubset_oappl_app_l.
    + apply osubset_oappl_app_r; left; eauto 3 with slow.
    + apply osubset_oappl_app_r; right.
      apply implies_osubset_oappl_left; introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a as [l t]; allsimpl.
      introv j.
      eapply ind in j; eauto.
      apply in_olist_oappl_app.
      apply in_olist_oapp in j.
      allrw @in_olist_oappl.
      allrw @in_olist_OLL_singleton.
      repndors.
      * left.
        apply in_olist_OLL_map.
        eexists; dands; eauto.
      * right.
        apply osubset_get_cutokens_sosub_filter in j; auto.
Qed.

Lemma get_cutokens_sosub_subset {o} :
  forall (t : @SOTerm o) sub,
    osubset
      (get_cutokens (sosub sub t))
      (oapp (get_cutokens_so t) (get_cutokens_sosub sub)).
Proof.
  introv.
  pose proof (unfold_sosub sub t) as h; exrepnd.
  rw h1.
  apply get_cutokens_so_soalphaeq in h2; rw h2.
  rw (get_cutokens_sosub_alphaeq_sosub sub sub'); eauto with slow.
  apply get_cutokens_sosub_aux_subset.
Qed.

Lemma get_cutokens_mk_instance {o} :
  forall vars bs (rhs : @SOTerm o),
    matching_bterms vars bs
    -> osubset
         (get_cutokens (mk_instance vars bs rhs))
         (oapp (get_cutokens_so rhs) (get_cutokens_bs bs)).
Proof.
  introv m i.
  unfold mk_instance in i.
  apply get_cutokens_sosub_subset in i; allrw in_app_iff; repndors; tcsp.
  unfold get_cutokens_sosub in i.
  rw @sorange_mk_abs_subst in i; auto.
Qed.

Lemma nt_wf_mk_uni {o} : forall n, @nt_wf o (mk_uni n).
Proof.
  introv.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve nt_wf_mk_uni : slow.

Lemma osubset_OLL_nil {T} :
  forall (o : OList T), osubset (OLL []) o.
Proof.
  introv; apply osubset_nil_l.
Qed.
Hint Resolve osubset_OLL_nil : slow.

Lemma nt_wf_NCompOp {o} :
  forall c (bs : list (@BTerm o)),
    nt_wf (oterm (NCan (NCompOp c)) bs)
    <=> {t1 : NTerm
         & {t2 : NTerm
         & {t3 : NTerm
         & {t4 : NTerm
         & bs = [nobnd t1, nobnd t2, nobnd t3, nobnd t4]
         # nt_wf t1
         # nt_wf t2
         # nt_wf t3
         # nt_wf t4 }}}}.
Proof.
  introv; split; introv h.
  - inversion h as [|?|? ? imp e]; subst; allsimpl; clear h.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1]; allsimpl.
    destruct b0 as [l2 t2]; allsimpl.
    destruct b1 as [l3 t3]; allsimpl.
    destruct b2 as [l4 t4]; allsimpl.
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    destruct l3; allsimpl; ginv.
    destruct l4; allsimpl; ginv.
    allunfold @num_bvars; allsimpl; GC.
    pose proof (imp (bterm [] t1)) as h1.
    pose proof (imp (bterm [] t2)) as h2.
    pose proof (imp (bterm [] t3)) as h3.
    pose proof (imp (bterm [] t4)) as h4.
    clear imp.
    autodimp h1 hyp.
    autodimp h2 hyp.
    autodimp h3 hyp.
    autodimp h4 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; eexists; eexists; dands; eauto.
  - exrepnd; subst.
    constructor; unfold num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Lemma nt_wf_NArithOp {o} :
  forall c (bs : list (@BTerm o)),
    nt_wf (oterm (NCan (NArithOp c)) bs)
    <=> {t1 : NTerm
         & {t2 : NTerm
         & bs = [nobnd t1, nobnd t2]
         # nt_wf t1
         # nt_wf t2 }}.
Proof.
  introv; split; introv h.
  - inversion h as [|?|? ? imp e]; subst; allsimpl; clear h.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1]; allsimpl.
    destruct b0 as [l2 t2]; allsimpl.
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    allunfold @num_bvars; allsimpl; GC.
    pose proof (imp (bterm [] t1)) as h1.
    pose proof (imp (bterm [] t2)) as h2.
    clear imp.
    autodimp h1 hyp.
    autodimp h2 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; dands; eauto.
  - exrepnd; subst.
    constructor; unfold num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Definition oshallow_sub {o} (sub : @Sub o) :=
  forall t, LIn t (range sub) -> osize t = O1.

Lemma simple_osize_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    oshallow_sub sub
    -> osize (lsubst_aux t sub) = osize t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv ss; allsimpl; tcsp.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_some in Heqsf.
    apply in_sub_eta in Heqsf; repnd.
    apply ss in Heqsf; auto.

  - Case "oterm".
    f_equal; f_equal; allrw map_map; unfold compose.
    apply eq_maps; introv i; destruct x as [l t]; simpl.
    rw (ind t l); auto.
    intros x j.
    apply (ss x).
    apply range_sub_filter_subset in j; auto.
Qed.

Lemma simple_osize_subst_aux {o} :
  forall (t : @NTerm o) v u,
    osize u = O1
    -> osize (subst_aux t v u) = osize t.
Proof.
  introv e.
  unfold subst_aux; apply simple_osize_lsubst_aux.
  unfold oshallow_sub; simpl; introv k; sp; subst; auto.
Qed.

Lemma simple_osize_subst {o} :
  forall (t : @NTerm o) v u,
    osize u = O1
    -> osize (subst t v u) = osize t.
Proof.
  introv e.
  pose proof (unfold_lsubst [(v,u)] t) as h; exrepnd.
  unfold subst; rw h0.
  rw @simple_osize_lsubst_aux.
  - apply alpha_eq_preserves_osize in h1; auto.
  - unfold oshallow_sub; simpl; introv k; sp; subst; auto.
Qed.

(*
Lemma get_cutokens_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) sub,
    osubset (get_cutokens (subst_utokens_aux t sub))
            (oapp (odiff (get_patom_deq o) (utok_sub_dom sub) (get_cutokens t))
                  (get_cutokens_utok_ren sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; auto.

  - Case "vterm".
    allsimpl; apply osubset_nil_l.

  - Case "sterm".
    simpl; auto.
    unfold oatoms.
    apply osubset_singleton_OLS_l; introv.
    SearchAbout osubset OLS.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf.

      * apply utok_sub_find_some in Heqsf.
        apply in_utok_sub_eta in Heqsf; repnd.
        introv j.
        rw in_app_iff; right.
        rw lin_flat_map.
        exists n; dands; auto.

      * apply utok_sub_find_none in Heqsf.
        simpl; rw subset_cons_l; dands.

        { rw in_app_iff; left.
          rw in_diff; simpl; sp.
        }

        { apply subset_flat_map; introv j.
          rw in_map_iff in j; exrepnd; subst.
          destruct a as [l t]; allsimpl.
          pose proof (ind t l j1) as h.
          introv i; apply h in i.
          allrw in_app_iff; allrw in_diff; repndors; exrepnd; tcsp.
          allsimpl.
          left; dands; tcsp.
          destruct (get_patom_deq o g x); tcsp.
          right.
          rw lin_flat_map; eexists; dands; eauto.
        }

    + rw diff_app_r.
      allapply @get_utok_none; allrw; simpl.
      allrw diff_nil; simpl.
      allrw flat_map_map; unfold compose.
      apply subset_flat_map; introv i.
      destruct x as [l t]; allsimpl.
      introv j.
      eapply ind in j; eauto.
      allrw in_app_iff; repndors; tcsp.
      left.
      rw diff_flat_map_r.
      rw lin_flat_map; eexists; dands; eauto.
Qed.
 *)

(*
Lemma get_cutokens_subst_utokens_subset {o} :
  forall (t : @NTerm o) sub,
    osubset (get_cutokens (subst_utokens t sub))
            (oapp (odiff (get_patom_deq o) (utok_sub_dom sub) (get_cutokens t))
                  (get_cutokens_utok_ren sub)).
Proof.
  introv i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0 in i.
  apply alphaeq_preserves_cutokens in h1; rw h1; clear h1.
  apply get_cutokens_subst_utokens_aux_subset; auto.
Qed.
*)

Lemma osubset_oeqset {T} :
  forall (o1 o2 o3 : OList T),
    osubset o1 o2 -> oeqset o2 o3 -> osubset o1 o3.
Proof.
  introv h1 h2 i.
  apply h1 in i; apply h2 in i; auto.
Qed.

Lemma implies_osubset_oapp_left {T} :
  forall (o o1 o2 : OList T),
    osubset o o1 -> osubset o (oapp o1 o2).
Proof.
  introv h.
  apply implies_osubset_oapp; tcsp.
Qed.
Hint Resolve implies_osubset_oapp_left : slow.

Lemma implies_osubset_oapp_right {T} :
  forall (o o1 o2 : OList T),
    osubset o o2 -> osubset o (oapp o1 o2).
Proof.
  introv h.
  apply implies_osubset_oapp; tcsp.
Qed.
Hint Resolve implies_osubset_oapp_right : slow.

Lemma osubset_oappl_nil_left {T} :
  forall (o : OList T), osubset (oappl []) o.
Proof.
  introv i.
  rw @oappl_nil in i.
  inversion i; subst; exrepnd; allsimpl; tcsp.
Qed.
Hint Resolve osubset_oappl_nil_left : slow.

(* end hide *)

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
