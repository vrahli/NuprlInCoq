(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

 *)


Require Export Omega.
Require Export Bool.
Require Export Eqdep_dec.
Require Export Arith.


(*

  This file presents some results that we have proved in Nuprl,
  namely:

  (1) Following Escardo and Xu's proof, we show that the non-squashed
  continuity principle if false in Coq.

  See lemma [continuity_false].

  (2) We then show that the squashed continuity principle is also
  false in Coq, when assuming AC20.  Note that AC20 is false in Nuprl,
  while the squashed continuity principle is true.

  See lemma [sq_continuity_prop_false].

  (3) Equivalently, the squashed continuity principle implies the
  negation of AC20.

  See lemma [sq_continuity_prop_implies_not_ac20].

  (4) Finally, we show that the squashed continuity principle implies
  the negation of the monotone bar induction principle.

  See lemma [untruncated_monotone_bar_induction_false].

*)


(* ============================================= *)
(* First some notations and tactics *)

Notation "! x" := (notT x)%type (at level 75, right associativity).

Ltac exrepnd :=
   repeat match goal with
           | [ H : _ /\ _ |- _ ] => let name := fresh H in destruct H as [name H]
           | [ H : prod _ _ |- _ ] => let name := fresh H in destruct H as [name H]
           | [ H : exists (v : _),_  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
           | [ H : { v : _ | _ }  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
           | [ H : { v : _ & _ }  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
         end.

Tactic Notation "complete" tactic(tac) := tac; fail.

Ltac autodimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete auto)
        | try (let concl := fresh "hyp" in
                 pose proof (H hyp) as concl;
               clear hyp;
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.

Ltac clear_eq x y :=
  match goal with
    | [ H : x = y |- _ ] => clear H
  end.

Tactic Notation "applydup" constr(l) "in" ident(H) :=
  let newH := fresh H in
    remember H as newH; clear_eq newH H; apply l in newH.

Ltac introv_arg H :=
  hnf;
  match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

Ltac introv_noarg :=
  hnf;
  repeat match goal with
         | |- ?P -> ?Q => idtac
         | |- forall _, _ => intro
         end.

Tactic Notation "introv" := introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) := introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) := introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) simple_intropattern(I3) := introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) := introv I1; introv I2 I3 I4.

(* ============================================= *)


Definition baire := nat -> nat.

Definition eq_upto (n : nat) (f g : baire) :=
  forall m, m < n -> f m = g m.

Definition zeros : baire := fun n => 0.

Definition zero_until (n k : nat) : baire :=
  fun x => if lt_dec x n then 0 else k.

Lemma eq_upto_sym :
  forall (n : nat) a b, eq_upto n a b -> eq_upto n b a.
Proof.
  introv h q.
  pose proof (h m q) as e; auto.
Qed.

Lemma eq_upto_zero_until :
  forall m n k : nat, m <= n -> eq_upto m (zero_until n k) zeros.
Proof.
  introv h q.
  unfold zero_until, zeros.
  destruct (lt_dec m0 n); try omega.
Qed.

Lemma zero_until_prop2 :
  forall n k : nat, (zero_until n k) n = k.
Proof.
  introv.
  unfold zero_until.
  destruct (lt_dec n n); try omega.
Qed.

Definition nat_n (n : nat) := {m : nat | m <? n = true}.

Lemma ltb2lt : forall {n m : nat}, (n <? m) = true -> n < m.
Proof.
  apply Nat.ltb_lt.
Qed.

Lemma lt2ltb : forall {n m : nat}, n < m -> (n <? m) = true.
Proof.
  apply Nat.ltb_lt.
Qed.

Definition baire_n (n : nat) := nat_n n -> nat.

Definition emseq : baire_n 0 :=
  fun (m : nat_n 0) =>
    match m with
    | exist _ z p => match Nat.nlt_0_r z (ltb2lt p) with end
    end.

Definition seqp := forall n : nat, baire_n n -> Type.

Definition baire2baire_n (s : baire) (n : nat) : baire_n n :=
  fun (m : nat_n n) => s (proj1_sig m).

Definition S0 := nat.
Definition S1 := baire.
Definition S2 := baire -> nat.

(* non-squashed/non-truncated continuity principle *)
Definition nsq_continuity :=
  forall (F : S2) (f : S1),
    {n : S0 & forall g : S1, eq_upto n f g -> F f = F g}.

(* [usq_continuity_zeros] is [usq_continuity] for [f=zeros] *)
Definition nsq_continuity_zeros :=
  forall (F : S2), {n : S0 & forall g : S1, eq_upto n zeros g -> F zeros = F g}.

(*

  Escardo and Xu's proof that the non-squashed continuity principle if
  false in Martin-Lof-like type theories (see
  http://www.cs.bham.ac.uk/~mhe/papers/escardo-xu-inconsistency-continuity.pdf).

 *)

Lemma continuity_zeros_false : !nsq_continuity_zeros.
Proof.
  introv h.

  remember (fun F => projT1 (h F)) as M.

  remember (M (fun a => 0)) as m.

  remember (fun b => M (fun a => b (a m))) as f.

  assert (f zeros = m) as h1.
  { subst; auto. }

  assert (forall (b : baire), eq_upto (M f) zeros b -> m = f b) as h2.
  { introv.
    rewrite HeqM.
    remember (h f) as zz; exrepnd; simpl.
    pose proof (zz0 b) as xx.
    rewrite h1 in xx; auto. }

  assert (forall (b a : baire), eq_upto (f b) zeros a -> b 0 = b (a m)) as h3.
  { introv.
    rewrite Heqf.
    rewrite HeqM.
    remember (h (fun a => b (a m))) as zz; exrepnd; simpl.
    pose proof (zz0 a) as xx.
    unfold zeros in *; simpl in xx; auto. }

  remember (zero_until (M f + 1) 1) as b.

  assert (f b = m) as e.
  { symmetry; apply h2.
    subst b.
    apply eq_upto_sym.
    apply eq_upto_zero_until; omega. }

  pose proof (h3 b) as h4.
  rewrite e in h4.

  pose proof (h4 (zero_until m (M f + 1))) as h5.
  autodimp h5 hyp.
  { apply eq_upto_sym.
    apply eq_upto_zero_until; omega. }

  rewrite zero_until_prop2 in h5.
  rewrite Heqb in h5.
  rewrite zero_until_prop2 in h5.
  unfold zero_until in h5.
  destruct (lt_dec 0 (M f + 1)) in *; try omega.
Qed.

Lemma continuity_false : !nsq_continuity.
Proof.
  introv h.
  apply continuity_zeros_false; introv.
  apply h.
Qed.

(*

  It also works using an existential proposition when assuming AC20.
  See lemma [sq_continuity_prop_false] below.
  That's because we can prove that [!nsq_continuity_zeros]
  implies [!sq_continuity_prop_zeros], assuming [AC20].
  See lemma [not_usq_continuity_zeros_implies_not_sq_continuity_prop_zeros].

  AC20 is false in Nuprl.

 *)

Definition AC20 :=
  forall (R : S2 -> S0 -> Prop),
    (forall a : S2, exists (b : S0), R a b)
    -> (exists (f : S2 -> S0), forall a : S2, R a (f a)).

Inductive Cast (t : Type) : Prop :=
| cast : t -> Cast t.
Hint Constructors Cast.

(*

  squashed/truncated continuity principle.
  To truncate here we use the [Cast] operator.
  Equivalently we can use the propositional existential.

*)
Definition sq_continuity :=
  forall (F : S2) (f : S1), Cast {n : nat & forall g : S1, eq_upto n f g -> F f = F g}.

Definition sq_continuity_zeros :=
  forall (F : S2), Cast {n : nat & forall g : S1, eq_upto n zeros g -> F zeros = F g}.

Definition sq_continuity_prop_sch (F : S2) :=
  forall (f : S1), exists n, forall g : S1, eq_upto n f g -> F f = F g.

Definition sq_continuity_prop := forall (F : S2), sq_continuity_prop_sch F.

Definition sq_continuity_prop_zeros :=
  forall (F : S2), exists n, forall g : S1, eq_upto n zeros g -> F zeros = F g.

(*

  This show that we can interchangeably use of the Propositional existential or Cast.

 *)
Lemma sq_continuity_iff_prop :
  sq_continuity <-> sq_continuity_prop.
Proof.
  introv; split; intro h; repeat introv.

  { pose proof (h F f) as q; clear h.
    inversion q as [h]; clear q; exrepnd.
    exists n; auto. }

  { pose proof (h F f) as q; clear h; exrepnd.
    constructor; exists n; auto. }
Qed.

(*

  We can trivially show that AC20 (false in Nuprl) and the negation of
  the non-squashed continuity principle (this negation is true in
  Martin-Lof-like type theories) for the sequence of zeros imply the
  negation the squashed continuity principle (this negation is false
  in Nuprl because the squashed continuity principle is true in Nuprl)
  for the sequence of zeros.

 *)
Lemma not_nsq_continuity_zeros_implies_not_sq_continuity_prop_zeros :
  AC20 -> !nsq_continuity_zeros -> !sq_continuity_prop_zeros.
Proof.
  introv ac nucont scont.
  unfold sq_continuity_prop_zeros in scont.
  unfold nsq_continuity_zeros in nucont.

  apply ac in scont; exrepnd.
  destruct nucont; introv.
  pose proof (scont0 F) as q; clear scont0.
  exists (f F); auto.
Qed.

Definition choice_principle (T : Type) :=
  forall (P : T -> Type),
    (forall t, Cast (P t)) <-> Cast (forall t, P t).

(* AC10 is true in Nuprl *)
Definition AC10 :=
  forall (R : S1 -> S0 -> Prop),
    (forall (a : S1), exists (b : S0), R a b)
    -> (exists (f : S1 -> S0), forall a : S1, R a (f a)).

(*

  This shows that the negation of the non-squashed continuity
  principle (this negation is true in Martin-Lof-like type theories)
  and the squashed continuity principle (true in Nuprl) imply the
  negation of the choice principle for [S2].  We also assume AC1,
  which is true in Nuprl.

 *)
Lemma not_nsq_continuity_and_sq_continuity_prop_implies_not_choice_principle :
  AC10 -> !nsq_continuity -> sq_continuity_prop -> !(choice_principle S2).
Proof.
  introv ac10 nnsqcont sqcont cp.
  pose proof (cp (fun (F : S2) => {M : S2 & forall (f g : S1), eq_upto (M f) f g -> F f = F g} )) as h; simpl in h.
  clear cp.
  destruct h as [h1 h2].
  clear h2.
  autodimp h1 hyp.

  { introv.
    pose proof (sqcont t) as h; clear sqcont.
    apply ac10 in h; exrepnd.
    constructor.
    exists f; auto. }

  inversion h1 as [q]; clear h1.
  destruct nnsqcont.
  unfold nsq_continuity.
  introv.
  pose proof (q F) as h; clear q; exrepnd.
  exists (M f); auto.
Qed.

Definition AC20_cast :=
  forall (R : S2 -> S0 -> Type),
    (forall a : S2, Cast {b : S0 & R a b})
    -> Cast {f : S2 -> S0 & forall a : S2, R a (f a)}.

(*

  From
  [not_nsq_continuity_and_sq_continuity_prop_implies_not_choice_principle]
  we deduce that the negation of the non-squashed continuity principle
  (this negation is true in Martin-Lof-like type theories) and the
  squashed continuity principle (true in Nuprl) imply the negation of
  AC20_cast.  We also assume AC1, which is true in Nuprl.

 *)
Lemma not_nsq_continuity_and_sq_continuity_prop_implies_not_ac20 :
  AC10 -> !nsq_continuity -> sq_continuity_prop -> !AC20_cast.
Proof.
  introv ac10 nnsqcont sqcont ac20.
  apply not_nsq_continuity_and_sq_continuity_prop_implies_not_choice_principle; auto.
  introv; split; intro h;[|destruct h as [h]; introv; constructor; auto];[].

  unfold AC20 in ac20.
  pose proof (ac20 (fun F n => P F)) as q; simpl in q.
  autodimp q hyp.
  { introv; pose proof (h a) as q; destruct q; constructor; eexists 0; auto. }
  clear h.
  destruct q as [h]; exrepnd.
  constructor; auto.
Qed.

Lemma sq_continuity_prop_zeros_false :
  AC20
  -> !sq_continuity_prop_zeros.
Proof.
  introv ac.
  apply not_nsq_continuity_zeros_implies_not_sq_continuity_prop_zeros; auto.
  apply continuity_zeros_false.
Qed.

Lemma sq_continuity_prop_false :
  AC20
  -> !sq_continuity_prop.
Proof.
  introv ac cont.
  apply sq_continuity_prop_zeros_false; auto.
  introv; apply cont.
Qed.

Lemma sq_continuity_prop_implies_not_ac20 :
  sq_continuity_prop -> !AC20.
Proof.
  introv cont ac.
  apply sq_continuity_prop_zeros_false; auto.
  introv; apply cont.
Qed.


(*

  Let's now look at bar induction now.  First we introduce some
  auxiliary definitions.  Then we define [monotone_bar_induction].

  Then we prove that the squashed continuity principle [sq_continuity]
  and [monotone_bar_induction] imply the non-squashed continuity
  principle [nsq_continuity] in
  [monotone_bar_induction_implies_continuity].

  Finally that means that we can prove the negation of
  [monotone_bar_induction] from [sq_continuity].  See lemma
  [untruncated_monotone_bar_induction_false].

 *)

Definition ext (n : nat) (s : baire_n n) (m : nat) : baire_n (S n) :=
  fun (k : nat_n (S n)) =>
    match k with
    | exist _ z q =>
      match le_lt_eq_dec z n (lt_n_Sm_le z n (ltb2lt q)) with
      | left p => s (exist (fun m => m <? n = true) z (lt2ltb p))
      | right _ => m
      end
    end.

Definition bar (B : seqp) := forall s : baire, Cast {n : nat & B n (baire2baire_n s n)}.

Definition base (B P : seqp) := forall n (s : baire_n n), B n s -> P n s.

Definition inductive (P : seqp) := forall n (s : baire_n n), (forall m, P (S n) (ext n s m)) -> P n s.

Definition monotone (B : seqp) := forall n m (s : baire_n n), B n s -> B (S n) (ext n s m).

Definition monotone_bar_induction :=
  forall (B P : seqp),
    bar B
    -> base B P
    -> inductive P
    -> monotone B
    -> P 0 emseq.

Definition updf (n : nat) (s : baire_n n) (f : baire) : baire :=
  fun (k : nat) =>
    match le_lt_dec n k with
    | left p => f k
    | right p => s (exist (fun m => m <? n = true) k (lt2ltb p))
    end.

Lemma updf_if_lt :
  forall {n m : nat} (p : m < n) (s : baire_n n) (f : baire),
    updf n s f m = s (exist (fun m => m <? n = true) m (lt2ltb p)).
Proof.
  introv; unfold updf.
  destruct (le_lt_dec n m) as [d|d]; try omega; auto.
  f_equal; f_equal.
  apply UIP_dec; apply bool_dec.
Qed.

Lemma eq_upto_updf :
  forall (n : nat) (s f : baire),
    eq_upto n s (updf n (baire2baire_n s n) f).
Proof.
  introv ltmn.
  rewrite (updf_if_lt ltmn); auto.
Qed.

Definition BB (F : S2) (f : S1) : seqp :=
  fun (n : nat) (s : baire_n n) =>
    forall (g : baire),
      (baire2baire_n (updf n s f) n = baire2baire_n g n)
      -> F (updf n s f) = F g.

Definition PP (F : S2) (f : S1) : seqp :=
  fun (n : nat) (s : baire_n n) =>
    {m : nat
     & {p : n <= m
     & forall (g : baire),
            (baire2baire_n (updf n s f) m = baire2baire_n g m)
            -> F (updf n s f) = F g }}.

Require Export FunctionalExtensionality.

Lemma updf_ext :
  forall n (s : baire_n n) f,
    updf (S n) (ext n s (f n)) f = updf n s f.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold updf.
  unfold ext.
  destruct (le_lt_dec (S n) x) as [d|d];
    destruct (le_lt_dec n x) as [p|p];
    try (destruct (le_lt_eq_dec x n (lt_n_Sm_le x n (ltb2lt (lt2ltb d)))) as [z|z]);
    try omega; subst; auto.
  f_equal; f_equal.
  apply UIP_dec; apply bool_dec.
Qed.

Lemma monotone_bar_induction_implies_continuity :
   sq_continuity -> monotone_bar_induction -> nsq_continuity.
Proof.
  introv scont bi; introv.

  pose proof (bi (BB F f) (PP F f)) as h; clear bi.

  repeat (autodimp h hyp).

  { (* bar *)
    introv.
    unfold BB.
    pose proof (scont F s) as q.
    inversion q as [h]; clear q; exrepnd.
    constructor.
    exists n.
    introv q.
    pose proof (h0 g) as z.
    autodimp z hyp.

    { introv ltmn.
      pose proof (equal_f q (exist (fun m => m <? n = true) m (lt2ltb ltmn))) as e.
      unfold baire2baire_n in e; simpl in e.
      rewrite (updf_if_lt ltmn) in e; simpl in e; auto. }

    rewrite <- z; clear z.
    symmetry.
    apply h0.
    apply eq_upto_updf.
  }

  { (* base *)
    introv bh.
    unfold PP.
    unfold BB in bh.
    exists n.
    exists (le_n n); auto.
  }

  { (* inductive *)
    introv h.
    pose proof (h (f n)) as q; clear h.
    unfold PP in *; exrepnd.
    exists m.
    exists (le_Sn_le n m p); introv z.
    pose proof (q1 g) as q; clear q1.
    rewrite updf_ext in *; auto. }

  { (* monotone *)
    introv bh h.
    pose proof (bh g) as q; autodimp q hyp.

    { apply functional_extensionality; introv.
      destruct x as [x p].
      pose proof (equal_f h (exist (fun m => m <? S n = true) x (lt2ltb (Nat.lt_lt_succ_r x n (ltb2lt p))))) as e.
      simpl in e.
      unfold baire2baire_n in *; simpl in *.
      rewrite <- e; clear e.
      unfold updf.
      applydup @ltb2lt in p.
      destruct (le_lt_dec (S n) x) as [d|d]; destruct (le_lt_dec n x) as [z|z]; try omega; auto.
      unfold ext.
      destruct (le_lt_eq_dec x n (lt_n_Sm_le x n (ltb2lt (lt2ltb d)))) as [w|w]; try omega; auto.
      f_equal; f_equal.
      apply UIP_dec; apply bool_dec. }

    { rewrite <- q; clear q.
      symmetry.
      apply bh.
      symmetry.

      apply functional_extensionality; introv.
      destruct x as [x p].
      unfold baire2baire_n in *; simpl in *.
      unfold updf.
      applydup @ltb2lt in p.
      destruct (le_lt_dec (S n) x) as [d|d]; destruct (le_lt_dec n x) as [z|z]; try omega; auto.
      unfold ext.
      destruct (le_lt_eq_dec x n (lt_n_Sm_le x n (ltb2lt (lt2ltb d)))) as [w|w]; try omega; auto.
      f_equal; f_equal.
      apply UIP_dec; apply bool_dec. }
  }

  { (* conclusion *)
    unfold PP in h; exrepnd.
    exists m; introv e.
    pose proof (h1 g) as q.
    autodimp q hyp.
    apply functional_extensionality; introv.
    destruct x as [x ltxm].
    unfold baire2baire_n; simpl.
    unfold updf.
    destruct (le_lt_dec 0 x); try omega; auto.
    applydup @ltb2lt in ltxm.
    apply e; auto. }
Qed.

Lemma untruncated_monotone_bar_induction_false :
  sq_continuity -> !(monotone_bar_induction).
Proof.
  introv scont bi.
  pose proof continuity_false as ucont.
  apply monotone_bar_induction_implies_continuity in bi; auto.
Qed.


(*

   This is about \forall\alpha\exists\beta-continuity.

   We show that it contradicts Kripke's Schema.
   This follows Dummett's proof in "Elements of Intuitionism (2nd edition)" p.246.
   The original proof is by Myhill in
   "Notes towards an axiomatization of intuitionistic analysis".

 *)

Definition cons_seq (n : S0) (a : S1) : S1 :=
  fun k => if zerop k then n else a (pred k).

Definition shift_seq (c : S2) (a : S1) : S1 :=
  fun n => c (cons_seq n a).

Definition ones : S1 := fun _ => 1.

Definition replace_from (a : S1) (n : nat) (d : nat) : S1 :=
  fun k => if le_lt_dec n k then d else a k.

Lemma replace_from_cons_seq :
  forall (a : S1) (x : S0) (n : nat) (d : nat),
    replace_from (cons_seq x a) (S n) d
    = cons_seq x (replace_from a n d).
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold replace_from, cons_seq.
  destruct (zerop x0); subst; simpl; auto.
  destruct x0; simpl; try omega.
  destruct (le_lt_dec n x0); subst; auto.
Qed.

Definition sq_continuity1_prop :=
  forall (A : S1 -> S1 -> Prop),
    (forall (a : S1), exists (b : S1), A a b)
    ->
    exists (c : S2),
      sq_continuity_prop_sch c
      /\ forall (a : S1), A a (shift_seq c a).

Definition kripke_s_schema :=
  forall (A : Prop),
  exists (a : S1),
    ((exists (x : nat), a(x) = 1) <-> A).

Lemma kripke_s_schema_contradicts_continuity1 :
  kripke_s_schema -> ~ sq_continuity1_prop.
Proof.
  introv KS CONT.
  remember (fun (a : S1) => forall (x : nat), a(x) = 1) as P.

  assert (forall (a : S1),
             exists (b : S1),
               ((exists (x : nat), b(x) = 1) <-> P(a))) as h.
  { introv; apply (KS (P a)). }

  applydup CONT in h.
  exrepnd.

  pose proof (h1 ones) as q.
  destruct q as [q' q]; clear q'; autodimp q hyp.
  { subst; auto. }
  exrepnd.

  unfold shift_seq in q0.

  pose proof (h0 (cons_seq x ones)) as w; exrepnd.
  pose proof (w0 (replace_from (cons_seq x ones) (S n) 0)) as e.
  autodimp e hyp.
  {
    introv ltmn.
    unfold cons_seq, replace_from.
    destruct (le_lt_dec (S n) m) as [d|d]; auto; try omega.
  }

  pose proof (h1 (replace_from ones n 0)) as z.
  destruct z as [z z']; clear z'; autodimp z hyp.
  {
    exists x.
    unfold shift_seq.
    rewrite replace_from_cons_seq in e.
    rewrite <- e; auto.
  }

  rewrite HeqP in z.
  pose proof (z n) as r.
  unfold replace_from in r.
  destruct (le_lt_dec n n); try omega.
Qed.
