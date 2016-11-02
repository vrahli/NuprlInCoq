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

Require Export tactics2.
Require Export terms_tacs.
Require Export Eqdep_dec.

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
  boolvar; omega.
Qed.

Lemma zero_until_prop2 :
  forall n k : nat, (zero_until n k) n = k.
Proof.
  introv.
  unfold zero_until.
  boolvar; omega.
Qed.

Definition S0 := nat.
Definition S1 := baire.
Definition S2 := baire -> nat.

(* unsquashed continuity *)
Definition usq_continuity :=
  forall (F : S2) (f : S1),
    {n : S0 & forall g : S1, eq_upto n f g -> F f = F g}.

(* Escardo's proof *)
Lemma continuity_false : usq_continuity -> False.
Proof.
  introv h.
  assert (forall (f : baire) (F : baire -> nat),
             {n : nat & forall g : baire, eq_upto n f g -> F f = F g}) as q by auto.
  clear h.
  pose proof (q zeros) as h.
  clear q.

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
  boolvar; try omega.
Qed.


(* It also works using an existential proposition *)

Definition AC20 :=
  forall (R : S2 -> S0 -> Prop),
    (forall a : S2, exists (b : S0), R a b)
    -> (exists (f : S2 -> S0), forall a : S2, R a (f a)).

Definition sq_continuity :=
  forall (F : S2) (f : S1), Cast {n : nat & forall g : S1, eq_upto n f g -> F f = F g}.

Definition sq_continuity_prop :=
  forall (F : S2) (f : S1), exists n, forall g : S1, eq_upto n f g -> F f = F g.

Lemma sq_continuity_iff_prop :
  sq_continuity <-> sq_continuity_prop.
Proof.
  introv; split; intro h; introv.

  { pose proof (h F f) as q; clear h.
    inversion q as [h]; clear q; exrepnd.
    exists n; auto. }

  { pose proof (h F f) as q; clear h; exrepnd.
    constructor; exists n; auto. }
Qed.

Lemma sq_continuity_prop_false :
  AC20
  -> sq_continuity_prop
  -> False.
Proof.
  introv ac h.
  assert (forall (f : S1) (F : S2),
             exists n, forall g : S1, eq_upto n f g -> F f = F g) as q by auto.
  clear h.
  pose proof (q zeros) as h.
  clear q.

  apply ac in h; exrepnd.
  (* This is a version of AC20.
   * We know that the q-truncated (i.e., quotiented by True) version
   * of this axiom is false in Nuprl, while it's consistent with Coq.
   *)
  rename f into M.

  remember (M (fun a => 0)) as m.

  remember (fun b => M (fun a => b (a m))) as f.

  assert (f zeros = m) as h1.
  { subst; auto. }

  assert (forall (b : S1), eq_upto (M f) zeros b -> m = f b) as h2.
  { introv q.
    pose proof (h0 f b) as zz.
    rewrite h1 in zz; auto. }

  assert (forall (b a : baire), eq_upto (f b) zeros a -> b 0 = b (a m)) as h3.
  { introv.
    rewrite Heqf.
    apply h0. }

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
  boolvar; try omega.
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

Definition bar_induction :=
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

Lemma bar_induction_implies_continuity :
   sq_continuity -> bar_induction -> usq_continuity.
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
    exists n (le_n n); auto.
  }

  { (* inductive *)
    introv h.
    pose proof (h (f n)) as q; clear h.
    unfold PP in *; exrepnd.
    exists m (le_Sn_le n m p); introv z.
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

Lemma untruncated_bar_induction_false :
  sq_continuity -> !(bar_induction).
Proof.
  introv scont bi.
  pose proof continuity_false as ucont.
  apply bar_induction_implies_continuity in bi; auto.
Qed.
