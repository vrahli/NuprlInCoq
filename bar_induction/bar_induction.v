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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export Peano.
Require Export Arith.
Require Export Arith.EqNat.
Require Export Eqdep_dec.
Require Export eq_rel.
Require Export tactics.
Require Export tactics2.


Lemma contraposition :
  forall A B : Type, (A -> B) -> (!B -> !A).
Proof. sp. Qed.

Definition ltb (n m : nat) : bool :=
  if lt_dec n m then true else false.

Definition Ltb (n m : nat) : Prop := ltb n m = true.

Lemma Ltb_proof_irrelevance :
  forall {n m : nat}
         (x y : Ltb n m),
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma Ltb_lt {n m : nat} : Ltb n m -> n < m.
Proof.
  introv h.
  unfold Ltb, ltb in h.
  destruct (lt_dec n m); ginv.
Qed.

Lemma lt_Ltb {n m : nat} : n < m -> Ltb n m.
Proof.
  introv h.
  unfold Ltb, ltb.
  destruct (lt_dec n m); tcsp.
Qed.

Definition nat_k (k : nat) := {n : nat & Ltb n k}.
Definition mk_nat_k {k} (n : nat) (p : Ltb n k) : nat_k k := existT _ n p.
Definition mk_nat_k1 {k} (n : nat) (p : n < k) : nat_k k := mk_nat_k n (lt_Ltb p).

Definition kseq (n : nat) := nat_k n -> nat.
Definition pseq := {n : nat & kseq n}.
Definition seq := nat -> nat.

Definition mk_pseq {n : nat} (f : kseq n) : pseq := existT _ n f.

Definition emseq : seq := fun x => 0.
Definition emkseq : kseq 0 := fun x => 0.
Definition empseq : pseq := mk_pseq emkseq.

Definition m_seq2kseq (s : seq) (n : nat) : kseq n :=
  fun x =>
    match x with
      | existT _ k ltk => s k
    end.

Definition m_seq2pseq (s : seq) (n : nat) : pseq :=
  mk_pseq (m_seq2kseq s n).

Definition extend1 (n : nat) (f : kseq n) (k : nat) : kseq (S n) :=
  fun x =>
    match x with
      | existT _ m _ =>
        match lt_dec m n with
          | left p => f (mk_nat_k1 m p)
          | _ => k
        end
    end.

Definition extend (s : pseq) (k : nat) : pseq :=
  match s with
    | existT _ n f => mk_pseq (extend1 n f k)
  end.

Definition barind_dec (R : pseq -> Type) : Type :=
  forall (s : pseq), R s [+] !(R s).

Definition barind_bared (R : pseq -> Type) : Prop :=
  forall (s : seq),
    exists n, Cast (R (m_seq2pseq s n)).

Definition barind_imp (R : pseq -> Type) (A : pseq -> Prop) : Type :=
  forall (s : pseq), R s -> A s.

Definition barind_ind (A : pseq -> Prop) : Type :=
  forall (s : pseq),
    (forall k, A (extend s k))
    -> A s.

Require Export Classical_Pred_Type.

Lemma barind_ind_cont :
  forall (A : pseq -> Prop),
    barind_ind A
    -> forall s,
         !(A s)
         -> exists k, !(A (extend s k)).
Proof.
  introv bi na.
  pose proof (bi s) as h; clear bi.
  apply contraposition in h; auto.
  apply not_all_ex_not in h; auto.
Qed.

Definition barind (R : pseq -> Type) (A : pseq -> Prop) : Type :=
  barind_dec R
  -> barind_bared R
  -> barind_imp R A
  -> barind_ind A
  -> A empseq.

Definition pseqNA (A : pseq -> Prop) :=
  {s : pseq & !(A s)}.

Definition mk_pseqna {A : pseq -> Prop}
           (s : pseq)
           (p : !(A s)) : pseqNA A :=
  existT _ s p.

Definition pseqNA2seq {A : pseq -> Prop}
           (s : pseqNA A) : pseq := projT1 s.

Lemma nat_le : forall n, 0 <= n.
Proof. introv; omega. Qed.

Lemma nat_lt_S : forall n, n < S n.
Proof. introv; omega. Qed.

Lemma le2ltS : forall {n m}, n <= m -> n < S m.
Proof. introv; omega. Qed.

Lemma le2leS : forall {n m}, n <= m -> n <= S m.
Proof. introv; omega. Qed.

Definition kseq_at {n : nat} (s : kseq n) (m : nat) (p : m < n) : nat :=
  s (mk_nat_k1 m p).

Definition kseqNA (n : nat) (A : pseq -> Prop) :=
  {m : nat
   & {s : kseq (S n)
   & kseq_at s n (nat_lt_S n) = m
   # !(A (mk_pseq s)) }}.

Definition kseqNA2seq {n : nat} {A : pseq -> Prop}
           (k : kseqNA n A) : kseq (S n) :=
  match k with
    | existT _ _ (existT _ s _) => s
  end.

Definition kseqNA2m {n : nat} {A : pseq -> Prop}
           (k : kseqNA n A) : nat :=
  match k with
    | existT _ m _ => m
  end.

Definition mk_kseqna {n : nat} {A : pseq -> Prop}
           (m : nat)
           (s : kseq (S n))
           (q : kseq_at s n (nat_lt_S n) = m)
           (p : !(A (mk_pseq s))) : kseqNA n A :=
  existT _ m (existT _ s (q,p)).

Lemma kseq_at_extend1 :
  forall (n : nat)
         (g : kseq (S n))
         (k : nat),
    kseq_at (extend1 (S n) g k) (S n) (nat_lt_S (S n)) = k.
Proof.
  introv.
  unfold kseq_at, extend1; simpl.
  destruct (lt_dec (S n) (S n)); omega.
Qed.

Fixpoint alpha
         (A : pseq -> Prop)
         (h : !A empseq)
         (f : pseqNA A -> nat)
         (ind : forall a : pseqNA A, !A (extend (pseqNA2seq a) (f a)))
         (n : nat) : kseqNA n A :=
  match n with
    | 0 =>
      let ps := empseq in
      let p := mk_pseqna ps h in
      let k := f p in
      mk_kseqna k (extend1 0 emkseq k) eq_refl (ind p)
    | S n =>
      let (_,r) := alpha A h f ind n in
      let (g,pp) := r in
      let (_,na) := pp in
      let ps := mk_pseq g in
      let p := mk_pseqna ps na in
      let k := f p in
      mk_kseqna k (extend1 (S n) g k) (kseq_at_extend1 n g k) (ind p)
  end.

Definition kseq2kseq (n m : nat) (s : kseq n) (lemn : m <= n) : kseq m :=
  fun x =>
    match x with
      | existT _ k ltkm => s (mk_nat_k1 k (lt_le_trans k m n (Ltb_lt ltkm) lemn))
    end.

Definition kseqS2kseq (n : nat) (s : kseq (S n)) : kseq n :=
  fun x =>
    match x with
      | existT _ k ltkn => s (mk_nat_k1 k (lt_trans k n (S n) (Ltb_lt ltkn) (nat_lt_S n)))
    end.

Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Lemma fun_app :
  forall {A : Type} {B : A -> Type}
         (a : A)
         (f g : forall a : A, B a),
    f = g -> f a = g a.
Proof.
  introv e.
  subst; auto.
Qed.

Lemma alpha_prop1 :
  forall (A : pseq -> Prop)
         (h : !A empseq)
         (f : pseqNA A -> nat)
         (ind : forall a : pseqNA A, !A (extend (pseqNA2seq a) (f a)))
         (n m : nat)
         (lemn : m <= n),
    kseq2kseq (S n) (S m) (kseqNA2seq (alpha A h f ind n)) (le_n_S m n lemn)
    = kseqNA2seq (alpha A h f ind m).
Proof.
  introv.
  assert {k : nat & n = k + m} as e.
  { exists (n - m); omega. }
  exrepnd; subst.
  remember (le_n_S m (k + m) lemn) as lem; clear Heqlem lemn.
  induction k; introv;
  apply functional_extensionality_dep; introv; allsimpl.

  - unfold kseq2kseq.
    destruct x; allsimpl.
    unfold mk_nat_k1, mk_nat_k.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l2
    end; clear Heql2.

    pose proof (Ltb_proof_irrelevance l l2) as e; subst; auto.

  - assert (S m <= S (k + m)) as e by omega.
    pose proof (IHk e) as q; clear IHk.
    rw <- q; clear q.
    unfold kseq2kseq.
    destruct x; allsimpl.

    remember (alpha A h f ind (k + m)) as am.
    unfold kseqNA in am; exrepnd; allsimpl.
    subst.
    dup l as ltx.
    apply Ltb_lt in ltx.
    destruct (lt_dec x (S (k + m))) as [d|d]; try omega;[].

    allunfold @mk_nat_k1.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l1
    end; clear Heql1.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l2
    end; clear Heql2.

    pose proof (Ltb_proof_irrelevance l1 l2) as xx; subst; auto.
Qed.

Lemma kseqNA2seq_last :
  forall (n : nat) (A : pseq -> Prop) (k : kseqNA n A),
    kseqNA2seq k (mk_nat_k n (lt_Ltb (nat_lt_S n)))
    = kseqNA2m k.
Proof.
  introv.
  unfold kseqNA2seq, kseqNA2m.
  destruct k; exrepnd.
  rw <- s2.
  unfold kseq_at.
  unfold mk_nat_k1; auto.
Qed.

Lemma emkseq_eq :
  forall s, emkseq = m_seq2kseq s 0.
Proof.
  introv.
  apply functional_extensionality_dep; introv; allsimpl.
  destruct x.
  dup l as q.
  apply Ltb_lt in q.
  destruct x; try omega.
Qed.

Axiom FunctionalChoice_on :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall a : A, exists (b : B), R a b)
    -> (exists (f : A -> B), forall a : A, R a (f a)).

Require Export Classical_Prop.

(* Following Dummett's proof *)
Lemma barind_true_classically :
  forall (R : pseq -> Type) (A : pseq -> Prop),
    barind R A.
Proof.
  introv dec bar imp ind.
  pose proof (classic (A empseq)) as h.
  repndors; auto.
  provefalse.

  (* we now construct a sequence s which has no initial segment in R,
     i.e., forall n, ~(R (seq2pseq s n)) *)
  pose proof (barind_ind_cont A ind) as ind1; clear ind.

  assert (forall x : pseqNA A,
            exists k, !A (extend (pseqNA2seq x) k)) as ind2.
  { unfold pseqNA; introv; exrepnd; simpl; auto. }
  clear ind1.
  apply FunctionalChoice_on in ind2; exrepnd.
  rename ind0 into ind.

  remember (alpha A h f ind) as g.

  remember (fun m => kseqNA2m (g m)) as s.

  assert (forall n,
            m_seq2pseq s n
            = mk_pseq (kseqS2kseq n (kseqNA2seq (g n)))) as e.
  { introv; unfold m_seq2pseq.
    f_equal.
    subst.
    apply functional_extensionality_dep; introv.
    destruct x.

    unfold m_seq2kseq.
    unfold kseqS2kseq.

    unfold mk_nat_k1.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l1
    end; clear Heql1.
    clear l.

    dup l1 as ltx.
    apply Ltb_lt in ltx.
    applydup lt_n_Sm_le in ltx as ltx2.

    pose proof (alpha_prop1 A h f ind n x ltx2) as e.
    apply (fun_app (mk_nat_k x (lt_Ltb (nat_lt_S x)))) in e.
    rw kseqNA2seq_last in e.
    rw <- e.

    unfold kseq2kseq; simpl.
    unfold mk_nat_k1.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l2
    end; clear Heql2.

    pose proof (Ltb_proof_irrelevance l1 l2) as xx; subst; auto.
  }

  pose proof (bar s) as b.
  exrepnd.
  inversion b0 as [b]; clear b0.
  apply imp in b.

  induction n; allsimpl.

  { unfold m_seq2pseq in b; allsimpl.
    rw <- emkseq_eq in b; auto. }

  pose proof (e (S n)) as q1.
  rw q1 in b.
  pose proof (e n) as q2.
  rw q2 in IHn.
  clear q1 q2 e.
  subst.
  allsimpl.
  remember (alpha A h f ind n) as an.
  unfold kseqNA in an; exrepnd; allsimpl.

  assert (kseqS2kseq (S n) (extend1 (S n) s (f (mk_pseqna (mk_pseq s) an1))) = s) as ee.
  { apply functional_extensionality_dep; introv.
    destruct x.
    unfold kseqS2kseq; simpl.
    dup l as ltx.
    apply Ltb_lt in ltx.
    destruct (lt_dec x (S n)); try omega.
    unfold mk_nat_k1, mk_nat_k.

    match goal with
      | [ |- context[lt_Ltb ?a] ] => remember (lt_Ltb a) as l2
    end; clear Heql2.

    pose proof (Ltb_proof_irrelevance l l2) as xx; subst; auto.
  }

  rw ee in b; auto.
Qed.
