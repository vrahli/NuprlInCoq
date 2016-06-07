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


(*Require Export SfLib.*)
Require Export Coq.Init.Notations.
Require Export tactics.
Require Export Peano.
Require Export Basics.
Require Export Bool.
Require Export Arith.
Require Export Arith.EqNat.
Require Export Omega.


(* Prop/Type exists depending on the switch universe-type.v/universe-prop.v *)
Notation "{ a , b : T $ P }" :=
  {a : T $ {b : T $ P}}
    (at level 0, a at level 99, b at level 99).
Notation "{ a , b , c : T $ P }" :=
  {a : T $ {b : T $ {c : T $ P}}}
    (at level 0, a at level 99, b at level 99, c at level 99).
Notation "{ a , b , c , d : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ P}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99).
Notation "{ a , b , c , d , e : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ {e : T $ P}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99).
Notation "{ a , b , c , d , e , f : T $ P }" :=
  {a : T $ {b : T $ {c : T $ {d : T $ {e : T $ {f : T $ P}}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99, f at level 99).


(* Some extra notation from SfLib *)
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

(* Some lemmas from SfLib *)
Theorem beq_nat_sym :
  forall (n m : nat),
    beq_nat n m = beq_nat m n.
Proof.
  induction n; sp.
  unfold beq_nat; destruct m; sp.
  simpl; destruct m; simpl; sp.
Qed.

Definition Deq (T : Type) := forall (x y : T), {x = y} + {x <> y}.

Lemma deq_prod :
  forall (A B : Type), Deq A -> Deq B -> Deq (A * B).
Proof.
  unfold Deq; introv da db; introv; sp.
  generalize (da x0 y0) (db x y); introv ea eb; sp; subst; sp;
  right; intro k; inversion k; sp.
Defined.

Hint Resolve deq_prod : Deq.

Definition assert (b : bool) : Prop := b = true.

Lemma assert_true : assert true.
Proof.
  sp.
Qed.
Hint Immediate assert_true.

Lemma not_assert_false : !(assert false).
Proof.
  unfold assert; sp.
Qed.
Hint Immediate not_assert_false.

Lemma fold_assert :
  forall b,
    (b = true) = assert b.
Proof.
  unfold assert; auto.
Qed.

Lemma assert_orb :
  forall a b,
    assert (a || b) -> assert a + assert b.
Proof.
  destruct a; destruct b; sp.
Qed.

Lemma assert_andb :
  forall a b,
    assert (a && b) <-> assert a /\ assert b.
Proof.
  destruct a; destruct b; sp; split; sp.
Qed.

Lemma assert_of_andb :
  forall a b,
    assert (a && b) <=> assert a # assert b.
Proof.
  destruct a; destruct b; sp; split; sp.
Qed.

Lemma not_assert :
  forall b, b = false <-> ~ assert b.
Proof.
  destruct b; unfold assert; simpl; split; sp.
Qed.

Lemma not_of_assert :
  forall b, b = false <=> ! assert b.
Proof.
  destruct b; unfold assert; simpl; split; sp.
Qed.

Lemma andb_true :
  forall a b,
    a && b = true <-> a = true /\ b = true.
Proof.
  destruct a; destruct b; simpl; sp; split; sp.
Qed.

Lemma andb_eq_true :
  forall a b,
    a && b = true <=> (a = true) # (b = true).
Proof.
  destruct a; destruct b; simpl; sp; split; sp.
Qed.


(* ------ useful stuff ------ *)

Lemma max_prop1 :
  forall a b, a <= max a b.
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto.
  assert (a <= max a b); auto; omega.
Qed.

Lemma max_prop2 :
  forall a b, b <= max a b.
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto; try omega.
  assert (b <= max a b); auto; omega.
Qed.

Lemma max_or :
  forall a b,
    (max a b = a) \/ (max a b = b).
Proof.
  induction a; simpl; sp; try omega.
  destruct b; auto.
  assert (max a b = a \/ max a b = b) by apply IHa; sp.
Qed.

Theorem comp_ind:
  forall P: nat -> Prop,
    (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
    -> forall n:nat, P n.
Proof.
 intros P H n.
 assert (forall n:nat , forall m:nat, m < n -> P m).
 intro n0. induction n0 as [| n']; intros.
 inversion H0.
  apply le_S_n in H0.
  apply le_lt_or_eq in H0.
 sp; subst; sp.
 apply H0 with (n := S n).
  auto.
Qed.

Theorem comp_ind_type :
  forall P: nat -> Type,
    (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
    -> forall n:nat, P n.
Proof.
 intros P H n.
 assert (forall n:nat , forall m:nat, m < n -> P m).
 intro n0. induction n0 as [| n']; intros.
 omega.
 destruct (eq_nat_dec m n'); subst; auto.
 apply IHn'; omega.
 apply H; apply X.
Defined.

(*
Print NTerm_ind.

Print eq_refl.

Require Import Eqdep.

Axiom dec_eq_eq :
  forall (A : Type),
    (forall a b : A, {a = b} + {a <> b})
    -> forall a b : A,
       forall e e' : a = b,
         e = e'. (* Proved in Eqdep_dec. *)

Definition eq_dep_eq_dec'
           (A : Type)
           (dec_eq : forall a b : A, {a = b} + {a <> b})
           (X : A -> Type)
           (a : A)
           (x y : X a)
           (e : eq_dep A X a x a y) : x = y
 := (match e in eq_dep _ _ _ _ a' y' return
          forall e' : a = a',
            (match e' in _ = a' return X a' with
                eq_refl => x
            end) = y'
    with
    | eq_dep_intro =>
      fun e : a = a =>
        match dec_eq_eq A dec_eq a a (eq_refl a) e
              in _ = e
              return match e in _ = a' return X a' with eq_refl => x end = x with
          | eq_refl => eq_refl x
        end
    end) (eq_refl a).
*)



Lemma trivial_if :
  forall T,
  forall b : bool,
  forall t : T,
    (if b then t else t) = t.
Proof.
  intros;  destruct b; auto.
Qed.

Hint Rewrite trivial_if.

Lemma minus0 :
  forall n, n - 0 = n.
Proof.
  destruct n; auto.
Qed.

Lemma pair_inj :
  forall A B,
  forall a c : A,
  forall b d : B,
    (a, b) = (c, d) -> a = c /\ b = d.
Proof.
  sp; inversion H; sp.
Qed.

Lemma S_inj :
  forall a b, S a = S b -> a = b.
Proof.
  auto.
Qed.

Lemma S_le_inj :
  forall a b, S a <= S b -> a <= b.
Proof.
  sp; omega.
Qed.

Lemma S_lt_inj :
  forall a b, S a < S b -> a < b.
Proof.
  sp; omega.
Qed.

Lemma not_or :
  forall a b,
    ~ (a \/ b) -> ~ a /\ ~ b.
Proof.
  sp; apply H; sp.
Qed.

Lemma not_over_or :
  forall a b,
    !(a [+] b) <=> !a # !b.
Proof.
  sp; split; sp.
Qed.

Theorem apply_eq :
  forall {A B} (f: A -> B) {a1 a2:A},
    a1 = a2 -> f a1 = f a2.
Proof. intros. rewrite H. reflexivity.
Qed.

Theorem iff_push_down_forall : forall A (P Q: A-> Prop) ,
  (forall a, P a <=> Q a) -> ((forall a, P a) <=> (forall a, Q a)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Theorem iff_push_down_forallT : forall A (P Q: A-> [univ]) ,
  (forall a, P a <=> Q a) -> ((forall a, P a) <=> (forall a, Q a)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Theorem iff_push_down_impliesT : forall P Q R,
  (R -> (P <=> Q)) -> ((R -> P) <=> (R -> Q)).
Proof. introv Hiff. repeat split; intros; apply Hiff; auto.
Qed.

Lemma sum_assoc :
  forall a b c,
    (a [+] (b [+] c)) <=> ((a [+] b) [+] c).
Proof.
  sp; split; sp.
Qed.

Definition isInl {A B : Type} 
    (d : A + B) : bool :=
match d with
| inl _ => true
| inr _ => false
end.

Definition isInr {A B : Type} 
    (d : A + B) : bool :=
match d with
| inl _ => false
| inr _ => true
end.

Definition isInlInl {A B C D: Type} 
    (d : (A + B) + (C + D)) : bool :=
match d with
| inl (inl _) => true
| _ => false
end.


Definition liftNth {A: Type} 
    (f : A-> bool) (l : list A ) (n:nat) : bool :=
match (nth_error l n) with
| Some x => f x
| None => false
end.

Definition liftInl {A B : Type} 
    (f : A -> bool) (d : A + B) : bool :=
match d with
| inl a => f a
| inr _ => false
end.

Notation deq_nat := Nat.eq_dec.
Hint Resolve Nat.eq_dec : Deq.



(* ========= DEPENDENT PAIRS ========= *)

Definition eq_existsT (A : Type)
                      (B : A -> Type)
                      (a a' : A)
                      (b : B a)
                      (b' : B a')
                      (ea : a = a')
                      (eb : match ea in _ = a' return B a' with eq_refl => b end = b')
  : existT B a b = existT B a' b'
  := match ea as ea
              in _ = a'
        return forall b' : B a',
                 match ea in _ = a' return B a' with eq_refl => b end = b'
                 -> existT B a b = existT B a' b'
     with
       | eq_refl => fun b' eb => match eb with eq_refl => eq_refl (existT B a b) end
     end b' eb.

Lemma dep_pair_eq :
  forall {T : Type} {a b : T} (eq : a = b) (P : T -> Prop) (pa : P a) (pb : P b),
    @eq_rect T a P pa b eq = pb
    -> exist P a pa = exist P b pb.
Proof.
  intros.
  rewrite <- H.
  rewrite <- eq.
  reflexivity.
Qed.



Ltac apply_tiff_f H1 H2 :=
  let H3 := fresh in (
    (pose proof (fst (H1) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (fst(H1 _ _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3)).

Ltac apply_tiff_b H1 H2 :=
  let H3 := fresh in (
    (pose proof (snd (H1) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
    (pose proof (snd(H1 _ _ _ _ _ _ _) H2) as H3; clear H2; pose proof H3 as H2; clear H3)).

Tactic Notation "apply_tiff"  constr(H1) constr(H2) :=
 (apply_tiff_f H1 H2 || apply_tiff_b H1 H2) .


Tactic Notation "refl" := reflexivity.


Theorem and_tiff_compat_l:
 forall A B C : [univ], (B <=> C) -> (A # B <=> A # C).
Proof. 
 introv Hiff. rw Hiff. apply t_iff_refl. 
Qed.

Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
@eq_rect T a P pa b eq.

Definition typeCast {A B:Type}  (eq:A=B) (pa: A) : (B):=
@eq_rect Type A (fun X => X) pa B eq.

Definition injective_fun {A B: Type} (f: A->B)  :=
  forall (a1 a2: A), (f a1= f a2) -> a1=a2.

Lemma min_eq : forall n1 n2,
  n1=n2 -> min n1 n2 = n2.
Proof.
  introv H. rewrite  H.
  apply Min.min_idempotent.
Qed.

Lemma negb_eq_true :
  forall b, negb b = true <=> ! (assert b).
Proof.
  intro.
  unfold assert; destruct b; simpl; split; sp.
Qed.

Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Type :=
 forall s: S , (g (f s)) = s.

Definition bijection  {S T : Type} (f: S -> T) (g: T-> S) : Type
 := prod (left_identity f g)  (left_identity g f). 

Definition injection {S T : Type} (f: S -> T) :=
  forall (s1 s2 : S), (f s1 = f s2) -> s1=s2.

Lemma left_id_injection: forall {S T : Type} (f: S -> T) (g: T-> S),
  left_identity f g -> injection f.
Proof.
  introv lid feq.
  apply_eq g feq ffeq.
  rw lid in ffeq.
  rw lid in ffeq.
  trivial.
Qed.

Definition equipollent (A B : Type)
 := {f : A -> B $ { g : B -> A $ bijection f g }}.

(** constructive defn. of surjection -- it gives
    the right inverse for free. classical one may
    be obtained by changing [sig] to [ex] *)
Definition Csurjection {S T : Type} (f: S -> T) :=
  forall (t : T), {s : S $ f s =t}.

Lemma injection_surjection_equipollent 
  : forall {S T : Type} (f: S -> T) ,
  injection f
  -> Csurjection f
  -> equipollent S T.
Proof.
Abort.
(**
http://cstheory.stackexchange.com/questions/18962/formalizing-the-theory-of-finite-sets-in-type-theory
*)
Definition Fin (n:nat)
  := {m:nat & if lt_dec m n then unit else void}.

 
Lemma Fin_eq:
  forall (n: nat) (fa fb : Fin n),
    (projT1 fa) = (projT1 fb)
    -> fa = fb.
Proof.
  introv Heq.
  destruct fa as [a ap].
  destruct fb as [b bp].
  allsimpl.
  subst.
  apply eq_existsT with (ea := eq_refl).
  remember (lt_dec b n); destruct s; destruct ap, bp; auto.
Qed.

Lemma Fin_decidable : forall (n:nat), Deq (Fin n).
Proof.
  unfold Deq.
  intros.
  destruct (Nat.eq_dec (projT1 x) (projT1 y)) as [T|F];[left|right].
  - apply Fin_eq; auto.
  - intro Heq. destruct F. destruct x. destruct y.
    inverts Heq. allsimpl. reflexivity.
Defined.

Hint Resolve Fin_decidable : Deq.

Lemma equipollent_Deq : forall (A B:Type), 
    Deq A 
    -> equipollent A B 
    -> Deq B.
Proof.
  unfold Deq, equipollent, bijection.
  introv Ha Heq. intros. exrepnd.
  pose proof (Ha (g x) (g y)) as Hd.
  dorn Hd; [left| right].
  - apply left_id_injection in Heq1.
    repnud Heq1. auto.
  - introv Heq. apply Hd. f_equal; auto.
Qed.


Hint Resolve equipollent_Deq : Deq.


Lemma bool2_Equi :
  equipollent bool (Fin 2).
Abort.

(** This is a strong constructive version of
    finiteness of a type. It says that
    there should be a bijection between 
    some finite initial segment of numbers
    and that type *)
Definition Finite (T : Type) :=
  {n:nat $ equipollent ( Fin n) T}.

Lemma Finite_Deq : forall (A:Type), 
    Finite A 
    -> Deq A.
Proof.
  introv Hf.
  repnud Hf. exrepnd.
  (* info_eauto with Deq *)
    eapply equipollent_Deq.
    apply Fin_decidable.
    exact Hf0.
Qed.

Hint Resolve Finite_Deq : Deq.

Lemma prod_assoc :
  forall a b c,
    (a # b) # c <=> a # (b # c).
Proof.
  sp; split; sp.
Qed.

Lemma prod_comm :
  forall a b,
    a # b <=> b # a.
Proof.
  sp; split; sp.
Qed.

Lemma or_true_l :
  forall t, True [+] t <=> True.
Proof. sp. Qed.

Lemma or_true_r :
  forall t, t [+] True <=> True.
Proof. sp. Qed.

Lemma or_false_r : forall t, t [+] False <=> t.
Proof. sp; split; sp. Qed.

Lemma or_false_l : forall t, False [+] t <=> t.
Proof. sp; split; sp. Qed.

Lemma and_true_l :
  forall t, True # t <=> t.
Proof. sp; split; sp. Qed.

Lemma not_false_is_true : !False <=> True.
Proof. sp; split; sp. Qed.

Lemma forall_num_lt_d : forall m P,
  (forall n, n < S m -> P n)
  -> P 0 # (forall n, n <  m -> P (S n) ).
Proof.
  introv Hlt.
  dimp (Hlt 0); auto; [omega|].
  dands; auto.
  introv Hgt.
  apply lt_n_S in Hgt.
  eauto.
Qed.
Ltac dforall_lt_hyp name := 
  repeat match goal with
  [ H : forall  n : nat , n< S ?m -> ?C |- _ ] => 
    apply forall_num_lt_d in H;
    let Hyp := fresh name in
    destruct H as [Hyp H]
  | [ H : forall  x : ?T , _ < 0 -> _ |- _ ] => clear H
  end.

Lemma not_over_and :
  forall a b,
    decidable a -> (!(a # b) <=> !a [+] !b).
Proof.
  introv d; split; intro k; tcsp.
  dorn d.
  - right; intro h.
    apply k; sp.
  - left; auto.
Qed.

Lemma decidable_prod : forall
  (P Q: [univ]),
  decidable P
  -> decidable Q
  -> decidable (P * Q).
Proof.
  introv Hpd Hqd.
  unfold decidable;
  destruct Hpd; destruct Hqd;
  try (left; dands; auto; fail);
  (right; introv Hc; repnd; auto).
Defined.


Require Import Coq.Logic.Eqdep_dec.


Lemma UIPReflDeq: forall { A : Type} (deq : Deq A)
  (a: A) (p: a=a), p = eq_refl.
Proof.
  intros.
  remember (@eq_refl A a) as eqr.
  apply UIP_dec.
  auto.
Qed.

Definition DeqP (A : Type):=
forall x0 y0 : A, x0 = y0 \/ x0 <> y0.

Lemma DeqDeqp : forall {A : Type},
  Deq A -> DeqP A.
Proof.
  introv deq.
  intros x y.
  destruct (deq x y);[left|right]; auto.
Qed.


(** copied from Coq.Logic.EqDep_dec.v
    and converted things from Prop to Type
    (and ex to sigT) *)

 Let projT {A : Type} {x: A} (dec: Deq A)
  {P:A -> Type} (exP: sigT P) (def:P x) : P x :=
   match exP with
     | existT _ x' prf =>
       match dec x' x with
         | left eqprf => eq_rect x' P prf x eqprf
         | _ => def
       end
   end.
 Theorem injRightsigT: 
   forall  {A : Type} {x: A} (dec: Deq A) (P:A -> Type)  (y y':P x),
     existT P x y = existT P x y' -> y = y'.
 Proof.
   intros.
   cut (projT dec 
      (existT _ x y) y = projT dec (existT _ x y') y).
   simpl.
   case (dec x x).
   intro e.
   elim e using K_dec; trivial.

  apply DeqDeqp. trivial.

   intros.
   case n; trivial.

   case H.
   reflexivity.
 Qed.

Ltac EqDecSndEq :=
  let dec:= fresh "dec" in
repeat match goal with
[H : @existT ?A _ _ _ = _ |- _ ] => 
  assert (Deq A) as dec by eauto with Deq;
  apply (injRightsigT dec) in H; clear dec
end.

Lemma DeqTrue:  forall {A} (deq : Deq A) (a : A),
  (deq a a) = (left (@eq_refl A a)).
Proof.
  intros; auto.
  destruct (deq a a) as [HH| HH].
  - f_equal.
    apply UIPReflDeq; auto.
  - destruct HH. auto.
Defined.

Lemma DeqSym:  forall {A} T (deq : Deq A) (a b: A)
  (f : (a=b) -> T) (c:T),
  match deq a b with
  | left p => f p
  | _ => c
  end 
  =
  match deq b a with
  | left p => f (eq_sym p)
  | _ => c
  end.
Proof.
  intros.
  destruct (deq a b) as [HH| HH].
  - destruct (deq a b) as [H| H]; subst;sp.
    destruct (deq b b); sp;[].
    pose proof (UIPReflDeq deq _  e) as XX.
    rw XX.
    auto.
  - destruct (deq b a) as [H| H]; subst; sp.
Defined.

Definition constantFn {A B : Type} (f: A-> B): [univ] :=
  forall a1 a2, f a1 = f a2.

Lemma constantMapEq :
  forall {A B : Type} (f: A-> B),
  constantFn f
  -> forall l1 l2,
        length l1 = length l2
        -> map f l1 = map f l2.
Proof.
  introv Hc. repnud Hc.
  induction l1 as [| h1 t1 Hind]; introv Hleq;
  destruct l2; inverts Hleq;[|]; simpl. auto.
  f_equal; auto; congruence.
Defined.

Definition DeqBool : Deq bool := bool_dec.

Hint Resolve  deq_prod DeqBool: Deq.

Definition sigTDeq
 {A : Type} (deq : Deq A)
  (P : A -> Type)
  (deqf : forall (a:A), Deq (P a)) :
  Deq (sigT P).
  introv.
  destruct (deq (projT1 x) (projT1 y)) as [Heq | Hneq];
    [| right].
  - destruct x as [xa xb]. allsimpl.
    revert xb. rewrite Heq.
    intros. allsimpl.
    destruct y as [ya yb].
    allsimpl.
    destruct ((deqf ya) xb yb) as [beq | bneq];[left|right].
    + f_equal; auto.
    + introv Hc. EqDecSndEq.
      apply bneq. exact Hc.
  - introv Heq. apply (f_equal (@projT1 _ _)) in Heq.
    apply Hneq. exact Heq.
Defined.

Definition Deq2Bool {A : Type} (deq : Deq A) (a b : A)
  : bool.
destruct (deq a b);[exact true | exact false].
Defined.

Hint Resolve sigTDeq : Deq.

Lemma and_true_r :
  forall t, t # True <=> t.
Proof. sp; split; sp. Qed.

Lemma true_eq_same : forall T (t : T), t = t <=> True.
Proof. sp; split; sp. Qed.
