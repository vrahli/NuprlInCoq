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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

 *)


Require Export unsquashed_continuity.
Require Export Coq.Logic.ConstructiveEpsilon.


(*

  Some results from Kripke's
  "Semantical Analysis of Intuitionistic Logic I" (p.104).

  This is a theory of absolutely free choice sequences (afcs)
  but I've used [baire] here, which is bogus (and several concrete
  sequences that are not absolutely free).  For example the
  axiom [continuity_seq_prop] of LC is clearly false if we don't
  restrict ourselves to afcs's...but at least this gives a rough idea
  of what's going on...

  Could I use an axiomatization of afcs's instead of [baire]?

 *)

Definition continuity_seq_prop :=
  forall (A : baire -> Prop) (a : baire),
    A a -> exists (p : nat), forall (b : baire), eq_upto p a b -> A b.

Definition uniform_continuity :=
  forall (F : cantor -> nat),
    {n : nat | forall (f g : cantor), eq_upto n f g -> F f = F g}.

(* sequences can either increase by one or not increase at all *)
Definition increasing (a : baire) : Prop :=
  forall (n : nat), a (S n) = a n \/ a (S n) = S (a n).

Definition init0 (a : baire) : Prop := a 0 = 0.

Definition initF (a : cantor) : Prop := a 0 = false.

(* if a(pred n)=a(n) then b2c(a)(n)=false otherwise b2c(a)(n)=true, meaning it increases *)
Definition baire2cantor (a : baire) : cantor :=
  fun n => if eq_nat_dec (a (pred n)) (a n) then false else true.

(* We have to pick the initial value at 0.  We chose 0, which is why we
   require the [init0] condition below. *)
Fixpoint cantor2baire (a : cantor) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n =>
    let m := cantor2baire a n in
    if a (S n) then
      S m
    else
      m
  end.

Lemma increasing_cantor2baire :
  forall (a : cantor), increasing (cantor2baire a).
Proof.
  intros a n; simpl.
  destruct (a (S n));[right|left];auto.
Qed.
Hint Resolve increasing_cantor2baire : cont.

Lemma init0_cantor2baire :
  forall (a : cantor), init0 (cantor2baire a).
Proof.
  intros a; simpl.
  unfold init0; simpl; auto.
Qed.
Hint Resolve init0_cantor2baire : cont.

Lemma initF_baire2cantor :
  forall (a : baire), initF (baire2cantor a).
Proof.
  intros a; simpl.
  unfold initF, baire2cantor; simpl.
  destruct (Nat.eq_dec (a 0) (a 0)); auto; omega.
Qed.
Hint Resolve initF_baire2cantor : cont.

Lemma cantor2baire2cantor :
  forall (a : cantor), initF a -> baire2cantor (cantor2baire a) = a.
Proof.
  introv init.
  apply functional_extensionality; introv.

  unfold baire2cantor; simpl.

  destruct x; simpl; auto.
  remember (cantor2baire a x) as m.
  destruct (a (S x)).

  - destruct (Nat.eq_dec m (S m)); auto; try omega.

  - destruct (Nat.eq_dec m m); auto; try omega.
Qed.

Lemma baire2cantor2baire :
  forall (a : baire),
    init0 a
    -> increasing a
    -> cantor2baire (baire2cantor a) = a.
Proof.
  introv init inc.
  apply functional_extensionality; introv.

  induction x; simpl; auto.
  rewrite IHx; clear IHx.
  unfold baire2cantor; simpl.

  destruct (Nat.eq_dec (a x) (a (S x))); try omega.
  pose proof (inc x) as h; destruct h; auto; try omega.
Qed.

(* A non increasing sequence: *)
Definition non_inc_seq : baire :=
  fun n =>
    if eq_nat_dec n 0 then 0
    else if eq_nat_dec n 1 then 1
         else 0.

(* we now prove that we need the [increasing] hypothesis to prove [baire2cantor2baire] *)
Lemma baire2cantor2baire_needs_increassing :
  cantor2baire (baire2cantor non_inc_seq) <> non_inc_seq.
Proof.
  introv h.
  apply equal_f with (x := 2) in h.
  simpl in h.
  unfold non_inc_seq in h; simpl in h; omega.
Qed.

Fixpoint least_greater_aux (b : baire) (n : nat) (x : nat) : option nat :=
  match n with
  | 0 => None
  | S m =>
    match least_greater_aux b m x with
    | Some k => Some k
    | None => if le_lt_dec x (b m) then Some m else None
    end
  end.

Definition least_greater (b : baire) (n : nat) (x : nat) : nat :=
  match least_greater_aux b n x with
  | Some k => k
  | None => n
  end.

Definition least_greater_aux_prop1 :
  forall b n x k,
    least_greater_aux b n x = Some k
    -> x <= b k.
Proof.
  induction n; introv h; simpl in *; try (inversion h; fail).
  remember (least_greater_aux b n x) as l; symmetry in Heql; destruct l.

  - inversion h; subst; clear h.
    apply IHn in Heql; auto.

  - destruct (le_lt_dec x (b n)); inversion h; subst; clear h; auto.
Qed.

Definition increasing_le :
  forall a n m,
    n <= m
    -> increasing a
    -> a n <= a m.
Proof.
  induction m; introv lenm inc.

  - assert (n = 0) by omega; subst; auto.

  - destruct (le_lt_dec n m) as [d|d].

    + repeat (autodimp IHm hyp).
      pose proof (inc m) as q; destruct q; omega.

    + assert (n = S m) by omega; subst; auto.
Qed.

Definition least_greater_aux_prop2 :
  forall b a n x k,
    eq_upto x b a
    -> increasing a
    -> least_greater_aux b n (S (a x)) = Some k
    -> x <= k.
Proof.
  introv equ inca e.
  apply least_greater_aux_prop1 in e.
  destruct (le_lt_dec x k); auto.
  rewrite (equ k l) in e.
  pose proof (increasing_le a k x) as q; repeat (autodimp q hyp); try omega.
Qed.

Lemma implies_eq_upto_baire2cantor :
  forall (a b : baire) n,
    eq_upto n a b
    -> eq_upto n (baire2cantor a) (baire2cantor b).
Proof.
  introv h q.
  unfold baire2cantor.

  destruct m; simpl.

  { destruct (Nat.eq_dec (a 0) (a 0)); try omega.
    destruct (Nat.eq_dec (b 0) (b 0)); try omega.
    auto. }

  destruct (Nat.eq_dec (a m) (a (S m))) as [d1|d1];
    destruct (Nat.eq_dec (b m) (b (S m))) as [d2|d2];
    auto.

  - pose proof (h m) as h1; autodimp h1 hyp; try omega.
    pose proof (h (S m)) as h2; autodimp h2 hyp; try omega.

  - pose proof (h m) as h1; autodimp h1 hyp; try omega.
    pose proof (h (S m)) as h2; autodimp h2 hyp; try omega.
Qed.
Hint Resolve implies_eq_upto_baire2cantor : cont.

Definition baire_eq_from (a : baire) (k : nat) : baire :=
  fun n => if lt_dec n k then a n else a k.

Lemma increasing_baire_eq_from :
  forall (a : baire) n,
    increasing a
    ->  increasing (baire_eq_from a n).
Proof.
  introv inc; introv.
  unfold baire_eq_from.
  destruct (lt_dec (S n0) n); destruct (lt_dec n0 n); auto; try omega.
  assert (n = S n0) as xx by omega; subst; simpl in *; auto.
Qed.
Hint Resolve increasing_baire_eq_from : cont.

Definition baire_diff_from (a : baire) (k : nat) : baire :=
  fun n =>
    if le_lt_dec k n
    then (* k <= n *)
      if eq_nat_dec (a k) (a (pred k))
      then S (a (pred k))
      else a (pred k)
    else (* n < k *) a n.

Lemma eq_upto_baire_diff_from :
  forall n a, eq_upto n a (baire_diff_from a n).
Proof.
  introv h.
  unfold baire_diff_from.
  destruct (le_lt_dec n m); auto; try omega.
Qed.
Hint Resolve eq_upto_baire_diff_from : cont.

Lemma eq_upto0 :
  forall {T} (a b : Seq T), eq_upto 0 a b.
Proof.
  introv h; omega.
Qed.
Hint Resolve eq_upto0 : cont.

Lemma init0_implies_eq_upto1_zeros :
  forall (a : baire), init0 a -> eq_upto 1 a zeros.
Proof.
  introv init h.
  destruct m; try omega; auto.
Qed.
Hint Resolve init0_implies_eq_upto1_zeros : cont.

Lemma init0_zeros : init0 zeros.
Proof.
  compute; auto.
Qed.
Hint Resolve init0_zeros : cont.

Lemma increasing_zeros : increasing zeros.
Proof.
  compute; auto.
Qed.
Hint Resolve increasing_zeros : cont.

Definition change_from1 (a : baire) : cantor :=
  fun n => if eq_nat_dec n 0 then false else
             if eq_nat_dec (a 1) (a 0) then true
             else false.

Lemma init0_baire_diff_from :
  forall a n, 0 < n -> init0 a -> init0 (baire_diff_from a n).
Proof.
  introv lt0 init.
  unfold init0, baire_diff_from.
  destruct (le_lt_dec n 0); try omega; auto.
Qed.
Hint Resolve init0_baire_diff_from : cont.

Lemma increasing_baire_diff_from :
  forall a n, increasing a -> increasing (baire_diff_from a n).
Proof.
  introv cont; introv.
  unfold baire_diff_from.
  destruct (le_lt_dec n (S n0)) as [d1|d1];
    destruct (Nat.eq_dec (a n) (a (Init.Nat.pred n))) as [d2|d2];
    destruct (le_lt_dec n n0) as [d3|d3]; auto; try omega;
      assert (n = S n0) by omega; subst; simpl in *; auto.
Qed.
Hint Resolve increasing_baire_diff_from : cont.

Lemma baire_diff_from_diff :
  forall a n, a n <> baire_diff_from a n n.
Proof.
  introv h.
  unfold baire_diff_from in h.
  destruct (le_lt_dec n n) as [d|d]; try omega.
  clear d.
  destruct (Nat.eq_dec (a n) (a (Init.Nat.pred n))) as [d|d]; auto.
  omega.
Qed.

Lemma eq_upto_baire_eq_from :
  forall a p n,
    p <= n
    -> eq_upto p a (baire_eq_from a n).
Proof.
  introv lepn h.
  unfold baire_eq_from.
  destruct (lt_dec m n); auto; try omega.
Qed.
Hint Resolve eq_upto_baire_eq_from : cont.

Lemma init0_baire_eq_from :
  forall a n, init0 a -> init0 (baire_eq_from a n).
Proof.
  introv inti.
  unfold init0, baire_eq_from; simpl.
  destruct (lt_dec 0 n); auto.
  assert (n = 0) by omega; subst; auto.
Qed.
Hint Resolve init0_baire_eq_from : cont.

Definition baire_inc_from (a : baire) (n : nat) : baire :=
  fun k => if lt_dec k n then a k else (a n) + k - n.

Lemma eq_upto_baire_inc_from :
  forall (a : baire) (p : nat),
    eq_upto p a (baire_inc_from a p).
Proof.
  introv h.
  unfold baire_inc_from.
  destruct (lt_dec m p); auto; omega.
Qed.
Hint Resolve eq_upto_baire_inc_from : cont.

Lemma increasing_baire_inc_from :
  forall (a : baire) (p : nat),
    increasing a
    -> increasing (baire_inc_from a p).
Proof.
  introv inc; introv.
  unfold increasing, baire_inc_from.
  destruct (lt_dec (S n) p) as [d1|d1]; destruct (lt_dec n p) as [d2|d2]; auto; try omega.
  assert (p = S n) by omega; subst.
  rewrite Nat.add_sub; auto.
Qed.
Hint Resolve increasing_baire_inc_from : cont.

(* This is Kripke's lemma (a) in section 2 p.104 *)
Lemma kripke2a :
  continuity_seq_prop
  ->
  forall (a : baire) (m : nat),
    increasing a
    -> !!{n : nat | a(n) >= m}.
Proof.
  introv cont inv h.

  pose proof (cont (fun a => !{n : nat | a n >= m}) a) as q; simpl in q.
  autodimp q hyp.
  exrepnd.

  assert (a(p) < m) as lem.
  {
    destruct (lt_dec (a p) m); auto.
    destruct h; exists p; omega.
  }

  assert (forall (y : nat), y < p -> a y < m) as ltym.
  {
    introv z.
    pose proof (increasing_le a y p) as w; repeat (autodimp w hyp); try omega.
  }

  pose proof (q0 (baire_inc_from a p))  as z.
  repeat (autodimp z hyp); eauto 2 with cont.
  destruct z.
  exists (p + m - a p).
  unfold baire_inc_from.
  assert (a p + (p + m - a p) - p = m) as xx by omega; rewrite xx; clear xx.
  destruct (lt_dec (p + m - a p) p); auto; omega.
Qed.

(* This is meant to be only true for absolutely free choice sequences *)
Lemma kripke2a_concl_false :
  !forall (a : baire) (m : nat),
      increasing a
      -> !!{n : nat | a(n) >= m}.
Proof.
  introv h.
  pose proof (h zeros 1) as z; clear h.
  autodimp z hyp; eauto 2 with cont.
  unfold zeros in z.
  destruct z; intro z; exrepnd; omega.
Qed.

(* This is meant to be only true for absolutely free choice sequences *)
Lemma continuity_seq_prop_false :
  !continuity_seq_prop.
Proof.
  introv C.
  pose proof (C (fun a => forall n, a n = 0) zeros) as q; simpl in q.
  autodimp q hyp.
  exrepnd.
  pose proof (q0 (fun n => if lt_dec n p then 0 else 1)) as h; simpl in h; clear q0.
  autodimp h hyp.

  {
    introv ltn.
    unfold zeros.
    destruct (lt_dec m p); omega.
  }

  {
    pose proof (h p) as q; clear h.
    destruct (lt_dec p p); omega.
  }
Qed.

Lemma kripke2a_prop :
  continuity_seq_prop
  ->
  forall (a : baire) (m : nat),
    increasing a
    -> !!exists (n : nat), a(n) >= m.
Proof.
  introv cont inc h.
  pose proof (kripke2a cont a m inc) as q.
  destruct q; intro q; exrepnd.
  destruct h; exists n; auto.
Qed.

(* This is Kripke's lemma (b) in section 2 p.104 *)
Lemma kripke2b :
  continuity_seq_prop
  ->
  uniform_continuity
  ->
  forall (a : baire),
    init0 a
    -> increasing a
    -> !forall (m : nat), {n : nat | a(n) >= m}.
Proof.
  introv pcont ucont init inc.
  introv h.

  pose proof (pcont (fun a => forall m : nat, Cast {n : nat | a n >= m}) a) as q.
  simpl in q.
  autodimp q hyp.
  exrepnd.

  assert (forall (b : baire), eq_upto p a b -> forall (m : nat), {n : nat | b n >= m}) as w.
  {
    introv equ; introv.
    pose proof (q0 b equ m) as z.
    apply (constructive_indefinite_ground_description nat (fun n => n) (fun n => n)); auto.
    { introv; apply ge_dec. }
    inversion z; exrepnd; eexists; eauto.
  }

  clear q0.

  assert (forall (b : baire), eq_upto p a b -> {n : nat | b(n) >= S (a p)}) as z.
  {
    introv equ.
    apply w; auto.
  }

  clear w.

  remember (fun (b : cantor) =>
              match eq_upto_dec p a (cantor2baire b) with
              | left q => least_greater
                            (cantor2baire b)
                            (proj1_sig (z (cantor2baire b) q))
                            (S (a p))
              | right _ => 0
              end) as c.

  pose proof (ucont c) as q; exrepnd.
  rename q0 into q.

  assert (p <= n) as lepn.
  {
    (* change a starting at n *)
    destruct (le_lt_dec p n) as [ltnp|ltnp]; auto.
    assert False as xx;[|destruct xx];[].

    destruct (eq_nat_dec n 0) as [ez|ez].

    {
      subst n.

      destruct (eq_nat_dec p 1) as [po|po].

      - subst p.
        pose proof (z zeros) as w.
        repeat (autodimp w hyp); eauto 3 with cont.
        exrepnd.
        compute in w0; omega.

      - pose proof (q (baire2cantor a) (change_from1 a)) as w.
        autodimp w hyp; eauto 2 with cont.
        clear q.
        subst c.
        destruct (eq_upto_dec p a (cantor2baire (baire2cantor a))) as [d1|d1];
          [|destruct d1; rewrite baire2cantor2baire; eauto 2 with cont];[].
        destruct (eq_upto_dec p a (cantor2baire (change_from1 a))) as [d2|d2].

        { pose proof (d2 1) as xx; autodimp xx hyp; try omega.
          unfold change_from1, cantor2baire in xx; simpl in xx.
          destruct (Nat.eq_dec (a 1) (a 0)) as [d|d]; auto;
            rewrite xx in d; rewrite init in d; omega. }

        match type of w with
        | context[proj1_sig ?a] => remember a as xx; exrepnd; simpl in *
        end.
        clear Heqxx.

        rewrite baire2cantor2baire in *; auto;[].
        unfold least_greater in w.
        remember (least_greater_aux a n (S (a p))) as lg; destruct lg; symmetry in Heqlg; subst;
          [|rewrite init in xx0; omega].

        pose proof (least_greater_aux_prop2 a a n p 0) as zz.
        repeat (autodimp zz hyp); omega.
    }

    assert (0 < n) as gz by omega; clear ez.

    pose proof (q (baire2cantor a)
                  (baire2cantor (baire_diff_from a n))) as w.
    autodimp w hyp; eauto with cont; eauto with cont;[].

    clear q; subst c.

    repeat match type of w with
           | context[eq_upto_dec ?a ?b ?c] =>
             let d := fresh "d" in
             destruct (eq_upto_dec a b c) as [d|d]
           end;
      repeat match type of w with
             | context[proj1_sig ?a] =>
               let q := fresh "q" in
               remember a as q; exrepnd; simpl in *;
                 match goal with
                 | [ H : _ = a |- _ ] => clear H
                 end
             end;
      try (complete (destruct d; rewrite baire2cantor2baire in *; eauto 2 with cont));
      repeat (rewrite baire2cantor2baire in *; eauto 3 with cont);[|].

    - pose proof (d0 n) as xx; autodimp xx hyp.
      apply baire_diff_from_diff in xx; auto.

    - unfold least_greater in w.
      remember (least_greater_aux a n0 (S (a p))) as lg; destruct lg; symmetry in Heqlg; subst;
        [|rewrite init in q0; omega].

      pose proof (least_greater_aux_prop2 a a n0 p 0) as zz.
      repeat (autodimp zz hyp); omega.
  }

  pose proof (z (baire_eq_from a p)) as xx.
  repeat (autodimp xx hyp); eauto 3 with cont.
  exrepnd.

  unfold baire_eq_from in xx0.
  destruct (lt_dec n0 p) as [d|d]; try omega.

  pose proof (increasing_le a n0 p) as zz.
  repeat (autodimp zz hyp); try omega.
Qed.

Lemma kripke2b_prop :
  continuity_seq_prop
  ->
  uniform_continuity
  ->
  forall (a : baire),
    init0 a
    -> increasing a
    -> !forall (m : nat), exists (n : nat), a(n) >= m.
Proof.
  introv cont ucont init inc; intro h.
  pose proof (kripke2b cont ucont a init inc) as q.
  destruct q; introv.
  pose proof (h m) as w; clear h.

  apply (constructive_indefinite_ground_description nat (fun n => n) (fun n => n)); auto.
  introv; apply ge_dec.
Qed.

Definition kuroda :=
  forall (A : nat -> Prop),
    (forall (m : nat), !!(A m)) -> (!!forall (m : nat), A m).

Definition markov :=
  forall (A : nat -> Prop),
    (forall m, A m \/ !A m)
    -> (!!exists (n : nat), A n)
    -> exists (n : nat), A n.

(* For this we don't actually need kripke2b
   and we only need kripke2a on the zero sequence
   --- This is because we're cheating:
       zero is not an absolutely free choice sequence

   Which means that we've cheated above in the proofs of kripke2a and kripke2b
   because I probably used many non-absolutely free choice sequences
 *)
Lemma continuity_contradicts_kuroda :
  continuity_seq_prop
  -> !kuroda.
Proof.
  introv cont K.

  pose proof (K (fun m => exists (n : nat), zeros n >= m)) as q; simpl in q.
  autodimp q hyp.

  {
    introv.
    apply kripke2a_prop; eauto 2 with cont.
  }

  {
    destruct q; intro h.
    pose proof (h 1) as z; clear h.
    exrepnd.
    unfold zeros in z0.
    omega.
  }
Qed.
