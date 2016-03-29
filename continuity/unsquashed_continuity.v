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

(* Escardo's proof *)
Lemma continuity_false :
  (forall (F : baire -> nat) (f : baire),
      {n : nat & forall g : baire, eq_upto n f g -> F f = F g})
  -> False.
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

Axiom FunctionalChoice_on :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall a : A, exists (b : B), R a b)
    -> (exists (f : A -> B), forall a : A, R a (f a)).

Lemma continuity_false_prop :
  (forall (F : baire -> nat) (f : baire),
      exists n, forall g : baire, eq_upto n f g -> F f = F g)
  -> False.
Proof.
  introv h.
  assert (forall (f : baire) (F : baire -> nat),
             exists n, forall g : baire, eq_upto n f g -> F f = F g) as q by auto.
  clear h.
  pose proof (q zeros) as h.
  clear q.

  apply FunctionalChoice_on in h; exrepnd.
  rename f into M.

  remember (M (fun a => 0)) as m.

  remember (fun b => M (fun a => b (a m))) as f.

  assert (f zeros = m) as h1.
  { subst; auto. }

  assert (forall (b : baire), eq_upto (M f) zeros b -> m = f b) as h2.
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

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
