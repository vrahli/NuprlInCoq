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

Require Export Coq.Logic.ConstructiveEpsilon.
Require Export per_props_nat.
Require Export continuity_defs_ceq.


Definition equality_of_nat_tt {o} lib (n m : @CTerm o) :=
  {k : nat & computes_to_valc lib n (mkc_nat k)
           # computes_to_valc lib m (mkc_nat k)}.

Definition equality_of_nat2 {p} lib (t1 t2 : @CTerm p) :=
  {j : nat
   , {n : nat
   , reduces_kstepsc lib t1 (mkc_nat n) j
   # reduces_kstepsc lib t2 (mkc_nat n) j}}.

Lemma equality_of_nat_implies_nat2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2 -> equality_of_nat2 lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
  exists (Peano.max k1 k0); exists k; dands; spcast.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e4]; auto;
    apply Nat.le_max_r; auto.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e2]; auto;
    apply Nat.le_max_l; auto.
Qed.

Lemma equality_of_nat2_implies_nat {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat2 lib t1 t2 -> equality_of_nat lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat2 in e; exrepnd; spcast.
  exists n; dands; spcast;
  apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
  dands; eauto 3 with slow.
Qed.

Lemma dec_reduces_kstepsc {o} :
  forall lib k (t v : @CTerm o),
    (forall x, decidable (x = get_cterm v))
    -> decidable (reduces_kstepsc lib t v k).
Proof.
  introv d.
  destruct_cterms; allsimpl.
  pose proof (dec_reduces_in_atmost_k_steps lib k x0 x d) as h.
  destruct h as [h|h];[left|right].
  - spcast; tcsp.
  - intro r; spcast; tcsp.
Qed.

Lemma equality_of_nat_imp_tt {o} :
  forall lib (n m : @CTerm o),
    equality_of_nat lib n m
    -> equality_of_nat_tt lib n m.
Proof.
  introv e.
  unfold equality_of_nat_tt.
  apply equality_of_nat_implies_nat2 in e.
  unfold equality_of_nat2 in e.
  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in e; auto.

  - exrepnd.
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in e0; auto.

    + exrepnd.
      exists x0; dands; auto;
      apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
      dands; eauto 3 with slow; exists x; spcast; auto.

    + clear e0.
      introv.
      pose proof (dec_reduces_kstepsc lib x n (mkc_nat x0)) as h; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      pose proof (dec_reduces_kstepsc lib x m (mkc_nat x0)) as q; allsimpl.
      autodimp q hyp; eauto 3 with slow.
      destruct h as [h|h]; destruct q as [q|q]; tcsp;
      try (complete (right; intro r; repnd; tcsp)).

  - clear e.
    introv.
    remember (compute_at_most_k_steps lib x (get_cterm n)) as c1; symmetry in Heqc1.
    remember (compute_at_most_k_steps lib x (get_cterm m)) as c2; symmetry in Heqc2.
    destruct c1, c2.

    + destruct (decidable_ex_mk_nat n0) as [h|h]; exrepnd.

      * rw h0 in Heqc1; clear h0.
        destruct (decidable_ex_mk_nat n1) as [q|q]; exrepnd.

        { rw q0 in Heqc2; clear q0.
          destruct (deq_nat n2 n3) as [d|d].

          - subst.
            left; exists n3; dands; spcast; auto.

          - right; intro r; exrepnd; spcast.
            allunfold @reduces_in_atmost_k_stepsc; allsimpl.
            allunfold @reduces_in_atmost_k_steps.
            rw Heqc1 in r1.
            rw Heqc2 in r0.
            inversion r1 as [c1].
            inversion r0 as [c2].
            allapply Znat.Nat2Z.inj; subst; tcsp.
        }

        { right; intro r; exrepnd; spcast.
          allunfold @reduces_in_atmost_k_stepsc; allsimpl.
          allunfold @reduces_in_atmost_k_steps.
          rw Heqc1 in r1.
          rw Heqc2 in r0.
          inversion r1 as [c1].
          inversion r0 as [c2].
          allapply Znat.Nat2Z.inj; subst; tcsp.
          destruct q; exists n3; auto.
        }

      * right; intro r; exrepnd; spcast.
        allunfold @reduces_in_atmost_k_stepsc; allsimpl.
        allunfold @reduces_in_atmost_k_steps.
        rw Heqc1 in r1.
        rw Heqc2 in r0.
        inversion r1 as [c1].
        inversion r0 as [c2].
        allapply Znat.Nat2Z.inj; subst; tcsp.
        destruct h; exists n2; auto.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.
Qed.

Lemma equality_in_tnat_nat {o} :
  forall (lib : @library o) n, equality lib (mkc_nat n) (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat; unfold equality_of_nat; exists n.
  dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.
Hint Resolve equality_in_tnat_nat : slow.
