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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.

Hint Resolve iscvalue_mkc_admiss : slow.

Lemma type_mkc_admiss {o} :
  forall lib (A : @CTerm o), type lib (mkc_admiss A) <=> type lib A.
Proof.
  introv; split; intro h.

  - unfold type in h; exrepnd.
    inversion h0; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; eauto 3 with slow.

  - unfold type in h; exrepnd.
    exists (per_admiss_eq eq).
    apply CL_admiss.
    exists A eq; dands; spcast; eauto 3 with slow.
Qed.

Definition cofinite_subst_fapprox {o}
           lib
           (T : @CTerm o)
           {v : NVar}
           (e e' : CVTerm [v])
           (f : @CTerm o) :=
    {j : nat
     , forall (k :nat),
         k>j -> equality lib (subst_fapproxc e f k) (subst_fapproxc e' f k) T}.

Definition subst_fix {o}
           lib
           (T : @CTerm o)
           {v : NVar}
           (e e' : CVTerm [v])
           (f : @CTerm o) :=
  equality lib (subst_fixc e f) (subst_fixc e' f) T.

Definition has_admissible_equality {o} lib (T : @CTerm o) :=
  forall v (e e' : CVTerm [v]) (f : @CTerm o),
    cofinite_subst_fapprox lib T e e' f
    -> subst_fix lib T e e' f.

Lemma admissible_equality_iff_has_admissible_equality {o} :
  forall lib (A : @CTerm o) eq,
    nuprl lib A eq
    -> (admissible_equality eq <=> has_admissible_equality lib A).
Proof.
  introv n; split; introv h w.

  - unfold subst_fix.
    unfold cofinite_subst_fapprox in w; exrepnd.
    eapply eq_equality0;[|eauto].
    apply h.
    unfold cofinite_subst_fapprox_eqc.
    exists j.
    introv gtk.
    apply w0 in gtk.
    eapply equality_implies_eq; eauto.

  - unfold subst_fix_eqc.
    unfold cofinite_subst_fapprox_eqc in w; exrepnd.
    eapply equality_implies_eq;[eauto|].
    apply h.
    unfold cofinite_subst_fapprox.
    exists j.
    introv gtk.
    apply w0 in gtk.
    eapply eq_equality0;eauto.
Qed.

Lemma equality_in_mkc_admiss_iff_has_admissible_equality {o} :
  forall lib (t u A : @CTerm o),
    equality lib t u (mkc_admiss A) <=> (has_admissible_equality lib A # type lib A).
Proof.
  introv; split; intro h.

  - unfold equality in h; exrepnd.
    inversion h1; subst; try not_univ.
    match goal with
    | [ H : per_admiss _ _ _ _ |- _ ] => rename H into q
    end.
    allunfold @per_admiss; exrepnd.
    computes_to_value_isvalue.
    fold (nuprl lib) in *.
    apply q1 in h0; unfold per_admiss_eq in h0.
    dands; eauto 3 with slow.
    eapply admissible_equality_iff_has_admissible_equality; eauto.

  - repnd.
    unfold type in h; exrepnd.
    exists (per_admiss_eq eq); dands; auto.
    { apply CL_admiss.
      exists A eq; dands; spcast; eauto 3 with slow. }
    unfold per_admiss_eq.
    eapply admissible_equality_iff_has_admissible_equality; eauto.
Qed.

Lemma tequality_admiss {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_admiss A1) (mkc_admiss A2)
    <=> (type lib A1
         # type lib A2
         # (has_admissible_equality lib A1 <=> has_admissible_equality lib A2)).
Proof.
  introv.
  rw @tequality_iff_ext_eq.
  allrw @type_mkc_admiss.

  split; intro h; repnd; dands; auto.

  - pose proof (h mkc_axiom mkc_axiom) as q; clear h.
    repeat (rw @equality_in_mkc_admiss_iff_has_admissible_equality in q).
    split; intro w; destruct q as [q1 q2];[autodimp q1 hyp|autodimp q2 hyp];tcsp.

  - introv.
    repeat (rw @equality_in_mkc_admiss_iff_has_admissible_equality).
    split; intro w; repnd; destruct h as [q1 q2];[autodimp q1 hyp|autodimp q2 hyp];tcsp.
Qed.
