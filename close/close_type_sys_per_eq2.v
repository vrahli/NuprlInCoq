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


Require Export type_sys.



Lemma defines_only_universes_eq_L :
  forall ts : candidate-type-system,
  forall T T1 T2 eq1 eq2,
    type_system ts
    -> defines_only_universes ts
    -> ts T T2 eq2
    -> per_eq (close ts) T T1 eq1
    -> False.
Proof.
  intros.
  allunfold defines_only_universes.
  assert (ts T T eq2) by (apply type_system_type_mem with (T' := T2); allunfold type_system; sp).
  apply_in_hyp p; close_diff.
Qed.

Lemma defines_only_universes_eq_LR :
  forall ts : candidate-type-system,
  forall T T1 T2 eq1 eq2,
    type_system ts
    -> defines_only_universes ts
    -> ts T2 T eq2
    -> per_eq (close ts) T T1 eq1
    -> False.
Proof.
  intros.
  allunfold defines_only_universes.
  assert (ts T T eq2) by (apply type_system_type_mem with (T' := T2); allunfold type_system; sp).
  apply_in_hyp p; close_diff.
Qed.

Lemma defines_only_universes_eq_R :
  forall ts : candidate-type-system,
  forall T T1 T2 eq1 eq2,
    type_system ts
    -> defines_only_universes ts
    -> ts T T2 eq2
    -> per_eq (close ts) T1 T eq1
    -> False.
Proof.
  intros.
  allunfold defines_only_universes.
  assert (ts T T eq2) by (apply type_system_type_mem with (T' := T2); allunfold type_system; sp).
  apply_in_hyp p; close_diff.
Qed.

Lemma defines_only_universes_eq_RR :
  forall ts : candidate-type-system,
  forall T T1 T2 eq1 eq2,
    type_system ts
    -> defines_only_universes ts
    -> ts T2 T eq2
    -> per_eq (close ts) T1 T eq1
    -> False.
Proof.
  intros.
  allunfold defines_only_universes.
  assert (ts T T eq2) by (apply type_system_type_mem with (T' := T2); allunfold type_system; sp).
  apply_in_hyp p; close_diff.
Qed.


Lemma close_type_system_eq :
  forall ts : candidate-type-system,
    type_system ts
    -> is_type_system (per_eq ts).
Proof.
  introv tysys.
  unfold is_type_system; introv pereq.
  unfold per_eq in pereq; exrepnd.
  unfold type_system_props; dands.

  - unfold uniquely_valued_body.
    introv pereq'.
    allunfold per_eq; exrepnd.
    spcast; repeat computes_to_eqval.
    unfold eq_term_equals; introv.
    rw pereq0.
    rw pereq'0.
    onedts uv tye tys tyt tyvr tes tet tevr.
    generalize (uv A B eqa eqa0); intro k; repeat (dest_imp k hyp).
    rw k; sp.

  - unfold type_extensionality_body; introv teq.
    unfold per_eq.
    exists A B a1 a2 b1 b2 eqa; sp.
    rw <- teq.
    rw pereq0; sp.

  - unfold type_symmetric_body; introv.
    unfold per_eq.

    generalize (type_system_ts_refl ts A B eqa); introv r;
    repeat (dest_imp r hyp); repnd.

    assert (term_equality_symmetric eqa)
      as eqs
        by (onedts uv tye tys tyt tyvr tes tet tevr; apply (tes A B eqa); sp).

    assert (term_equality_transitive eqa)
      as eqt
        by (onedts uv tye tys tyt tyvr tes tet tevr; apply (tet A B eqa); sp).

    assert (term_equality_respecting eqa)
      as eqc
        by (onedts uv tye tys tyt tyvr tes tet tevr; apply (tevr A eqa); sp).

    exists B A b1 b2 a1 a2 eqa; sp.
    onedts uv tye tys tyt tyvr tes tet tevr.
    generalize (tys A B eqa); intro k; dest_imp k hyp.
    apply eqorsq_sym; sp.
    apply eqorsq_sym; sp.
    rw pereq0; split; sp.

    apply eqorsq_commutes with (a := a1) (c := a2); sp.

    apply eqorsq_commutes with (a := b1) (c := b2); sp;
    apply eqorsq_sym; sp.

  - unfold type_transitive_body; introv pereq.
    unfold per_eq in pereq; exrepnd.
    spcast; repeat computes_to_eqval.
    unfold per_eq.

    assert (eq_term_equals eqa eqa0)
      as eqt
        by (apply uniquely_valued_eq2_ts with (ts := ts) (T := B) (T1 := A) (T2 := B0); sp).

    exists A B0 a1 a2 b0 b3 eqa; sp.

Qed.
