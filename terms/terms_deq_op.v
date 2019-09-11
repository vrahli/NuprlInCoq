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

  Authors: Vincent Rahli

 *)


Require Export terms.


Lemma canonical_dec_op {o} :
  forall (x y : @CanonicalOp o), option (x = y).
Proof.
  introv.
  destruct x; destruct y; try (complete (left; reflexivity));
    match goal with
    | [ |- option (?x _ = ?x _) ] => idtac
    | _ => exact None
    end.

  - destruct (can_inj_deq c c0) as [d|d]; subst;[left|right];auto.

  - destruct (Z.eq_dec z z0) as [d|d]; subst;[left|right];auto.

  - right; auto.

  - destruct (choice_sequence_name_deq c c0) as [d|d]; subst; tcsp.

  - destruct (String.string_dec s s0) as [d|d]; subst;[left|right]; auto.

  - assert (Deq (get_patom_set o)) as d by (destruct o; destruct patom; auto).
    pose proof (d g g0) as h; dorn h;subst;[left|right]; auto.

  - destruct (deq_nat n n0) as [d|d]; subst; [left|right]; auto.

  - right; auto.

  - right; auto.
Defined.

Lemma opid_dec_op {o} :
  forall (x y : @Opid o), option (x = y).
Proof.
  introv.
  dopid x as [can1|ncan1|exc1|abs1] Case;
    dopid y as [can2|ncan2|exc2|abs2] SCase.

  - Case "Can"; SCase "Can".
    pose proof (canonical_dec_op can1 can2) as h; destruct h as [h|h]; subst;
      try (complete (left; auto)).
    right; auto.

  - Case "Can"; SCase "NCan".
    right; auto.

  - Case "Can"; SCase "Exc".
    right; auto.

  - Case "Can"; SCase "Abs".
    right; auto.

  - Case "NCan"; SCase "Can".
    right; auto.

  - destruct ncan1; destruct ncan2; try (complete (left; auto));
      match goal with
      | [ |- option (NCan (?x _) = NCan (?x _)) ] => idtac
      | _ => exact None
      end.

    + try destruct c; try destruct c0; try (complete (left; auto)); right; auto.
    + try destruct a; try destruct a0; try (complete (left; auto)); right; auto.
    + try destruct c; try destruct c0; try (complete (left; auto)); right; auto.

  - Case "NCan"; SCase "Exc".
    right; auto.

  - Case "NCan"; SCase "Abs".
    right; auto.

  - Case "Exc"; SCase "Can".
    right; auto.

  - Case "Exc"; SCase "NCan".
    right; auto.

  - Case "Exc"; SCase "Exc".
    left; auto.

  - Case "Exc"; SCase "Abs".
    right; auto.

  - Case "Abs"; SCase "Can".
    right; auto.

  - Case "Abs"; SCase "NCan".
    right; auto.

  - Case "Abs"; SCase "Exc".
    right; auto.

  - destruct abs1, abs2.
    pose proof (String.string_dec opabs_name opabs_name0) as h.
    dorn h; subst;[|right].
    pose proof (parameters_dec opabs_params opabs_params0) as h.
    dorn h; subst;[|right].
    pose proof (opsign_dec opabs_sign opabs_sign0) as h.
    dorn h; subst;[|right].
    left; auto.
Defined.

Lemma term_dec_op {o} :
  forall (x y : @NTerm o), option (x = y).
Proof.
  sp_nterm_ind1 x as [v1|f1|op1 bs1 ind] Case; introv.

  - Case "vterm".
    destruct y as [v2|f1|op bs2];[|exact None|exact None].
    destruct (deq_nvar v1 v2); subst;[|exact None].
    left; reflexivity.

  - Case "sterm".
    right.

  - Case "oterm".
    destruct y as [v2|f2|op2 bs2];[right|right|].
    destruct (opid_dec_op op1 op2); subst;[|right].

    assert (option (bs1 = bs2)) as opbs.
    {
      revert bs2.
      induction bs1; introv.
      - destruct bs2;[left|right]; auto.
      - destruct bs2;[right|].
        destruct a as [l1 t1], b as [l2 t2].
        simpl in *.
        autodimp IHbs1 hyp.
        { introv i; introv; eapply ind; eauto. }
        pose proof (ind t1 l1) as q; autodimp q hyp; clear ind.
        pose proof (q t2) as h; clear q.
        destruct (list_eq_dec deq_nvar l1 l2) as [d|d]; subst;[|right].
        destruct h as [d|d]; subst;[|right].
        destruct (IHbs1 bs2) as [d|d]; subst;[|right].
        left; auto.
    }

    destruct opbs as [d|d]; subst;[left|right];auto.
Defined.
