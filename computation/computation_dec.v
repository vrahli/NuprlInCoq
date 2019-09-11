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


Require Export terms5.
Require Export computation7.
Require Export computation_exc.
Require Export computation_dec1.


Lemma decidable_isprog {o} :
  forall (t : @NTerm o),
    decidable (isprog t).
Proof.
  introv.
  apply decidable_eq_bool.
Qed.

Lemma decidable_isprogram {o} :
  forall (t : @NTerm o),
    decidable (isprogram t).
Proof.
  introv.
  destruct (decidable_isprog t) as [d|d];[left|right]; eauto 3 with slow.
  intro xx; destruct d; eauto 3 with slow.
Qed.

Lemma decidable_wf_term {o} :
  forall (t : @NTerm o),
    decidable (wf_term t).
Proof.
  introv.
  apply decidable_eq_bool.
Qed.

Lemma decidable_isvalue {o} :
  forall (t : @NTerm o),
    decidable (isvalue t).
Proof.
  introv.
  destruct t as [v|op bs]; try (complete (right; allsimpl; intro xx; inversion xx)).
  dopid op as [c|nc|e|a] Case; try (complete (right; allsimpl; intro xx; inversion xx)).
  destruct (decidable_isprogram (oterm (Can c) bs)) as [d|d];[left|right]; auto.
  introv xx; destruct d.
  inversion xx; auto.
Qed.

Lemma decidable_iscvalue {o} :
  forall (t : @CTerm o),
    decidable (iscvalue t).
Proof.
  introv.
  destruct_cterms.
  unfold iscvalue; simpl.
  apply decidable_isvalue.
Qed.
