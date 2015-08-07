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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export cequiv_props.

Lemma isprog_vars_pi1 {p} :
  forall vs (t : @NTerm p), isprog_vars vs t -> isprog_vars vs (mk_pi1 t).
Proof.
  introv ip.
  apply isprog_vars_spread; eauto 3 with slow.
Qed.

Lemma isprog_vars_pi2 {p} :
  forall vs (t : @NTerm p), isprog_vars vs t -> isprog_vars vs (mk_pi2 t).
Proof.
  introv ip.
  apply isprog_vars_spread; eauto 3 with slow.
Qed.

Definition mkc_pi1 {o} (t : @CTerm o) : CTerm :=
  let (x,p) := t in
  exist isprog (mk_pi1 x) (isprog_pi1 x p).

Definition mkc_pi2 {o} (t : @CTerm o) : CTerm :=
  let (x,p) := t in
  exist isprog (mk_pi2 x) (isprog_pi2 x p).

Definition mkcv_pi1 {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  let (x,p) := t in
  exist (isprog_vars vs) (mk_pi1 x) (isprog_vars_pi1 vs x p).

Definition mkcv_pi2 {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  let (x,p) := t in
  exist (isprog_vars vs) (mk_pi2 x) (isprog_vars_pi2 vs x p).
