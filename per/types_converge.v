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

Require Export per_props_compute.

Lemma types_converge {o} :
  forall lib (t : @CTerm o), type lib t -> chaltsc lib t.
Proof.
  introv n.
  unfold type, tequality, nuprl in n; exrepnd.
  induction n0
    as [ h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h ];
    allunfold_per; uncast; allapply @computes_to_valc_implies_hasvaluec;
    try (complete (spcast; auto)).
  inversion h as [i u].
  rw @univi_exists_iff in u; exrepnd.
  spcast.
  apply computes_to_valc_implies_hasvaluec in u2; auto.
Qed.
