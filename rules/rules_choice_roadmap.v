(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


(* Contains a proof of a squashed version of LS1 as well as a proof that
   all choice sequences of numbers are in the baire space: *)
Require Export rules_choice1.

(* Contains a proof of intensional LS2: *)
Require Export rules_choice2.

(* Similar to the proof that all choice sequences of numbers are in the baire space,
   we've proved: ∀ (a ∈ Free) (n ∈ ℕ). ∃ (x:ℕ). a(n) = x ∈ ℕ *)
Require Export rules_choice3.

(* Contains a proof of a non-squashed version of LS1 *)
(* === disabled for now because swapping does not preserve generating new choice sequence names === *)
(*Require Export rules_choice4.*)

(* Contains a proof of the validity of the extensional version of LS2 *)
Require Export rules_choice5.

(* A proof of a simple version of LS3 *)
Require Export rules_ls3.
