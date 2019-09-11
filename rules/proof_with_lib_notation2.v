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


Require Export proof_with_lib.


Notation "𝕌( i )" := (oterm (Can (NUni i)) []).
Notation "𝕍( v )" := (vterm (nvar v)) (at level 0).
Notation "𝕎( v )" := (sovar (nvar v) []) (at level 0).
Notation "★" := (oterm (Can NAxiom) []).
Notation "LibraryEntry_proof( name , stmt , exp )" := (RigidLibraryEntry_proof _ name stmt exp _ _ _).
Notation "'ℤ'" := (oterm (Can NInt) []).
