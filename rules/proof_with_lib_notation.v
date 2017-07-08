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
Notation "𝔸( name , t1 , t2 )" := (oterm (Abs {| opabs_name := name; opabs_params := []; opabs_sign := [0, 0] |}) [ bterm [] t1, bterm [] t2]).
Notation " ( a ≡ b ∈ T ) " := (oterm  (Can NEquality) [ bterm [] a, bterm [] b, bterm [] T]) (at level 0).
Notation "⋂ v : T . U" := (oterm (Can NIsect) [ bterm [] T, bterm [nvar v] U ]) (at level 0).
Notation " ( a ≣ b ∈ T ) " := (soterm (Can NEquality) [ sobterm [] a, sobterm [] b, sobterm [] T ]).
Notation "★" := (oterm (Can NAxiom) []).
Notation "𝔸( name , v1 , v2 ) ≜ t" := (lib_abs {| opabs_name := name; opabs_params := []; opabs_sign := [0, 0] |} [ (nvar v1, 0), (nvar v2, 0) ] t _) (at level 0).
Notation "⎧ v ∷ t ⎫" := {| hvar := nvar v; hidden := false; htyp := t; lvl := nolvl |}.
Notation "⎡ v ∷ t ⎤" := {| hvar := nvar v; hidden := true; htyp := t; lvl := nolvl |}.
Notation "( a ≈ b )" := (oterm (Can NCequiv) [ bterm [] a, bterm [] b]).
Notation "LibraryEntry_proof( name , stmt , exp )" := (LibraryEntry_proof _ name stmt exp _ _ _).
Notation "CUT( B , C , t , u , x , H , prf1 , prf2 )" := (proof_cut _ B C t u x H _ _ _ prf1 prf2).
Notation "'ℤ'" := (oterm (Can NInt) []).
