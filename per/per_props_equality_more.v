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



(*Require Export per_props_more.*)
Require Export per_props_equality.
Require Export per_props_uni.

Lemma tequality_in_uni_iff {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    <=> (member lib T1 (mkc_uni i) <=> member lib T2 (mkc_uni i))
         # (member lib T1 (mkc_uni i) -> equality lib T1 T2 (mkc_uni i)).
Proof.
  introv; rw (@tequality_mkc_member p); split; intro; repnd; sp.
  apply tequality_mkc_uni.
Qed.

Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    -> (member lib T1 (mkc_uni i) <=> member lib T2 (mkc_uni i))
         # (member lib T1 (mkc_uni i) -> tequality lib T1 T2).
Proof.
  intros.
  dup H as H1; rw (@tequality_mkc_member p) in H1; repnd; split; sp.
  apply tequality_in_uni_implies_tequality in H; auto. 
Qed.

(*
Lemma tequality_in_uni_iff_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    <=> (member lib T1 (mkc_uni i) <=> member lib T2 (mkc_uni i))
         # (member lib T1 (mkc_uni i) -> tequality lib T1 T2).
Proof.
  introv; split; intro. 
  - apply tequality_in_uni_implies_tequality; auto.
  -  sp.   rw (@tequality_mkc_member p).
  split; try (apply tequality_mkc_uni); sp.
  dup H1 as H2; apply H0 in H2; clear H0.
  need the lemma Vincent is proving 
  
Qed.
*)
