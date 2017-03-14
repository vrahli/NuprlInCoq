(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017x Cornell University

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


Require Export per_props_equality.


(* This is not true anymore *)
Lemma tequality_in_uni_iff_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality
      lib
      (mkc_member T1 (mkc_uni i))
      (mkc_member T2 (mkc_uni i))
    <=> equorsq lib T1 T2 (mkc_uni i).
Proof.
  introv.
  allrw <- @fold_mkc_member.
  rw @tequality_mkc_equality.
  split; intro k; repnd; dands; tcsp; eauto 3 with slow.

  -


    apply tequality_mkc_uni.
  split; intro e.
  generalize (cequorsq_equality_trans2 lib T1 T1 T2 (mkc_uni i)); intro e1.
  repeat (dest_imp e1 hyp).
  apply equality_sym in e1.
  apply equality_refl in e1; sp.
  generalize (cequorsq_equality_trans1 lib T1 T2 T2 (mkc_uni i)); intro e1.
  repeat (dest_imp e1 hyp).
  apply equality_refl in e1; sp.
Qed.