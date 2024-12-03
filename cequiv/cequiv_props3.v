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

Require Export cequiv_props2.


Lemma implies_cequivc_mkc_spread1 {o} :
  forall lib (t1 t2 : @CTerm o) a b u,
    cequivc lib t1 t2
    -> cequivc lib (mkc_spread t1 a b u) (mkc_spread t2 a b u).
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  destruct ceq.
  split; repeat prove_approx; eauto 3 with slow;
  apply approx_congruence_sub; simpl; fold_terms;
  try (apply isprogram_spread_iff2; dands; eauto 3 with slow).

  - split; simpl; auto.
    introv j; repeat (destruct n; try lia); unfold selectbt; simpl; eauto 3 with slow.

    + apply blift_sub_nobnd_congr; apply approx_implies_approx_open; auto.

    + unfold blift_sub; exists [a,b] x1 x1; dands; eauto 3 with slow.
      left; dands; eauto 3 with slow.
      intro xxx; ginv.

  - split; simpl; auto.
    introv j; repeat (destruct n; try lia); unfold selectbt; simpl; eauto 3 with slow.

    + apply blift_sub_nobnd_congr; apply approx_implies_approx_open; auto.

    + unfold blift_sub; exists [a,b] x1 x1; dands; eauto 3 with slow.
      left; dands; eauto 3 with slow.
      intro xxx; ginv.
Qed.

Lemma cequivc_mkc_spread_mkc_pair {o} :
  forall lib (a b : @CTerm o) u v t,
    cequivc
      lib
      (mkc_spread (mkc_pair a b) u v t)
      (lsubstc2 u a v b t).
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms.
  unfold reduces_toc; simpl.
  apply reduces_to_if_step; auto.
Qed.
