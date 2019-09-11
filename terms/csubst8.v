(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export csubst6.
Require Export cvterm4.


Lemma substc2_inteq {o} :
  forall v x (w : @CTerm o) (a b c d : CVTerm [v,x]),
    substc2 v w x (mkcv_inteq [v,x] a b c d)
    = mkcv_inteq
        [v]
        (substc2 v w x a)
        (substc2 v w x b)
        (substc2 v w x c)
        (substc2 v w x d).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_inteq : slow.

Hint Rewrite @substc2_apply : slow.
Hint Rewrite @mkcv_inteq_substc : slow.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
