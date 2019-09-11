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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export cvterm2.


Lemma isprog_vars_vbot {o} :
  forall vs v, @isprog_vars o vs (mk_vbot v).
Proof.
  introv.
  apply isprog_vars_fix.
  apply isprog_vars_lam; auto.
  apply isprog_vars_var_if; simpl; auto.
Qed.
Hint Resolve isprog_vars_vbot : slow.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)