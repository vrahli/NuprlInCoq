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


Require Export substitution3.


Tactic Notation "unfsubst" "in" ident(H) :=
  rewrite @cl_subst_subst_aux in H;
  eauto 3 with slow;
  unfold subst_aux in H.

Tactic Notation "unfsubst" constr(t) "in" ident(H) :=
  rewrite (cl_subst_subst_aux t) in H;
  eauto 3 with slow;
  unfold subst_aux in H.

Tactic Notation "unfsubst" :=
  rewrite @cl_subst_subst_aux;
  eauto 3 with slow;
  unfold subst_aux.

Tactic Notation "unfsubst" constr(t) :=
  rewrite (cl_subst_subst_aux t);
  eauto 3 with slow;
  unfold subst_aux.

Tactic Notation "unflsubst" "in" ident(H) :=
  rewrite @cl_lsubst_lsubst_aux in H;
  eauto 3 with slow;
  unfold subst_aux in H.

Tactic Notation "unflsubst" constr(t) "in" ident(H) :=
  rewrite (cl_lsubst_lsubst_aux t) in H;
  eauto 3 with slow;
  unfold subst_aux in H.

Tactic Notation "unflsubst" :=
  rewrite @cl_lsubst_lsubst_aux;
  eauto 3 with slow;
  unfold subst_aux.

Tactic Notation "unflsubst" constr(t) :=
  rewrite (cl_lsubst_lsubst_aux t);
  eauto 3 with slow;
  unfold subst_aux.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
