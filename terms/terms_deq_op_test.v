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


Require Export terms_deq_op.
Require Export terms_union.


Eval compute in (term_dec_op mk_axiom mk_axiom).

Eval compute in (term_dec_op (mk_inl mk_axiom) (mk_inl mk_axiom)).

Eval compute in (term_dec_op
                   (mk_equality (mk_inl mk_axiom) (mk_inl mk_axiom) (mk_bunion mk_true mk_true))
                   (mk_equality (mk_inl mk_axiom) (mk_inl mk_axiom) (mk_bunion mk_true mk_true))).
