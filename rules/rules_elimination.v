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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export sequents_equality.
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export rules_tyfam.
Require Export rules_tyfam2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export lsubstc_weak.

Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.


(*

  Our elimination rules are simpler than the ones in Nuprl.
  This rule is to get back the same behavior

<<
   H, x : t in T |- C ext e[z\t]

     By elimination z

     H, z : T, x = z = t in T |- e
>>

 *)


Definition rule_elimination_concl {o} (H : @bhyps o) x z t T C e :=
  mk_baresequent
    (snoc H (mk_hyp x (mk_member t T)))
    (mk_concl C (subst e z t)).

Definition rule_elimination_hyp1 {o} (H : @bhyps o) x z t T C e :=
  mk_baresequent
    (snoc (snoc H (mk_hyp z T)) (mk_hyp x (mk_equality (mk_var z) t T)))
    (mk_concl C e).

Definition rule_elimination {o}
           (H : @bhyps o)
           (x z : NVar)
           (t T C e : NTerm) :=
  mk_rule
    (rule_elimination_concl H x z t T C e)
    [
      rule_elimination_hyp1 H x z t T C e
    ]
    [(*sarg_term a, sarg_var z*)].
