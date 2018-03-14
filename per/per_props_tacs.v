(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export nuprl_props.


Lemma ccequivc_ext_mkc_function_implies {o} :
  forall lib (A A' : @CTerm o) v v' B B',
    ccequivc_ext lib (mkc_function A v B) (mkc_function A' v' B')
    -> ccequivc_ext lib A A' # bcequivc_ext lib [v] B [v'] B'.
Proof.
  introv ceq; dands; introv ext; apply ceq in ext; simpl in *; spcast;
    apply cequivc_mkc_function_implies in ext; exrepnd;
      apply computes_to_valc_isvalue_eq in ext1; eauto 3 with slow; eqconstr ext1; auto.
Qed.

Ltac ccomputes_to_valc_ext_val :=
  match goal with
  | [ H : (mkc_function _ _ _) ===>(_) (mkc_function _ _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_function_implies in H;
    repnd

  | [ H : (mkc_cequiv _ _) ===>(_) (mkc_cequiv _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_cequiv_right in H;
    repnd

  | [ H : (mkc_approx _ _) ===>(_) (mkc_approx _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_approx_right in H;
    repnd
  end.
