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


Require Export terms2.


Definition mk_refname {o} n : @NTerm o := oterm (Can (NRefName n)) [].

Theorem isprog_refname {o} : forall n, @isprog o (mk_refname n).
Proof.
  repeat constructor.
Qed.

Definition mkc_refname {o} n : @CTerm o := exist isprog (mk_refname n) (isprog_refname n).

Lemma fold_refname {o} : forall n, @oterm o (Can (NRefName n)) [] = mk_refname n.
Proof.
  tcsp.
Qed.

Definition mkcv_refname {o} (vs : list NVar) n : @CVTerm o vs :=
  mk_cv vs (mkc_refname n).
