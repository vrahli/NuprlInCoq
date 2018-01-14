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


Definition mk_csname {o} n : @NTerm o := oterm (Can (NCSName n)) [].

Theorem isprog_csname {o} : forall n, @isprog o (mk_csname n).
Proof.
  repeat constructor.
Qed.

Definition mkc_csname {o} n : @CTerm o := exist isprog (mk_csname n) (isprog_csname n).

Lemma fold_csname {o} : forall n, @oterm o (Can (NCSName n)) [] = mk_csname n.
Proof.
  tcsp.
Qed.

Definition mkcv_csname {o} (vs : list NVar) n : @CVTerm o vs :=
  mk_cv vs (mkc_csname n).
