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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms2.


Definition mk_choice_seq {o} name : @NTerm o := oterm (Can (Ncseq name)) [].

Lemma isprogram_mk_choice_seq {o} :
  forall n, @isprogram o (mk_choice_seq n).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isprogram_mk_choice_seq : slow.

Lemma isprog_mk_choice_seq {o} :
  forall (n : choice_sequence_name), @isprog o (mk_choice_seq n).
Proof.
  introv; apply isprog_eq; apply isprogram_mk_choice_seq.
Qed.

Definition mkc_choice_seq {o} name : @CTerm o :=
  exist isprog (mk_choice_seq name) (isprog_mk_choice_seq name).
