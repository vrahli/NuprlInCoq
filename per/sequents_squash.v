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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_squash.
Require Export sequents.


Lemma teq_and_eq_if_squash {o} :
  forall lib (a : @NTerm o) s1 s2 H wa ca1 ca2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> inhabited_type lib (lsubstc a wa s1 ca1)
    -> tequality lib (lsubstc a wa s1 ca1) (lsubstc a wa s2 ca2)
    -> (tequality lib
          (mkc_squash (lsubstc a wa s1 ca1))
          (mkc_squash (lsubstc a wa s2 ca2))
        # (inhabited_type lib (lsubstc a wa s1 ca1))).
Proof.
  introv hf sim ceq1 ceq2.

  assert (hyps_functionality lib s2 H)
    as hf2
      by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  assert (similarity lib s2 s1 H) as sim21 by (apply similarity_sym; auto).
  assert (similarity lib s1 s1 H) as sim11 by (apply similarity_refl in sim; auto).
  assert (similarity lib s2 s2 H) as sim22 by (apply similarity_refl in sim21; auto).

  dands; auto.
  rw @tequality_mkc_squash; auto.
Qed.
