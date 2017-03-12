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


Require Export per_props_equality.


Lemma tequality_mkc_equality_sp_eq {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    equality lib a1 a2 A
    -> (tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
        <=> (tequality lib A B # equality lib a1 b1 A # equality lib a2 b2 A)).
Proof.
  introv eqa.
  rw @tequality_mkc_equality.
  split; intro h; repnd; dands; auto; eauto 3 with slow.

  - apply tequality_iff_ext_eq; dands; auto.
    introv.
    split; intro q.

    + pose proof (h a1 a b) as w.
      destruct w as [w w']; clear w'.
      autodimp w hyp; repnd; dands; eauto 3 with nequality.

    + pose proof (h a1 a1 a1) as w.
      destruct w as [w w']; clear w'.
      autodimp w hyp; repnd; dands; eauto 3 with nequality.

      pose proof (h a1 a b) as z.
      destruct z as [z' z]; clear z'.
      autodimp z hyp; repnd; dands; eauto 3 with nequality.

  - pose proof (h a1 a1 a1) as w.
    destruct w as [w w']; clear w'.
    autodimp w hyp; repnd; dands; eauto 3 with nequality.

    pose proof (h b1 b1 b1) as z.
    destruct z as [z' z]; clear z'.
    autodimp z hyp; repnd; dands; eauto 3 with nequality.

  - pose proof (h a1 a1 a1) as w.
    destruct w as [w w']; clear w'.
    autodimp w hyp; repnd; dands; eauto 3 with nequality.

    pose proof (h b2 b2 b2) as z.
    destruct z as [z' z]; clear z'.
    autodimp z hyp; repnd; dands; eauto 3 with nequality.

  - introv; split; intro q; repnd; dands; eauto 3 with nequality.

    + eapply equality_trans;[|apply equality_sym;exact h1].
      eauto 3 with nequality.

    + eapply equality_trans;[|apply equality_sym;exact h].
      eauto 3 with nequality.
Qed.
