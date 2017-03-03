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


(*Require Export per_props_cequiv.*)
Require Export per_props_isect.
Require Export per_props_not.

Hint Rewrite @csubst_mk_cv : slow.

Lemma type_mkc_top {o} : forall lib, @type o lib mkc_top.
Proof.
  introv.
  rw @type_isect; dands; eauto 2 with slow.
  introv ea.
  autorewrite with slow; eauto 2 with slow.
Qed.
Hint Resolve type_mkc_top : slow.

Lemma equality_mkc_top {o} :
  forall lib (a b : @CTerm o), equality lib a b mkc_top.
Proof.
  introv.
  rw @equality_in_isect; dands; introv; eauto 2 with slow; introv e;
    autorewrite with slow; eauto 2 with slow.
  apply equality_in_false in e; sp.
Qed.
Hint Resolve equality_mkc_top : slow.
