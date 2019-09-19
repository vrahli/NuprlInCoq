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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

 *)


Require Export per_props_nat.
Require Export per_props_uni.
Require Export per_props_uni2.


Lemma tuni_fun {o} :
  forall lib (v : NVar),
    @type o lib (mkc_function mkc_tnat v (mkcv_tuni [v] (mkc_var v))).
Proof.
  introv.
  apply tequality_function; dands; [apply type_tnat|].
  introv ext en.
  apply equality_in_tnat in en.
  allrw @mkcv_tuni_substc; spcast.
  allrw @mkc_var_substc; eauto 3 with slow.
SearchAbout tequality mkc_tuni.
Locate equality_of_nat_bar.
Qed.
