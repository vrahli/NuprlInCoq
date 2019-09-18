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
           Abhishek Anand

*)


Require Export per_props_nat2.


Lemma tequality_natk2nat_nat {o} :
  forall lib n,
    @tequality o lib (natk2nat (mkc_nat n)) (natk2nat (mkc_nat n)).
Proof.
  introv.
  eapply tequality_natk2nat_aux;
    allrw @mkc_nat_eq; eauto 3 with slow.
  introv x.
  destruct (Z_lt_le_dec k (Z.of_nat n)); sp.
Qed.
Hint Resolve tequality_natk2nat_nat : slow.

Lemma implies_equality_natk2nat {o} :
  forall lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat
           & ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
           # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality lib f g (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { eapply type_mkc_natk_aux;
    allrw @mkc_nat_eq; eauto 3 with slow. }

  introv x e.
  eapply equality_in_natk_aux in e; exrepnd; spcast;
    allrw @mkc_nat_eq; eauto 3 with slow.

  eapply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv y e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        exact e1]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  assert (m < n) as ltm by omega.
  clear e0.

  apply equality_in_tnat.
  pose proof (imp m ltm) as h; exrepnd.
  apply in_ext_implies_all_in_ex_bar; introv z.
  exists k; dands; eauto 4 with slow.
Qed.

Lemma implies_member_natk2nat {o} :
  forall lib (f : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat & ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member lib f (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nat.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists k; auto.
Qed.

Lemma equality_natk2nat_implies {o} :
  forall lib m (f g : @CTerm o) n,
    m < n
    -> equality lib f g (natk2nat (mkc_nat n))
    -> in_open_bar lib (fun lib => {k : nat
        , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
        # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)}).
Proof.
  introv ltm mem.
  apply equality_in_fun in mem; repnd.
  clear mem0 mem1.
  pose proof (mem _ (lib_extends_refl lib) (mkc_nat m) (mkc_nat m)) as h; clear mem.
  autodimp h hyp.

  { eapply equality_in_natk_aux;
    allrw @mkc_nat_eq; eauto 3 with slow.
    apply in_ext_implies_all_in_ex_bar; introv x.
    exists m; dands; try omega; rw @mkc_nat_eq; eauto 3 with slow. }

  eapply equality_in_tnat in h.
  eapply all_in_ex_bar_modus_ponens1;try exact h; clear h; introv x h; exrepnd; spcast.
  unfold per_props_nat.equality_of_nat in h; exrepnd.
  exists k; auto; dands; spcast; auto.
Qed.

Lemma member_natk2nat_implies {o} :
  forall lib m (f : @CTerm o) n,
    m < n
    -> member lib f (natk2nat (mkc_nat n))
    -> in_open_bar lib (fun lib => {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}).
Proof.
  introv ltm mem.
  eapply equality_natk2nat_implies in mem;[|exact ltm].
  eapply all_in_ex_bar_modus_ponens1;try exact mem; clear mem; introv x mem; exrepnd; spcast.
  exists k; spcast; auto.
Qed.
