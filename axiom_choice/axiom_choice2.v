(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export axiom_choice.

(*

  (forall m : nat, psquash (exists n : nat, P(m,n)))
  -> (psquash (exists f : nat -> nat, forall m : nat, psquash (P (m, f m))))

 *)
Lemma choice_axiom00_psq {o} :
  forall lib f m n (P : @CTerm o),
    n <> m
    -> f <> m
    -> (forall a b,
          member lib a mkc_tnat
          -> member lib b mkc_tnat
          -> type lib (mkc_apply2 P a b))
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            m
            (mkcv_squash
               [m]
               (mkcv_exists
                  [m]
                  (mkcv_tnat [m])
                  n
                  (mkcv_apply2 [n,m]
                               (mk_cv [n,m] P)
                               (mk_cv_app_l [n] [m] (mkc_var m))
                               (mk_cv_app_r [m] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_exists
            nat2nat
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               m
               (mkcv_squash
                  [m,f]
                  (mkcv_apply2 [m,f]
                               (mk_cv [m,f] P)
                               (mk_cv_app_r [f] [m] (mkc_var m))
                               (mkcv_apply [m,f]
                                           (mk_cv_app_l [m] [f] (mkc_var f))
                                           (mk_cv_app_r [f] [m] (mkc_var m))))))).
Proof.
  introv d1 d2 impp inh.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
