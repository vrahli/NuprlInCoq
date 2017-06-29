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

  Authors: Vincent Rahli

*)


Require Export computation2.
Require Export soterms.


Fixpoint compute_atmost_k_steps {o}
         (lib : library)
         (k   : nat)
         (t   : @NTerm o) : NTerm :=
  match k with
    | 0 => t
    | S n =>
      match compute_step lib t with
      | csuccess u => compute_atmost_k_steps lib n u
      | cfailure _ _ => t
      end
  end.

Lemma reduces_atmost_k_steps_of_compute_atmost_k_steps {o} :
  forall lib k (t : @NTerm o),
    {n : nat
     & n <= k
     # reduces_in_atmost_k_steps lib t (compute_atmost_k_steps lib k t) n}.
Proof.
  induction k; introv; simpl.

  - exists 0; dands; auto.
    rw @reduces_in_atmost_k_steps_0; auto.

  - remember (compute_step lib t) as comp; symmetry in Heqcomp.
    destruct comp as [u|].

    + pose proof (IHk u) as h; clear IHk; exrepnd.
      exists (S n); dands; auto; try omega.
      rw @reduces_in_atmost_k_steps_S; allrw.
      eexists; dands; eauto.

    + exists 0; dands; try omega.
      rw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma reduces_to_of_compute_atmost_k_steps {o} :
  forall lib k (t : @NTerm o),
    reduces_to lib t (compute_atmost_k_steps lib k t).
Proof.
  introv.
  pose proof (reduces_atmost_k_steps_of_compute_atmost_k_steps lib k t) as q; exrepnd.
  exists n; auto.
Qed.

Definition opabs_member : opabs := Build_opabs "member" [] [0,0].

(* It would be better if the proof was just eq_refl *)
Lemma opabs_member_correct {o} :
  @correct_abs
    o
    opabs_member
    [(nvart, 0), (nvarT, 0)]
    (mk_so_equality (sovar nvart []) (sovar nvart []) (sovar nvarT [])).
Proof.
  exact (eq_refl, (eq_refl, (eq_refl, (eq_refl, eq_refl)))).
Qed.

Definition mk_abs {o} abs (l : list (@BTerm o)) : NTerm := oterm (Abs abs) l.

Time Eval compute in (compute_atmost_k_steps
                        [lib_abs
                           opabs_member
                           [(nvart, 0), (nvarT, 0)]
                           (mk_so_equality (sovar nvart []) (sovar nvart []) (sovar nvarT []))
                           opabs_member_correct]
                        1
                        (mk_abs opabs_member [nobnd (mk_var (nvar "t")), nobnd (mk_var (nvar "T"))])).
