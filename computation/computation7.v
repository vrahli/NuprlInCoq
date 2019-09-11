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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export computation6.


Definition reduces_in_atmost_k_stepsc {o} lib (t1 t2 : @CTerm o) k :=
  reduces_in_atmost_k_steps lib (get_cterm t1) (get_cterm t2) k.

Lemma reduces_toc_iff_reduces_in_atmost_k_stepsc {o} :
  forall lib (t1 t2 : @CTerm o),
    reduces_toc lib t1 t2
    <=> {k : nat & reduces_in_atmost_k_stepsc lib t1 t2 k}.
Proof.
  introv.
  destruct_cterms.
  unfold reduces_toc, reduces_to, reduces_in_atmost_k_stepsc; simpl; sp.
Qed.

Lemma computes_to_valc_iff_reduces_toc {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    <=> (reduces_toc lib t1 t2 # iscvalue t2).
Proof.
  introv; destruct_cterms.
  unfold computes_to_valc, reduces_toc, iscvalue; simpl; split; intro k; repnd; tcsp.
  unfold computes_to_value; sp.
Qed.

Lemma computes_to_valc_iff_reduces_in_atmost_k_stepsc {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    <=> ({k : nat & reduces_in_atmost_k_stepsc lib t1 t2 k}
         # iscvalue t2).
Proof.
  introv.
  rw @computes_to_valc_iff_reduces_toc.
  rw @reduces_toc_iff_reduces_in_atmost_k_stepsc; tcsp.
Qed.

Lemma reduces_in_atmost_k_stepsc_le {o} :
  forall lib (t v : @CTerm o) k j,
    k <= j
    -> iscvalue v
    -> reduces_in_atmost_k_stepsc lib t v k
    -> reduces_in_atmost_k_stepsc lib t v j.
Proof.
  introv lek isv r.
  destruct_cterms; allunfold @reduces_in_atmost_k_stepsc; allsimpl.
  allunfold @iscvalue; allsimpl.
  eapply no_change_after_value_ra; eauto.
Qed.

Definition compute_eager_exc {o}
           (lib : library)
           (a e : @NTerm o) : Comput_Result :=
  match a with
    | vterm _ => cfailure compute_step_error_not_closed (mk_exception a e)
    | oterm op _ =>
      match op with
        | Can _ =>
          match compute_step lib e with
            | csuccess e' => csuccess (mk_exception a e')
            | cfailure m e' => cfailure m (mk_exception a e')
          end
        | Exc =>
          match compute_step lib e with
            | csuccess e' => csuccess (mk_exception a e')
            | cfailure m e' => cfailure m (mk_exception a e')
          end
        | _ =>
          match compute_step lib a with
            | csuccess a' => csuccess (mk_exception a' e)
            | cfailure m a' => cfailure m (mk_exception a' e)
          end
      end
  end.

Fixpoint compute_at_most_k_steps_exc {p}
         (lib : library)
         (k : nat)
         (t : NTerm) : @Comput_Result p :=
  match k with
    | 0 => csuccess t
    | S n =>
      match t with
        | oterm Exc [bterm [] a, bterm [] e] =>
          match compute_eager_exc lib a e with
            | csuccess u => compute_at_most_k_steps_exc lib n u
            | cfailure m u => cfailure m u
          end
        | oterm Exc _ => cfailure bad_args t
        | _ => match compute_step lib t with
                 | csuccess u => compute_at_most_k_steps_exc lib n u
                 | cfailure m u => cfailure m u
               end
      end
  end.

Definition reduces_in_atmost_k_steps_exc {o} lib (t u : @NTerm o) k :=
  compute_at_most_k_steps_exc lib k t = csuccess u.

Definition reduces_in_atmost_k_steps_excc {o} lib (t u : @CTerm o) k :=
  reduces_in_atmost_k_steps_exc lib (get_cterm t) (get_cterm u) k.
