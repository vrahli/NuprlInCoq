(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export bar_induction2.

Lemma well_founded_lt :
  well_founded lt.
Proof.
  introv.
  induction a.
  - constructor; introv h; omega.
  - inversion IHa as [imp].
    constructor; introv h.
    rewrite NPeano.Nat.lt_succ_r in h.
    destruct h; auto.
    apply imp; omega.
Qed.

Definition update_seq_from {o} (s : @CTerm o) (n m : nat) (v : NVar) :=
  mkc_lam
    v
    (mkcv_less
       [v]
       (mkc_var v)
       (mkcv_nat [v] n)
       (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
       (mkcv_nat [v] m)).

Lemma is_seq_update_seq_from {o} :
  forall lib (s : @CTerm o) n m v,
    is_kseq lib s n
    -> is_seq lib (update_seq_from s n m v).
Proof.
  introv isk.
  unfold is_kseq, eq_kseq in isk.
  unfold is_seq, update_seq_from, nat2nat.
  apply equality_in_fun; dands; eauto 3 with slow;[].

  introv en.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  repeat (rewrite mkcv_less_substc).
  repeat (rewrite mkcv_apply_substc).
  repeat (rewrite mkc_var_substc).
  repeat (rewrite mkcv_nat_substc).
  repeat (rewrite csubst_mk_cv).

  apply equality_in_tnat in en.
  unfold equality_of_nat in en; exrepnd; spcast.
  allapply @computes_to_valc_implies_cequivc.

  eapply equality_respects_cequivc_left;
    [apply cequivc_mkc_less;
      [apply cequivc_sym;eauto
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_mkc_less;
      [apply cequivc_sym;eauto
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_mkc_less_nat
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_mkc_less_nat
    |].
  boolvar.

  - eapply equality_natk2nat_implies in isk;[|eauto]; exrepnd.
    allapply @computes_to_valc_implies_cequivc.
    eapply equality_respects_cequivc_left;
      [apply implies_cequivc_apply;
        [apply cequivc_refl
        |apply cequivc_sym;eauto]
      |].
    eapply equality_respects_cequivc_right;
      [apply implies_cequivc_apply;
        [apply cequivc_refl
        |apply cequivc_sym;eauto]
      |].
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;eauto
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;eauto
      |].
    eauto 3 with slow.

  - eauto 3 with slow.
Qed.

Definition barred {o} lib (P : @CTerm o) :=
  forall s,
    is_seq lib s ->
    {n : nat & inhabited_type lib (mkc_apply2 P (mkc_nat n) s)}.

Definition KSeq {o lib} := {s : @CTerm o & {n : nat & is_kseq lib s n}}.

(* s2 is of length n (from 0 to n-1) and s1 of length n+1 (from 0 to n) *)
Definition lt_seq {o}
           lib P (b : barred lib P) (v : NVar)
           (ks1 ks2 : @KSeq o lib) : Prop :=
  match ks1, ks2 with
    | existT s1 (existT n1 i1), existT s2 (existT n2 i2) =>
      n1 = n2 + 1
      /\ (forall m,
            m < n2 ->
            ccequivc lib (mkc_apply s1 (mkc_nat m)) (mkc_apply s2 (mkc_nat m)))
      /\ match b (update_seq_from s1 n1 0 v)
                 (is_seq_update_seq_from lib s1 n1 0 v i1) with
           | existT m inh => m >= n1
         end
  end.

Lemma well_founded_lt_seq {o} :
  forall lib P (b : @barred o lib P) v,
    well_founded (lt_seq lib P b v).
Proof.
  introv; unfold well_founded; introv.
  destruct a as [s a].
  destruct a as [n i].
Qed.

Lemma bar_induction_meta_sp {o} :
  forall lib P (X c : @CTerm o) v,
    barind_meta2_fun_bar lib P X v
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar ind.
  unfold barind_meta2_fun_ind in ind.
  unfold barind_meta2_fun_bar in bar.
  Print meta2_fun_on_seq.

  (*

Can we prove that given the bar, the relation a < b,
 true if a is closer to the bar (by 1) than b,
is well-founded?

   *)

  Check well_founded_induction_type.
  Print well_founded.

Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
