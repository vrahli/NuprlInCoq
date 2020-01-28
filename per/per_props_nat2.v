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


Require Export per_props_tacs.
Require Export Coq.Logic.ConstructiveEpsilon.
Require Export natk.
Require Export natk2.
Require Export cequiv_seq_util.
(*Require Export per_respects.*)
Require Export per_props_nat.
Require Export per_props_union.


Lemma equality_mkc_inl_implies {o} :
  forall lib (t1 t2 A B : @CTerm o),
    equality lib (mkc_inl t1) (mkc_inl t2) (mkc_union A B)
    -> equality lib t1 t2 A.
Proof.
  introv e.
  apply equality_mkc_union in e; repnd.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; spcast.
  repndors; exrepnd; spcast; repeat ccomputes_to_valc_ext_val.
  eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;eauto|].
  eapply equality_respects_cequivc_right;[|eauto]; apply ccequivc_ext_sym;auto.
Qed.

(* MOVE *)
Lemma all_in_ex_bar_in_ext_implies {o} :
  forall (lib : @library o) F,
    in_open_bar lib (fun lib' => in_ext lib' F) -> in_open_bar lib F.
Proof.
  introv h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' xt; apply h1; eauto 3 with slow.
Qed.

Lemma tt_not_ccequivc_ext_ff {o} :
  forall (lib : @library o), !ccequivc_ext lib tt ff.
Proof.
  introv h.
  pose proof (h _ (lib_extends_refl _)) as h; simpl in h; spcast.
  apply tt_not_cequivc_ff in h; auto.
Qed.

Lemma equality_tt_in_bool_implies_cequiv {o} :
  forall lib (t : @CTerm o),
    equality lib t tt mkc_bool
    -> ccequivc_bar lib t tt.
Proof.
  introv e.
  apply equality_in_bool in e.
  apply all_in_ex_bar_in_ext_implies.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd.
  repndors; repnd; spcast; eauto with slow.
  apply tt_not_ccequivc_ext_ff in e; sp.
Qed.

Lemma ccomputes_to_valc_ext_inl_implies_ccequivc_ext_isl_tt {o} :
  forall lib (t u : @CTerm o),
    ccomputes_to_valc_ext lib t (mkc_inl u)
    -> ccequivc_ext lib (mkc_isl t) tt.
Proof.
  introv comp ext; apply comp in ext; exrepnd; spcast; clear comp.
  apply cequivc_mkc_inl_implies in ext0; exrepnd.
  apply computes_to_valc_isvalue_eq in ext0; eauto 3 with slow; subst.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact ext1|].
  apply computes_to_valc_implies_cequivc.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma ccomputes_to_valc_ext_inr_implies_ccequivc_ext_isl_ff {o} :
  forall lib (t u : @CTerm o),
    ccomputes_to_valc_ext lib t (mkc_inr u)
    -> ccequivc_ext lib (mkc_isl t) ff.
Proof.
  introv comp ext; apply comp in ext; exrepnd; spcast; clear comp.
  apply cequivc_mkc_inr_implies in ext0; exrepnd.
  apply computes_to_valc_isvalue_eq in ext0; eauto 3 with slow; subst.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact ext1|].
  apply computes_to_valc_implies_cequivc.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma implies_isl_in_bool {o} :
  forall lib (A B a b : @CTerm o),
    equality lib a b (mkc_union A B)
    -> equality lib (mkc_isl a) (mkc_isl b) mkc_bool.
Proof.
  introv e.
  apply equality_mkc_union in e; exrepnd.
  apply equality_in_bool.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd.
  repndors; exrepnd; spcast;[left|right]; dands; spcast.
  - eapply ccomputes_to_valc_ext_inl_implies_ccequivc_ext_isl_tt; eauto.
  - eapply ccomputes_to_valc_ext_inl_implies_ccequivc_ext_isl_tt; eauto.
  - eapply ccomputes_to_valc_ext_inr_implies_ccequivc_ext_isl_ff; eauto.
  - eapply ccomputes_to_valc_ext_inr_implies_ccequivc_ext_isl_ff; eauto.
Qed.

Lemma lsubstc_mk_unit {o} :
  forall w (s : @CSub o) c,
    lsubstc mk_unit w s c = mkc_unit.
Proof.
  introv.
  unfold mk_unit, mkc_unit.
  rw @lsubstc_mk_true; apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_natU {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_natU w s c) natU.
Proof.
  introv.
  unfold mk_natU, natU.
  pose proof (lsubstc_mk_bunion_ex mk_tnat mk_unit s w c) as h.
  exrepnd.
  eapply alphaeqc_trans;[exact h1|]; clear h1.
  rw @lsubstc_mkc_tnat.
  rw @lsubstc_mk_unit.
  apply alphaeqc_refl.
Qed.

Lemma lsubstc_mk_nat2nat {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_nat2nat w s c) nat2nat.
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 2 with slow.

  simpl.

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  fold_terms.
  auto.
Qed.

Lemma type_nat2nat {o} :
  forall (lib : @library o), type lib nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply type_mkc_fun; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2nat : slow.

(*Lemma tequality_natk2nat {o} :
  forall lib (a b : @CTerm o),
    tequality lib (natk2nat a) (natk2nat b)
     <=> all_in_ex_bar lib (fun lib => {k1 , k2 : Z
          , (a) ===>(lib) (mkc_integer k1)
          # (b) ===>(lib) (mkc_integer k2)
          # (forall k : Z,
               (0 <= k)%Z ->
               ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z)}).
Proof.
  introv.
  unfold natk2nat.
  rw @tequality_mkc_fun.
  rw @tequality_mkc_natk.
  split; intro k; exrepnd; dands; eauto 3 with slow.
  introv x inh; apply type_tnat.
Qed.*)

Lemma tequality_natk2nat_aux {o} :
  forall lib (a b : @CTerm o) k1 k2,
    (a) ===>(lib) (mkc_integer k1)
    ->  (b) ===>(lib) (mkc_integer k2)
    -> (tequality lib (natk2nat a) (natk2nat b)
        <=> forall k : Z, (0 <= k)%Z -> ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z).
Proof.
  introv compa compb.
  unfold natk2nat.
  rw @tequality_mkc_fun.
  rw (tequality_mkc_natk_aux lib a b k1 k2 compa compb).
  split; intro k; exrepnd; dands; eauto 3 with slow.
  introv x inh; apply type_tnat.
Qed.

Lemma equality_natk_to_tnat {o} :
  forall lib (n1 n2 k : @CTerm o) n,
    k ===>(lib) (mkc_integer n)
    -> equality lib n1 n2 (mkc_natk k)
    -> equality lib n1 n2 mkc_tnat.
Proof.
  introv compk e.

  eapply equality_in_natk_aux in e; exrepnd; eauto.
  apply equality_in_tnat.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd.
  exists m; dands; spcast; auto.
Qed.

Lemma equality_nat2nat_to_natk2nat {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_tnat
    -> equality lib f g nat2nat
    -> equality lib f g (natk2nat n).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;try exact m; clear m; introv x m; exrepnd.
  allunfold @equality_of_nat; exrepnd; spcast; GC.
  eapply equality_monotone in e;[|eauto].
  clear dependent lib.
  rename lib' into lib.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { eapply type_mkc_natk_aux; eauto. }

  introv x en.
  eapply equality_natk_to_tnat in en; eauto 2 with slow.
Qed.

Lemma nat_in_nat {o} :
  forall (lib : @library o) n,
    member lib (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat.
  apply in_ext_implies_all_in_ex_bar; introv y; eauto 3 with slow.
  exists n; dands; eauto 3 with slow.
Qed.

Definition equality_of_nat_tt {o} lib (n m : @CTerm o) :=
  {k : nat & computes_to_valc lib n (mkc_nat k)
           # computes_to_valc lib m (mkc_nat k)}.

Definition equality_of_nat2 {p} lib (t1 t2 : @CTerm p) :=
  {j : nat
   , {n : nat
   , reduces_kstepsc lib t1 (mkc_nat n) j
   # reduces_kstepsc lib t2 (mkc_nat n) j}}.

(*Lemma equality_of_nat_implies_nat2 {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2 -> equality_of_nat2 lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
  exists (Peano.max k1 k0); exists k; dands; spcast.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e4]; auto;
    apply Nat.le_max_r; auto.
  - eapply reduces_in_atmost_k_stepsc_le;[|idtac|exact e2]; auto;
    apply Nat.le_max_l; auto.
Qed.*)

(*Lemma equality_of_nat2_implies_nat {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat2 lib t1 t2 -> equality_of_nat lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat2 in e; exrepnd; spcast.
  exists n; dands; spcast;
  apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
  dands; eauto 3 with slow.
Qed.*)

Lemma dec_reduces_kstepsc {o} :
  forall lib k (t v : @CTerm o),
    (forall x, decidable (x = get_cterm v))
    -> decidable (reduces_kstepsc lib t v k).
Proof.
  introv d.
  destruct_cterms; allsimpl.
  pose proof (dec_reduces_in_atmost_k_steps lib k x0 x d) as h.
  destruct h as [h|h];[left|right].
  - spcast; tcsp.
  - intro r; spcast; tcsp.
Qed.

(*Lemma equality_of_nat_imp_tt {o} :
  forall lib (n m : @CTerm o),
    equality_of_nat lib n m
    -> equality_of_nat_tt lib n m.
Proof.
  introv e.
  unfold equality_of_nat_tt.
  apply equality_of_nat_implies_nat2 in e.
  unfold equality_of_nat2 in e.
  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in e; auto.

  - exrepnd.
    apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
      in e0; auto.

    + exrepnd.
      exists x0; dands; auto;
      apply computes_to_valc_iff_reduces_in_atmost_k_stepsc;
      dands; eauto 3 with slow; exists x; spcast; auto.

    + clear e0.
      introv.
      pose proof (dec_reduces_kstepsc lib x n (mkc_nat x0)) as h; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      pose proof (dec_reduces_kstepsc lib x m (mkc_nat x0)) as q; allsimpl.
      autodimp q hyp; eauto 3 with slow.
      destruct h as [h|h]; destruct q as [q|q]; tcsp;
      try (complete (right; intro r; repnd; tcsp)).

  - clear e.
    introv.
    remember (compute_at_most_k_steps lib x (get_cterm n)) as c1; symmetry in Heqc1.
    remember (compute_at_most_k_steps lib x (get_cterm m)) as c2; symmetry in Heqc2.
    destruct c1, c2.

    + destruct (decidable_ex_mk_nat n0) as [h|h]; exrepnd.

      * rw h0 in Heqc1; clear h0.
        destruct (decidable_ex_mk_nat n1) as [q|q]; exrepnd.

        { rw q0 in Heqc2; clear q0.
          destruct (deq_nat n2 n3) as [d|d].

          - subst.
            left; exists n3; dands; spcast; auto.

          - right; intro r; exrepnd; spcast.
            allunfold @reduces_in_atmost_k_stepsc; allsimpl.
            allunfold @reduces_in_atmost_k_steps.
            rw Heqc1 in r1.
            rw Heqc2 in r0.
            inversion r1 as [c1].
            inversion r0 as [c2].
            allapply Znat.Nat2Z.inj; subst; tcsp.
        }

        { right; intro r; exrepnd; spcast.
          allunfold @reduces_in_atmost_k_stepsc; allsimpl.
          allunfold @reduces_in_atmost_k_steps.
          rw Heqc1 in r1.
          rw Heqc2 in r0.
          inversion r1 as [c1].
          inversion r0 as [c2].
          allapply Znat.Nat2Z.inj; subst; tcsp.
          destruct q; exists n3; auto.
        }

      * right; intro r; exrepnd; spcast.
        allunfold @reduces_in_atmost_k_stepsc; allsimpl.
        allunfold @reduces_in_atmost_k_steps.
        rw Heqc1 in r1.
        rw Heqc2 in r0.
        inversion r1 as [c1].
        inversion r0 as [c2].
        allapply Znat.Nat2Z.inj; subst; tcsp.
        destruct h; exists n2; auto.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.

    + right; intro r; exrepnd; spcast.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allunfold @reduces_in_atmost_k_steps.
      rw Heqc1 in r1.
      rw Heqc2 in r0.
      ginv.
Qed.*)

Lemma equality_in_tnat_nat {o} :
  forall (lib : @library o) n, equality lib (mkc_nat n) (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat.
  apply in_ext_implies_all_in_ex_bar; introv x.
  unfold equality_of_nat; exists n.
  dands; eauto 3 with slow.
Qed.
Hint Resolve equality_in_tnat_nat : slow.

Lemma member_tnat_implies_computes {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    -> in_open_bar lib (fun lib => {k : nat , ccomputes_to_valc_ext lib t (mkc_nat k)}).
Proof.
  introv mem.
  apply equality_in_tnat in mem.
  eapply all_in_ex_bar_modus_ponens1;try exact mem; clear mem; introv x mem; exrepnd.
  unfold equality_of_nat in mem; exrepnd.
  exists n; spcast; auto.
Qed.

Lemma member_tnat_iff {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    <=> in_open_bar lib (fun lib => {k : nat , ccomputes_to_valc_ext lib t (mkc_nat k)}).
Proof.
  introv; split; introv mem.
  - apply member_tnat_implies_computes; auto.
  - apply equality_in_tnat.
    eapply all_in_ex_bar_modus_ponens1;try exact mem; clear mem; introv x mem; exrepnd; spcast.
    exists k; dands; spcast; auto.
Qed.

Lemma equality_nat2nat_apply {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2nat
    -> equality lib a b mkc_tnat
    -> equality lib (mkc_apply f a) (mkc_apply g b) mkc_tnat.
Proof.
  introv eqf eqn.
  unfold nat2nat in eqf.
  apply equality_in_fun in eqf; repnd.
  apply eqf in eqn; auto; eauto 3 with slow.
Qed.

Lemma equality_int_nat_implies_cequivc {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    -> ccequivc_bar lib a b.
Proof.
  introv e.
  apply equality_in_tnat in e.
  apply all_in_ex_bar_in_ext_implies.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; spcast.
  unfold equality_of_nat in e; exrepnd.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in e1.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in e0.
  eapply ccequivc_ext_trans;[eauto|].
  apply ccequivc_ext_sym; auto.
Qed.
