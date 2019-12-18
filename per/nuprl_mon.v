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

*)



Require Export nuprl_extensionality.


Definition type_monotone {p} inh (ts : cts(p)) :=
  forall lib lib' T1 T2 eq,
    ts lib T1 T2 eq
    -> lib_extends inh lib' lib
    -> exists eq',
        ts lib' T1 T2 eq'
        # sub_per eq eq'.

Lemma sub_per_eq_eq_term_equals_left {o} :
  forall (per1 per2 per3 : per(o)),
    (per1 <=2=> per2)
    -> sub_per per2 per3
    -> sub_per per1 per3.
Proof.
  introv eqiff s h.
  apply s; apply eqiff; auto.
Qed.
Hint Resolve sub_per_eq_eq_term_equals_left : slow.

Lemma sub_per_equality_of_int_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_int_bar inh lib) (equality_of_int_bar inh lib').
Proof.
  introv ext h.
  unfold equality_of_int_bar in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_int_bar : slow.

Lemma sub_per_equality_of_int {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_int inh lib) (equality_of_int inh lib').
Proof.
  introv ext h.
  unfold equality_of_int in *; exrepnd.
  exists k; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_int : slow.

Lemma per_int_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_int inh ts).
Proof.
  introv per ext.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_nat_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_nat_bar inh lib) (equality_of_nat_bar inh lib').
Proof.
  introv ext h.
  unfold equality_of_nat_bar, equality_of_nat in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_nat_bar : slow.

Lemma sub_per_equality_of_nat {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_nat inh lib) (equality_of_nat inh lib').
Proof.
  introv ext h.
  unfold equality_of_nat in *; exrepnd.
  exists n; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_nat : slow.

Lemma per_nat_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_nat inh ts).
Proof.
  introv per ext.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_qnat_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_qnat_bar inh lib) (equality_of_qnat_bar inh lib').
Proof.
  introv ext h.
  unfold equality_of_qnat_bar, equality_of_qnat in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_qnat_bar : slow.

(*Lemma sub_per_equality_of_qnat {o} :
  forall (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_qnat lib) (equality_of_qnat lib').
Proof.
  introv ext h.
  unfold equality_of_qnat in *; exrepnd.
  dands; spcast; eexists; dands; eauto.
  { pose proof (h0 _ (lib_extends_trans xt ext)) as h0; simpl in *; exrepnd; exists n; auto. }
  { pose proof (h _ (lib_extends_trans xt ext)) as h; simpl in *; exrepnd; exists n; auto. }
Qed.
Hint Resolve sub_per_equality_of_qnat : slow.*)

Lemma per_qnat_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_qnat inh ts).
Proof.
  introv per ext.
  unfold per_qnat in *; exrepnd.
  exists (equality_of_qnat_bar inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_csname_bar {o} :
  forall inh n (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_csname_bar inh lib n) (equality_of_csname_bar inh lib' n).
Proof.
  introv ext h.
  unfold equality_of_csname_bar, equality_of_csname in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_csname_bar : slow.

Lemma sub_per_equality_of_csname {o} :
  forall inh n (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_csname inh lib n) (equality_of_csname inh lib' n).
Proof.
  introv ext h.
  unfold equality_of_csname in *; exrepnd.
  exists name; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_csname : slow.

Lemma per_csname_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_csname inh ts).
Proof.
  introv per ext.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar inh lib' n); dands; spcast; eauto 3 with slow.
  exists n; dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_atom_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_atom_bar inh lib) (equality_of_atom_bar inh lib').
Proof.
  introv ext h.
  unfold equality_of_atom_bar in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_atom_bar : slow.

Lemma sub_per_equality_of_atom {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_atom inh lib) (equality_of_atom inh lib').
Proof.
  introv ext h.
  unfold equality_of_atom in *; exrepnd.
  exists s; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_atom : slow.

Lemma per_atom_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_atom inh ts).
Proof.
  introv per ext.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_uatom_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_uatom_bar inh lib) (equality_of_uatom_bar inh lib').
Proof.
  introv ext h.
  unfold equality_of_uatom_bar in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_uatom_bar : slow.

Lemma sub_per_equality_of_uatom {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (equality_of_uatom inh lib) (equality_of_uatom inh lib').
Proof.
  introv ext h.
  unfold equality_of_uatom in *; exrepnd.
  exists u; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_uatom : slow.

Lemma per_uatom_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_uatom inh ts).
Proof.
  introv per ext.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_base_eq {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (per_base_eq inh lib) (per_base_eq inh lib').
Proof.
  introv ext h.
  unfold per_base_eq in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_base_eq : slow.

Lemma lib_extends_preserves_in_ext {o} :
  forall inh (lib lib' : @library o) F,
    lib_extends inh lib' lib
    -> in_ext inh lib F
    -> in_ext inh lib' F.
Proof.
  introv ext h x; eapply h; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_in_ext : slow.

Lemma sub_eq_per_base {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib),
    sub_per (per_base_eq inh lib) (per_base_eq inh lib').
Proof.
  introv ext h.
  unfold per_base_eq in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_eq_per_base : slow.

Lemma per_base_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_base inh ts).
Proof.
  introv per ext.
  unfold per_base in *; exrepnd.
  exists (per_base_eq inh lib'); dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_approx_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b,
    sub_per (per_approx_eq_bar inh lib a b) (per_approx_eq_bar inh lib' a b).
Proof.
  introv ext h.
  unfold per_approx_eq_bar in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_approx_eq_bar : slow.

(*Lemma sub_per_approx_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b,
    sub_per (per_approx_eq lib a b) (per_approx_eq lib' a b).
Proof.
  introv ext h.
  unfold per_approx_eq in *; exrepnd.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_approx_eq : slow.*)

Lemma per_approx_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_approx inh ts).
Proof.
  introv per ext.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar inh lib' a b); dands; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_cequiv_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b,
    sub_per (per_cequiv_eq_bar inh lib a b) (per_cequiv_eq_bar inh lib' a b).
Proof.
  introv ext h.
  unfold per_cequiv_eq_bar in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve sub_per_cequiv_eq_bar : slow.

(*Lemma sub_per_cequiv_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b,
    sub_per (per_cequiv_eq lib a b) (per_cequiv_eq lib' a b).
Proof.
  introv ext h.
  unfold per_cequiv_eq in *; exrepnd.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_cequiv_eq : slow.*)

Lemma per_cequiv_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_cequiv inh ts).
Proof.
  introv per ext.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar inh lib' a b); dands; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma implies_in_ext_ext_ts_raise_lib_per {o} :
  forall inh (ts : cts(o)) lib lib' (ext : lib_extends inh lib' lib) A A' (eqa : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib' (fun lib'' x => ts lib'' A A' (raise_lib_per inh eqa ext lib'' x)).
Proof.
  introv ie; repeat introv; apply ie.
Qed.
Hint Resolve implies_in_ext_ext_ts_raise_lib_per : slow.

(*Lemma implies_all_in_bar_ext_ts_raise_lib_per {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) lib' (ext : lib_extends inh lib' lib) A A' (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' A A' (eqa lib' x))
    -> all_in_bar_ext (raise_bar bar ext) (fun lib'' x => ts lib'' A A' (raise_lib_per eqa ext lib'' x)).
Proof.
  introv ie xt x; repeat introv; simpl in *; exrepnd.
  unfold raise_ext_per.
  eapply ie; eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_ts_raise_lib_per : slow.*)

(*Lemma implies_all_in_bar_ext_eqorceq_raise_lib_per {o} :
  forall lib (bar : BarLib lib) lib' (ext : lib_extends inh lib' lib) a b (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> all_in_bar_ext (raise_bar bar ext) (fun lib'' x => eqorceq lib'' (raise_lib_per eqa ext lib'' x) a b).
Proof.
  introv ie br lex; repeat introv; simpl in *; exrepnd.
  eapply ie; eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_eqorceq_raise_lib_per : slow.*)

(*Lemma implies_e_all_in_bar_ext_ts_raise_lib_per {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) lib' (ext : lib_extends inh lib' lib) A A' (eqa : lib-per(lib,o)),
    e_all_in_bar_ext bar (fun lib' x => ts lib' A A' (eqa lib' x))
    -> e_all_in_bar_ext (raise_bar bar ext) (fun lib'' x => ts lib'' A A' (raise_lib_per eqa ext lib'' x)).
Proof.
  introv ie xt; repeat introv; simpl in *; exrepnd.
  assert (lib_extends inh lib'1 lib1) as xt by eauto 3 with slow.
  pose proof (ie _ xt1 _ xt) as ie; simpl in *.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta h; introv; eauto.
Qed.
Hint Resolve implies_e_all_in_bar_ext_ts_raise_lib_per : slow.*)

(*Lemma implies_e_all_in_bar_ext_eqorceq_raise_lib_per {o} :
  forall lib (bar : BarLib lib) lib' (ext : lib_extends inh lib' lib) a b (eqa : lib-per(lib,o)),
    e_all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> e_all_in_bar_ext (raise_bar bar ext) (fun lib'' x => eqorceq lib'' (raise_lib_per eqa ext lib'' x) a b).
Proof.
  introv ie br; repeat introv; simpl in *; exrepnd.
  assert (lib_extends inh lib'1 lib1) as xt by eauto 3 with slow.
  pose proof (ie _ br1 _ xt) as ie; simpl in *.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
Qed.
Hint Resolve implies_e_all_in_bar_ext_eqorceq_raise_lib_per : slow.*)

(*Lemma per_eq_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_eq (close ts) lib T T' eq
    -> lib_extends inh lib' lib
    -> exists eq', per_eq (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_eq in *; exrepnd.
  exists (eq_per_eq lib' a1 a2 eqa) A B a1 a2 b1 b2 eqa.
  dands; spcast; eauto 3 with slow.
Abort.*)

Definition raise_ext_per_fam
           {o}
           inh
           {lib lib' : @library o}
           {eqa : lib-per(inh,lib,o)}
           (per : ext-per-fam(inh,lib,eqa,o))
           (ext : lib_extends inh lib' lib) : ext-per-fam(inh,lib',raise_lib_per inh eqa ext,o).
Proof.
  introv e.
  simpl in *.
  unfold raise_lib_per in e.
  apply (per lib'0 (lib_extends_trans ext0 ext) a a'); auto.
Defined.

Definition raise_lib_per_fam
           {o}
           inh
           {lib lib' : @library o}
           {eqa : lib-per(inh,lib,o)}
           (per : lib-per-fam(inh,lib,eqa,o))
           (ext : lib_extends inh lib' lib) : lib-per-fam(inh,lib',raise_lib_per inh eqa ext,o).
Proof.
  introv.
  exists (raise_ext_per_fam inh per ext).
  repeat introv; simpl in *.
  apply (lib_per_fam_cond _ _ per).
Defined.

Lemma implies_in_ext_ext_ts_raise_lib_per_fam {o} :
  forall inh (ts : cts(o)) lib lib' (ext : lib_extends inh lib' lib) v v' B B'
         (eqa : lib-per(inh,lib,o))
         (eqb : lib-per-fam(inh,lib,eqa,o)),
    in_ext_ext
      inh lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext
         inh lib'
         (fun lib'' x =>
            forall a a' (e : raise_lib_per inh eqa ext lib'' x a a'),
              ts lib'' (B)[[v\\a]] (B')[[v'\\a']] (raise_lib_per_fam inh eqb ext lib'' x a a' e)).
Proof.
  introv ie; repeat introv; apply ie.
Qed.
Hint Resolve implies_in_ext_ext_ts_raise_lib_per_fam : slow.

Lemma implies_type_family_ext_raise_lib_per {o} :
  forall C inh (ts : cts(o)) lib lib' (ext : lib_extends inh lib' lib) T T' eqa eqb,
    type_family_ext C inh ts lib T T' eqa eqb
    -> type_family_ext C inh ts lib' T T' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext).
Proof.
  introv tf.
  unfold type_family_ext in *; exrepnd.
  exists A A' v v' B B'; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_type_family_ext_raise_lib_per : slow.

Lemma sub_per_per_func_ext_eq {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqb,
    sub_per (per_func_ext_eq inh lib eqa eqb)
            (per_func_ext_eq inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
Proof.
  introv h; unfold per_func_ext_eq in *.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_func_ext_eq : slow.

Lemma per_func_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_func_ext inh ts).
Proof.
  introv per ext.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa ext)
         (raise_lib_per_fam inh eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_qtime_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa,
    sub_per (per_qtime_eq_bar inh lib eqa)
            (per_qtime_eq_bar inh lib' (raise_lib_per inh eqa ext)).
Proof.
  introv h.
  unfold per_qtime_eq_bar in *.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_qtime_eq_bar : slow.

Lemma per_qtime_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_qtime inh ts).
Proof.
  introv per ext.
  unfold per_qtime in *; exrepnd.

  exists (per_qtime_eq_bar inh lib' (raise_lib_per inh eqa ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa ext) A B.
  dands; eauto 3 with slow.
Qed.

(*Definition raise_bar_per {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends inh lib' lib),
    bar-per(lib,bar,o) -> bar-per(lib',raise_bar bar ext,o).
Proof.
  introv b.
  exists (fun lib1 (br : bar_lib_bar (raise_bar bar ext) lib1) lib2 ext t1 t2 =>
            exists (lib' : library),
              exists (br' : bar_lib_bar bar lib'),
                exists (x : lib_extends inh lib1 lib'),
                  bar_per_per _ b lib' br' lib2 (lib_extends_trans ext x) t1 t2).

  introv w z; repeat introv.
  simpl in *; exrepnd.
  split; introv h; exrepnd.
  { exists lib0 z1 z2; eapply (bar_per_cond _ b); eauto 3 with slow. }
  { exists lib4 w1 w2; eapply (bar_per_cond _ b); eauto 3 with slow. }
Defined.*)

Lemma sub_per_per_bar_eq {o} :
  forall inh {lib lib' : @library o} (ext : lib_extends inh lib' lib) eq eqa,
    (eq <=2=> (per_bar_eq inh lib eqa))
    -> sub_per eq (per_bar_eq inh lib' (raise_lib_per inh eqa ext)).
Proof.
  introv eqiff h.
  apply eqiff in h; clear eqiff.
  unfold per_bar_eq in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; simpl in *; auto.
Qed.
Hint Resolve sub_per_per_bar_eq : slow.

Lemma per_bar_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_bar inh ts).
Proof.
  introv per ext.
  unfold per_bar in *; exrepnd.

  exists (per_bar_eq inh lib' (raise_lib_per inh eqa ext)); dands; eauto 3 with slow;[].
  exists (raise_lib_per inh eqa ext); dands; eauto 3 with slow.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in per1; simpl in *; auto.
Qed.
Hint Resolve per_bar_monotone : slow.

Lemma lib_extends_preserves_ccequivc_ext {o} :
  forall inh lib lib' (a b : @CTerm o),
    lib_extends inh lib' lib
    -> ccequivc_ext inh lib a b
    -> ccequivc_ext inh lib' a b.
Proof.
  introv ext ceq x; eapply ceq; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_ccequivc_ext : slow.

Lemma sub_per_and_lib_extends_preserve_eqorceq {o} :
  forall inh lib lib' (a b : @CTerm o) eqa eqb,
    sub_per eqa eqb
    -> lib_extends inh lib' lib
    -> eqorceq inh lib eqa a b
    -> eqorceq inh lib' eqb a b.
Proof.
  introv sub ext eoc.
  unfold eqorceq in *; repndors;[left|right]; eauto 3 with slow.
Qed.
Hint Resolve sub_per_and_lib_extends_preserve_eqorceq : slow.

(*Lemma sub_per_per_eq_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b eqa,
    sub_per (per_eq_eq lib a b eqa) (per_eq_eq lib' a b (raise_lib_per eqa ext)).
Proof.
  introv h.
  unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; introv; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_eq_eq : slow.*)

Lemma sub_per_eq_per_eq {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b eqa eqb,
    sub_per eqa eqb
    -> sub_per (eq_per_eq inh lib a b eqa) (eq_per_eq inh lib' a b eqb).
Proof.
  introv ext sub h.
  unfold eq_per_eq in *; exrepnd.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_eq_per_eq : slow.

(*Lemma sub_per_eq_per_eq_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b (eqa eqb : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => sub_per (eqa lib' x) (eqb lib' x))
    -> sub_per (eq_per_eq_bar lib a b eqa) (eq_per_eq_bar lib' a b eqb).
Proof.
  introv ext sub h.
  unfold eq_per_eq_bar in *; exrepnd.
  exists (raise_bar bar ext).
  introv br x; simpl in *; exrepnd.
  eapply sub_per_eq_per_eq; eauto 3 with slow.
  eapply h0; eauto 3 with slow.
Qed.
Hint Resolve sub_per_eq_per_eq_bar : slow.*)

Lemma sub_per_per_union_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqb,
    sub_per (per_union_eq_bar inh lib eqa eqb)
            (per_union_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per inh eqb ext)).
Proof.
  introv h.
  unfold per_union_eq_bar in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_union_eq_bar : slow.

Lemma sub_per_per_union_eq {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqa' eqb eqb',
    sub_per eqa eqa'
    -> sub_per eqb eqb'
    -> sub_per (per_union_eq inh lib eqa eqb) (per_union_eq inh lib' eqa' eqb').
Proof.
  introv ext suba subb h.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
    [left|right]; eexists; eexists; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_union_eq : slow.

Lemma sub_per_eq_per_union_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqa' eqb eqb',
    sub_per eqa eqa'
    -> sub_per eqb eqb'
    -> sub_per (eq_per_union_bar inh lib eqa eqb) (eq_per_union_bar inh lib' eqa' eqb').
Proof.
  introv ext suba subb h.
  unfold eq_per_union_bar in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar _ _ _ _ ext) in h; auto.
  eapply in_open_bar_pres;[|exact h]; clear h; introv xt h.
  eapply sub_per_per_union_eq; try apply lib_extends_refl; eauto.
Qed.
Hint Resolve sub_per_eq_per_union_bar : slow.

Lemma sub_per_per_product_bar_eq {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqb,
    sub_per (per_product_eq_bar inh lib eqa eqb)
            (per_product_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
Proof.
  introv h.
  unfold per_product_eq_bar, per_product_eq in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_product_bar_eq : slow.

Lemma per_product_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_product_bar inh ts).
Proof.
  introv per ext.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa ext)
         (raise_lib_per_fam inh eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_set_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) eqa eqb,
    sub_per (per_set_eq_bar inh lib eqa eqb)
            (per_set_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
Proof.
  introv h.
  unfold per_set_eq_bar, per_set_eq in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_set_eq_bar : slow.

Lemma per_set_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_set inh ts).
Proof.
  introv per ext.
  unfold per_set in *; exrepnd.

  exists (per_set_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per_fam inh eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa ext)
         (raise_lib_per_fam inh eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_eq_per_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) a b (eqa : lib-per(inh,lib,o)),
    sub_per (eq_per_eq_bar inh lib a b eqa) (eq_per_eq_bar inh lib' a b (raise_lib_per inh eqa ext)).
Proof.
  introv h.
  unfold eq_per_eq_bar in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_eq_per_eq_bar : slow.

Lemma implies_eqorceq_ext_raise_lib_per {o} :
  forall inh lib lib' (ext : lib_extends inh lib' lib) (eqa : lib-per(inh,lib,o)) a b,
    eqorceq_ext inh lib eqa a b
    -> eqorceq_ext inh lib' (raise_lib_per inh eqa ext) a b.
Proof.
  introv ee; introv; simpl in *.
  eapply ee.
Qed.
Hint Resolve implies_eqorceq_ext_raise_lib_per : slow.

Lemma per_eq_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_eq inh ts).
Proof.
  introv per ext.
  unfold per_eq in *; exrepnd.

  exists (eq_per_eq_bar inh lib' a1 a2 (raise_lib_per inh eqa ext)).
  dands; eauto 3 with slow.

  exists A B a1 a2 b1 b2 (raise_lib_per inh eqa ext); dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_eq_monotone : slow.

Lemma per_union_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_union inh ts).
Proof.
  introv per ext.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar inh lib' (raise_lib_per inh eqa ext) (raise_lib_per inh eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa ext) (raise_lib_per inh eqb ext) A1 A2 B1 B2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_union_monotone : slow.

Lemma sub_per_per_image_eq_bar {o} :
  forall inh (lib lib' : @library o) (ext : lib_extends inh lib' lib) (eqa : lib-per(inh,lib,o)) f,
    sub_per (per_image_eq_bar inh lib eqa f) (per_image_eq_bar inh lib' (raise_lib_per inh eqa ext) f).
Proof.
  introv h.
  unfold per_image_eq_bar in *; exrepnd.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h; auto.
Qed.
Hint Resolve sub_per_per_image_eq_bar : slow.

Lemma per_image_monotone {o} :
  forall inh (ts : cts(o)), type_monotone inh (per_image inh ts).
Proof.
  introv per ext.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar inh lib' (raise_lib_per inh eqa ext) f1).
  dands; eauto 3 with slow;[].

  exists (raise_lib_per inh eqa ext) A1 A2 f1 f2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_image_monotone : slow.

Lemma close_monotone {o} :
  forall inh (ts : cts(o)),
    type_monotone inh ts
    -> type_monotone inh (close inh ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    pose proof (m lib lib' T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; dands; auto.

  - Case "CL_bar".
    pose proof (per_bar_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; eauto 3 with slow.

  - Case "CL_int".
    pose proof (per_int_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_nat".
    pose proof (per_nat_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_qnat".
    pose proof (per_qnat_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_csname".
    pose proof (per_csname_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_atom".
    pose proof (per_atom_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_base".
    pose proof (per_base_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_approx".
    pose proof (per_approx_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone inh ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_eq".
    pose proof (per_eq_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_qtime".
    pose proof (per_qtime_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_func".
    pose proof (per_func_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_union".
    pose proof (per_union_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_image".
    pose proof (per_image_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_set".
    pose proof (per_set_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_product".
    pose proof (per_product_monotone inh (close inh ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.
Qed.

Lemma univi_monotone_implies_univi_bar_monotone {o} :
  forall inh uni i,
    @type_monotone o inh (univi i inh uni)
    -> @type_monotone o inh (univi_bar i inh uni).
Proof.
  introv mon h ext.
  unfold univi_bar, per_bar in *; exrepnd.
  exists (per_bar_eq inh lib' (raise_lib_per inh eqa ext)).
  dands; auto; eauto 3 with slow.
  exists (raise_lib_per inh eqa ext).
  dands; tcsp;[].
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ ext) in h1; simpl in *; auto.
Qed.
Hint Resolve univi_monotone_implies_univi_bar_monotone : slow.

Lemma or_monotone {o} :
  forall inh (ts1 ts2 : cts(o)),
    type_monotone inh ts1
    -> type_monotone inh ts2
    -> type_monotone inh (cts_or ts1 ts2).
Proof.
  introv mona monb x ext.
  destruct x as [x|x].
  { eapply mona in x; apply x in ext; exrepnd.
    exists eq'; dands; tcsp. }
  { eapply monb in x; apply x in ext; exrepnd.
    exists eq'; dands; tcsp. }
Qed.
Hint Resolve or_monotone : slow.

Lemma univi_monotone {o} :
  forall inh uni i,
    type_monotone inh uni
    -> @type_monotone o inh (univi i inh uni).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv mon h ext.
  allrw @univi_exists_iff; exrepnd.
  exists (univi_eq j inh uni lib').
  allrw @univi_exists_iff.
  dands.

  { exists j; dands; tcsp; spcast; eauto 3 with slow. }

  { introv h.
    apply h0 in h; clear h0.
    unfold univi_eq, close_ex_eq in *; exrepnd.

    pose proof (@close_monotone o inh (univi_bar j inh uni)) as q.
    repeat (autodimp q hyp); eauto 4 with slow;[].

    pose proof (q lib lib' a b eqa) as q.
    repeat (autodimp q hyp); exrepnd.
    exists eq'; dands; auto. }
Qed.
Hint Resolve univi_monotone : slow.

Lemma univi_bar_monotone {o} :
  forall inh uni i, @type_monotone o inh (univi_bar i inh uni).
Proof.
  introv; unfold univi_bar; eauto 3 with slow.
Qed.
Hint Resolve univi_bar_monotone : slow.

(*Lemma univ_ex_monotone {o} : forall inh, @type_monotone o inh (univ_ex inh).
Proof.
  introv u e.
  unfold univ_ex in *; exrepnd.
  apply (univi_monotone _ _ lib lib') in u0; auto.
  exrepnd.
  exists eq'; dands; auto.
  exists i; auto.
Qed.
Hint Resolve univ_ex_monotone : slow.*)

(*Lemma univ_monotone {o} : @type_monotone o nuprlIA univ.
Proof.
  introv u e.
  unfold univ in *; exrepnd.
  eapply (per_bar_monotone _ _ lib lib') in u; auto.
Qed.
Hint Resolve univ_monotone : slow.*)

(*Lemma univa_monotone {o} : forall i inh, @type_monotone o inh (univa i).
Proof.
  induction i; introv h ext; simpl in *; tcsp; repnd.

Check raise_lib_per.
Qed.*)

Lemma univa_ex_bar_monotone {o} : @type_monotone o nuprla_ex_inh univa_ex_bar.
Proof.
  unfold univa_ex_bar; introv h ext; exrepnd. eapply per_bar_monotone; eauto.
Qed.
Hint Resolve univa_ex_bar_monotone : slow.

Lemma nuprl_monotone {o} : @type_monotone o nuprla_ex_inh nuprl.
Proof.
  introv.
  apply close_monotone; eauto 3 with slow.
  apply per_bar_monotone.
Qed.
Hint Resolve nuprl_monotone : slow.

Lemma tequality_monotone {o} :
  forall lib lib' (A B : @CTerm o),
    lib_extends nuprla_ex_inh lib' lib
    -> tequality lib A B
    -> tequality lib' A B.
Proof.
  introv ext teq.
  unfold tequality in *; exrepnd.
  apply (nuprl_monotone lib lib') in teq0; auto.
  exrepnd.
  exists eq'; dands; auto.
Qed.
Hint Resolve tequality_monotone : slow.

Lemma univia_i_monotone {o} : forall i, @type_monotone o nuprla_ex_inh (univia_i i).
Proof.
  introv u e.
  unfold univia_i in *; exrepnd.
  eapply per_bar_monotone in u; apply u in e; clear u; exrepnd.
  exists eq'; dands; tcsp.
Qed.
Hint Resolve univia_i_monotone : slow.

Lemma nuprli_monotone {o} : forall i, @type_monotone o nuprla_ex_inh (nuprli i).
Proof.
  introv u e.
  unfold nuprli in *; exrepnd.
  pose proof (@close_monotone o nuprla_ex_inh (univia_i i)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprli_monotone : slow.

Lemma equality_monotone {o} :
  forall lib lib' (a b A : @CTerm o),
    lib_extends nuprla_ex_inh lib' lib
    -> equality lib a b A
    -> equality lib' a b A.
Proof.
  introv ext equ.
  unfold equality in *; exrepnd.
  apply (nuprl_monotone lib lib') in equ1; exrepnd; auto.
  exists eq'; dands; tcsp.
Qed.
Hint Resolve equality_monotone : slow.

Lemma member_monotone {o} :
  forall lib lib' (a A : @CTerm o),
    lib_extends nuprla_ex_inh lib' lib
    -> member lib a A
    -> member lib' a A.
Proof.
  introv ext equ.
  eapply equality_monotone in equ; eauto.
Qed.
Hint Resolve member_monotone : slow.

Lemma meta_type_monotone {o} :
  forall lib lib' (A : @CTerm o),
    lib_extends nuprla_ex_inh lib' lib
    -> type lib A
    -> type lib' A.
Proof.
  introv ext equ.
  eapply tequality_monotone in equ; eauto.
Qed.
Hint Resolve meta_type_monotone : slow.
