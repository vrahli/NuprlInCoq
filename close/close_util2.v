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


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.

Require Export close_util1.


Lemma in_ext_ext_eqbs_sym {o} :
  forall {inh} {lib} (eqa1 eqa2 : lib-per(inh,lib,o)) (eqb1 : lib-per-fam(inh,lib,eqa1,o)) (eqb2 : lib-per-fam(inh,lib,eqa2,o)),
    in_ext_ext inh lib (fun lib' x => forall a a' (u : eqa1 lib' x a a') (v : eqa2 lib' x a a'), (eqb1 lib' x a a' u) <=2=> (eqb2 lib' x a a' v))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (u : eqa2 lib' x a a') (v : eqa1 lib' x a a'), (eqb2 lib' x a a' u) <=2=> (eqb1 lib' x a a' v)).
Proof.
  introv h; introv.
  apply eq_term_equals_sym; apply h.
Qed.

Hint Resolve bcequivc_ext_implies_ccequivc_ext : slow.

Lemma ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam {o} :
  forall inh ts lib va (A : @CVTerm o [va]) va' A' vb B (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    bcequivc_ext inh lib [va] A [va'] A'
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a va A) (substc a' vb B) (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a va' A') (substc a' vb B) (eqb lib' x a a' e)).
Proof.
  introv ceq tsp; introv.
  pose proof (tsp _ e a a' e0) as tsp; simpl in *.
  eapply ccequivc_ext_preserves_in_type_sys_props4; eauto; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_in_ext_ext_fam {o} :
  forall {inh} {lib lib'} (ext : @lib_extends o inh lib' lib) (eqa : lib-per(inh,lib,o))
         (F : forall (lib' : library) (x : lib_extends inh lib' lib) (a a' : CTerm) (e : eqa lib' x a a'), Prop),
    in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), F lib' x a a' e)
    -> in_ext_ext inh lib' (fun lib'' x => forall a a' (e : raise_lib_per inh eqa ext lib'' x a a'), F lib'' (lib_extends_trans x ext) a a' e).
Proof.
  introv h; introv.
  eapply h.
Qed.

Lemma lib_extends_preserves_bcequivc_ext {o} :
  forall {inh} {lib lib'} (x : @lib_extends o inh lib' lib) v B v' B',
    bcequivc_ext inh lib [v] B [v'] B'
    -> bcequivc_ext inh lib' [v] B [v'] B'.
Proof.
  introv x ceq ext.
  eapply ceq; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_bcequivc_ext : slow.

Lemma bcequivc_sym {o} :
  forall (lib : @library o) v B v' B',
    bcequivc lib [v] B [v'] B'
    -> bcequivc lib [v'] B' [v] B.
Proof.
  introv ceq.
  destruct_cterms.
  unfold bcequivc, bcequiv in *; simpl in *.
  unfold blift in *; exrepnd.
  exists lv nt2 nt1; dands; auto.
  apply olift_cequiv_approx in ceq1; repnd.
  apply olift_approx_cequiv; auto.
Qed.
Hint Resolve bcequivc_sym : slow.

Lemma bcequivc_ext_sym {o} :
  forall inh (lib : @library o) v B v' B',
    bcequivc_ext inh lib [v] B [v'] B'
    -> bcequivc_ext inh lib [v'] B' [v] B.
Proof.
  introv ceq ext.
  pose proof (ceq _ ext) as ceq; simpl in *; spcast; eauto 3 with slow.
Qed.
Hint Resolve bcequivc_ext_sym : slow.

Lemma in_ext_ext_type_sys_props4_sym_eq {o} :
  forall inh (ts : cts(o)) {lib lib'} (x : lib_extends inh lib' lib) A A' (eqa : lib-per(inh,lib,o)) a a',
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a' a.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_sym_eq : slow.

Lemma in_ext_ext_type_sys_props4_trans1_eq {o} :
  forall inh (ts : cts(o)) {lib lib'} (x : lib_extends inh lib' lib) A A' (eqa : lib-per(inh,lib,o)) a a',
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a a.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
  eapply tet;[eauto|]; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_trans1_eq : slow.

Lemma in_ext_ext_type_sys_props4_trans2_eq {o} :
  forall inh (ts : cts(o)) {lib lib'} (x : lib_extends inh lib' lib) A A' (eqa : lib-per(inh,lib,o)) a a',
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a' a'.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
  eapply tet;[|eauto]; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_trans2_eq : slow.

Lemma in_ext_ext_type_sys_props4_fam_sym {o} :
  forall inh (ts : cts(o)) lib A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e)).
Proof.
  introv tsa tsb; repeat introv.
  pose proof (tsb lib' e) as tcsp; simpl in *.
  apply type_sys_props4_sym; auto.
  apply type_sys_props4_eqb_comm; auto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_type_sys_props_type_value_respecting_trans1 {o} :
  forall inh (ts : cts(o)) lib A A1 A2 C (eqa eqa1 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> ccequivc_ext inh lib A A1
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa1 lib' x)).
Proof.
  introv tsp ceq tsts; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply tyvrt1; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_type_sys_props_type_value_respecting_trans2 {o} :
  forall inh (ts : cts(o)) lib A A1 A2 C (eqa eqa1 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> ccequivc_ext inh lib A A1
    -> in_ext_ext inh lib (fun lib' x => ts lib' A2 A1 (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa1 lib' x)).
Proof.
  introv tsp ceq tsts; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply tyvrt1; eauto; eauto 3 with slow.
Qed.

Lemma in_ext_ext_type_sys_props4_in_ext_ext_sym {o} :
  forall inh (ts : cts(o)) lib A A' B (eqa eqa1 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A B (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' B A (eqa1 lib' x)).
Proof.
  introv tsp tsts; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (tsts _ e) as tsts.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_in_ext_ext_sym_rev {o} :
  forall inh (ts : cts(o)) lib A A' B (eqa eqa1 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' B A (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A B (eqa1 lib' x)).
Proof.
  introv tsp tsts; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (tsts _ e) as tsts.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1 {o} :
  forall inh (ts : cts(o)) lib A A' A1 A2 (eqa eqa1 eqa2 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa2 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A2 (eqa1 lib' x)).
Proof.
  introv tsp ts1 ts2; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (ts1 _ e) as ts1.
  pose proof (ts2 _ e) as ts2.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (dum A A1 A2 (eqa1 lib' e) (eqa2 lib' e)) as q.
  repeat (autodimp q hyp); tcsp.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2 {o} :
  forall inh (ts : cts(o)) lib A A' A1 A2 (eqa eqa1 eqa2 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa2 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A2 (eqa2 lib' x)).
Proof.
  introv tsp ts1 ts2; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (ts1 _ e) as ts1.
  pose proof (ts2 _ e) as ts2.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (dum A A1 A2 (eqa1 lib' e) (eqa2 lib' e)) as q.
  repeat (autodimp q hyp); tcsp.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3 {o} :
  forall inh (ts : cts(o)) lib A A' A1 A2 (eqa eqa1 eqa2 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A' A (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa2 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A2 (eqa1 lib' x)).
Proof.
  introv tsp ts1 ts2; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (ts1 _ e) as ts1.
  pose proof (ts2 _ e) as ts2.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (dum A A1 A2 (eqa1 lib' e) (eqa2 lib' e)) as q.
  repeat (autodimp q hyp); tcsp.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4 {o} :
  forall inh (ts : cts(o)) lib A A' A1 A2 (eqa eqa1 eqa2 : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A' A (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A (eqa1 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A A2 (eqa2 lib' x))
    -> in_ext_ext inh lib (fun lib' x => ts lib' A1 A2 (eqa2 lib' x)).
Proof.
  introv tsp ts1 ts2; introv.
  pose proof (tsp _ e) as tsp.
  pose proof (ts1 _ e) as ts1.
  pose proof (ts2 _ e) as ts2.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (dum A A1 A2 (eqa1 lib' e) (eqa2 lib' e)) as q.
  repeat (autodimp q hyp); tcsp.
Qed.

Lemma in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 {o} :
  forall inh (ts : cts(o)) {lib lib'} (ext : lib_extends inh lib' lib) A' A B C (eqa : lib-per(inh,lib,o)) (eqa1 : lib-per(inh,lib',o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccequivc_ext inh lib' A A'
    -> in_ext_ext inh lib' (fun lib'' x => ts lib'' A' C (eqa1 lib'' x))
    -> in_ext_ext inh lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext))).
Proof.
  introv h ceq w; introv.
  pose proof (w _ e) as w.
  pose proof (h _ (lib_extends_trans e ext)) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' C (eqa1 lib'0 e)) as xx; repeat (autodimp xx hyp); eauto 3 with slow.
  apply uv in xx.
  apply eq_term_equals_sym;auto.
Qed.
