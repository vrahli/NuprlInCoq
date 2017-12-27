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



Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.
Require Export nuprl_mon_func.
Require Export local.



Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 {o} :
  forall (ts : cts(o)) {lib lib'} (ext : lib_extends lib' lib) A B C (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A C (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext))).
Proof.
  introv h w; introv.
  pose proof (w _ e) as w.
  pose proof (h _ (lib_extends_trans e ext)) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in w.
  apply eq_term_equals_sym;auto.
Qed.

Lemma in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam2 {o} :
  forall (ts : cts(o)) {lib lib'}
         (ext : lib_extends lib' lib)
         va A vb B vc C
         (eqa : lib-per(lib,o))
         (eqa1 eqa2 : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa,o))
         (eqb1 : lib-per-fam(lib',eqa1,o))
         (eqb2 : lib-per-fam(lib',eqa2,o)),
    in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a va A) (substc a' vb B) (eqb lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (e : eqa1 lib' x a a'), ts lib' (substc a va A) (substc a' vc C) (eqb1 lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (e : eqa2 lib' x a a'), ts lib' (substc a va A) (substc a' vc C) (eqb2 lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (u : eqa1 lib' x a a') (v : eqa2 lib' x a a'), (eqb1 lib' x a a' u) <=2=> (eqb2 lib' x a a' v)).
Proof.
  introv eqas h w q; introv.

  dup u as z.
  apply eqas in z.

  pose proof (w _ e a a' u) as w.
  pose proof (q _ e a a' v) as q.
  pose proof (h _ (lib_extends_trans e ext) a a' z) as h.
  simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in w.
  apply uv in q.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma implies_in_ext_ext_raise_ext_per_fam {o} :
  forall (F : forall (lib : library), CTerm -> CTerm -> per -> Prop) {lib lib'} (x : lib_extends lib' lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), F lib' a a' (eqb lib' x a a' e))
    -> in_ext_ext lib' (fun lib'' y => forall a a' (e : raise_lib_per eqa x lib'' y a a'), F lib'' a a' (raise_lib_per_fam eqb x lib'' y a a' e)).
Proof.
  introv h; introv.
  eapply h.
Qed.
Hint Resolve implies_in_ext_ext_raise_ext_per_fam : slow.

Lemma in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5 {o} :
  forall (ts : cts(o)) {lib lib'} (ext : lib_extends lib' lib) A B C (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B A (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' C A (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext))).
Proof.
  introv h w; introv.
  pose proof (w _ e) as w.
  pose proof (h _ (lib_extends_trans e ext)) as h.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs in tygt.
  pose proof (dum A C B) as q.
  eapply q in w; eauto; repnd.
  apply eq_term_equals_sym;auto.
  eapply uv.
  apply tygs; eauto.
Qed.

Lemma in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam3 {o} :
  forall (ts : cts(o)) {lib lib'}
         (ext : lib_extends lib' lib)
         va A vb B vc C
         (eqa : lib-per(lib,o))
         (eqa1 eqa2 : lib-per(lib',o))
         (eqb : lib-per-fam(lib,eqa,o))
         (eqb1 : lib-per-fam(lib',eqa1,o))
         (eqb2 : lib-per-fam(lib',eqa2,o)),
    in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa lib'' (lib_extends_trans x ext)))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a vb B) (substc a' va A) (eqb lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (e : eqa1 lib' x a a'), ts lib' (substc a vc C) (substc a' va A) (eqb1 lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (e : eqa2 lib' x a a'), ts lib' (substc a vc C) (substc a' va A) (eqb2 lib' x a a' e))
    -> in_ext_ext lib' (fun lib' x => forall a a' (u : eqa1 lib' x a a') (v : eqa2 lib' x a a'), (eqb1 lib' x a a' u) <=2=> (eqb2 lib' x a a' v)).
Proof.
  introv eqas h w q; introv.

  dup u as z.
  apply eqas in z.

  pose proof (w _ e a a' u) as w.
  pose proof (q _ e a a' v) as q.
  pose proof (h _ (lib_extends_trans e ext) a a' z) as h.
  simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  apply tygs in tygt.
  pose proof (dum (substc a' va A) (substc a vc C) (substc a vb B)) as qa.
  eapply qa in w; eauto; repnd.
  eapply qa in q; eauto; repnd.

  apply tygs in w0.
  apply uv in w0.
  apply tygs in q0.
  apply uv in q0.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.
