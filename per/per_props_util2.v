Require Export per_props_util.

Hint Resolve meta_type_monotone : slow.

Lemma in_ext_ext_Flib_implies_in_open_bar_ext {o} :
  forall (lib : @library o) (Flib : FunLibExt lib)
         (F : forall lib1 (ext1 : lib_extends lib1 lib), Prop)
         (G : forall lib1 (ext1 : lib_extends lib1 lib)
                     lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1))
                     (z : lib_extends lib2 lib), Prop),
    in_ext_ext
      lib
      (fun lib1 ext1 =>
         in_ext_ext
           (Flib lib1 ext1)
           (fun lib2 ext2 =>
              forall z : lib_extends lib2 lib,
                G lib1 ext1 lib2 ext2 z
                -> F lib2 z))
    -> in_ext_ext
         lib
         (fun lib1 ext1 =>
            in_ext_ext
              (Flib lib1 ext1)
              (fun lib2 ext2 =>
                 forall z : lib_extends lib2 lib,
                   G lib1 ext1 lib2 ext2 z))
    -> in_open_bar_ext lib F.
Proof.
  introv imp h ext.
  pose proof (h _ ext) as h; simpl in *.
  assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
  exists (Flib lib' ext) xta.
  introv xtb; introv.
  pose proof (h _ xtb z) as h.
  eapply imp; eauto.
Qed.

Lemma lib_extends_preserves_equorsq {o} :
  forall (lib1 lib2 : @library o) a b A,
    lib_extends lib2 lib1
    -> equorsq lib1 a b A
    -> equorsq lib2 a b A.
Proof.
  introv ext h.
  unfold equorsq in *; repndors; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_equorsq : slow.
