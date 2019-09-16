Require Export per_props_fam.

Lemma type_family_ext_nuprl_uniquely_valued_eqas {o} :
  forall (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons nuprl lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons nuprl lib (Cons A v B) (Cons C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv inj tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb2.
  apply constructor_inj_implies_ext in tfa0; auto.
  apply constructor_inj_implies_ext in tfa2; auto.
  apply constructor_inj_implies_ext in tfb0; auto.
  apply constructor_inj_implies_ext in tfb2; auto.
  repnd.

  introv.
  pose proof (tfa3 _ e) as tfa3.
  pose proof (tfb3 _ e) as tfb3.
  simpl in *.
  apply nuprl_refl in tfa3.
  apply nuprl_refl in tfb3.
  eapply nuprl_uniquely_valued; eauto.

  assert (ccequivc_ext lib' A1 A0) as ceq1 by (eauto 4 with slow).
  eapply nuprl_value_respecting_left;[|apply ccequivc_ext_sym;eauto].
  eapply nuprl_value_respecting_right;[|apply ccequivc_ext_sym;eauto].
  auto.
Qed.

Lemma type_family_ext_nuprl_uniquely_valued_eqbs {o} :
  forall (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons nuprl lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons nuprl lib (Cons A v B) (Cons C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e1 : eqa1 lib' x a a') (e2 : eqa2 lib' x a a'),
                           (eqb1 lib' x a a' e1) <=2=> (eqb2 lib' x a a' e2)).
Proof.
  introv inj tfa tfb.
  dup tfa as eqas.
  eapply type_family_ext_nuprl_uniquely_valued_eqas in eqas; try exact tfb; auto.

  unfold type_family_ext in *; exrepnd; spcast.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb2.
  apply constructor_inj_implies_ext in tfa0; auto.
  apply constructor_inj_implies_ext in tfa2; auto.
  apply constructor_inj_implies_ext in tfb0; auto.
  apply constructor_inj_implies_ext in tfb2; auto.
  repnd.

  introv.
  pose proof (tfa1 _ e _ _ e1) as tfa1.
  pose proof (tfb1 _ e _ _ e2) as tfb1.
  simpl in *.
  apply nuprl_refl in tfa1.
  apply nuprl_refl in tfb1.
  eapply nuprl_uniquely_valued; eauto.

  assert (ccequivc_ext lib' (substc a v0 B0) (substc a v1 B1)) as ceq1.
  { apply bcequivc_ext1.
    eapply bcequivc_ext_trans;[|eapply lib_extends_preserves_bcequivc_ext; eauto].
    eapply bcequivc_ext_sym; eapply lib_extends_preserves_bcequivc_ext; eauto. }
  eapply nuprl_value_respecting_left;[|eauto].
  eapply nuprl_value_respecting_right;[|eauto].
  auto.
Qed.

Lemma type_family_ext_nuprli_uniquely_valued_eqas {o} :
  forall i (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons (nuprli i) lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons (nuprli i) lib (Cons A v B) (Cons C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv inj tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb2.
  apply constructor_inj_implies_ext in tfa0; auto.
  apply constructor_inj_implies_ext in tfa2; auto.
  apply constructor_inj_implies_ext in tfb0; auto.
  apply constructor_inj_implies_ext in tfb2; auto.
  repnd.

  introv.
  pose proof (tfa3 _ e) as tfa3.
  pose proof (tfb3 _ e) as tfb3.
  simpl in *.
  apply nuprli_refl in tfa3.
  apply nuprli_refl in tfb3.
  eapply (nuprli_uniquely_valued _ i i); eauto.

  assert (ccequivc_ext lib' A1 A0) as ceq1 by (eauto 4 with slow).
  eapply nuprli_value_respecting_left;[|apply ccequivc_ext_sym;eauto].
  eapply nuprli_value_respecting_right;[|apply ccequivc_ext_sym;eauto].
  auto.
Qed.

Lemma type_family_ext_nuprli_uniquely_valued_eqbs {o} :
  forall i (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons (nuprli i) lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons (nuprli i) lib (Cons A v B) (Cons C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e1 : eqa1 lib' x a a') (e2 : eqa2 lib' x a a'),
                           (eqb1 lib' x a a' e1) <=2=> (eqb2 lib' x a a' e2)).
Proof.
  introv inj tfa tfb.
  dup tfa as eqas.
  eapply type_family_ext_nuprli_uniquely_valued_eqas in eqas; try exact tfb; auto.

  unfold type_family_ext in *; exrepnd; spcast.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfa2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in tfb2.
  apply constructor_inj_implies_ext in tfa0; auto.
  apply constructor_inj_implies_ext in tfa2; auto.
  apply constructor_inj_implies_ext in tfb0; auto.
  apply constructor_inj_implies_ext in tfb2; auto.
  repnd.

  introv.
  pose proof (tfa1 _ e _ _ e1) as tfa1.
  pose proof (tfb1 _ e _ _ e2) as tfb1.
  simpl in *.
  apply nuprli_refl in tfa1.
  apply nuprli_refl in tfb1.
  eapply (nuprli_uniquely_valued _ i i); eauto.

  assert (ccequivc_ext lib' (substc a v0 B0) (substc a v1 B1)) as ceq1.
  { apply bcequivc_ext1.
    eapply bcequivc_ext_trans;[|eapply lib_extends_preserves_bcequivc_ext; eauto].
    eapply bcequivc_ext_sym; eapply lib_extends_preserves_bcequivc_ext; eauto. }
  eapply nuprli_value_respecting_left;[|eauto].
  eapply nuprli_value_respecting_right;[|eauto].
  auto.
Qed.

Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa {o} :
  forall {lib lib'} {bar : @BarLib o lib} {feqa : bar-and-fam-per(lib,bar,o)}
         {A v B C w D}
         {Cons}
         (inj : constructor_inj Cons)
         (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext Cons nuprl lib2 (Cons A v B) (Cons C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
         {x : lib_extends lib' lib}
         {a a'}
         (lib1 : library)
         (br : bar_lib_bar bar lib1)
         (ext : lib_extends lib' lib1)
         (y : lib_extends lib' lib),
    (bar_and_fam_per2lib_per feqa) lib' x a a'
    -> (lpaf_eqa (feqa lib1 br lib' ext y)) lib' (lib_extends_refl lib') a a'.
Proof.
  introv inj F h; simpl in *; exrepnd.
  pose proof (F _ br0 _ ext0 x0) as q1.
  pose proof (F _ br _ ext y) as q2.
  eapply type_family_ext_nuprl_uniquely_valued_eqas in q1; try exact q2; auto.
  simpl in *.
  pose proof (q1 _ (lib_extends_refl lib')) as q1; simpl in *.
  apply q1; auto.
Qed.

Definition bar_and_fam_per2lib_per_fam {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o))
           {A v B C w D}
           {Cons}
           (cond : constructor_inj Cons)
           (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext Cons nuprl lib2 (Cons A v B) (Cons C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
  : lib-per-fam(lib,bar_and_fam_per2lib_per(feqa),o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) a a' (e : bar_and_fam_per2lib_per(feqa) lib' x a a') t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {y : lib_extends lib' lib
            , lpaf_eqb
                (feqa lib1 br lib' ext y)
                lib'
                (lib_extends_refl lib')
                a a'
                (bar_and_fam_per2lib_per_implies_lpaf_eqa cond F lib1 br ext y e)
                t1 t2}}}}).

  repeat introv.
  split; introv h; exrepnd.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
Defined.

Definition FunDepEqaFam {o} {lib} {Flib : @FunLibExt o lib} (Feqa : FunDepEqa Flib) :=
  forall lib1 (ext1 : lib_extends lib1 lib)
         lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1))
         (z : lib_extends lib2 lib),
    lib-per-fam(lib2,Feqa lib1 ext1 lib2 ext2 z,o).

Lemma in_open_bar_eqa_fam_choice {o} :
  forall (lib : @library o)
         (Flib : FunLibExt lib)
         (Feqa : FunDepEqa Flib)
         (G : forall lib1 (ext1 : lib_extends lib1 lib)
                     lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1))
                     (z : lib_extends lib2 lib)
                     (eqb : lib-per-fam(lib2,Feqa lib1 ext1 lib2 ext2 z,o)), Prop),
    in_ext_ext
      lib
      (fun lib1 (ext1 : lib_extends lib1 lib) =>
         in_ext_ext
           (Flib lib1 ext1)
           (fun lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1)) =>
              forall (z : lib_extends lib2 lib),
              exists (eqb : lib-per-fam(lib2,Feqa lib1 ext1 lib2 ext2 z,o)),
                G lib1 ext1 lib2 ext2 z eqb))
    -> exists (Feqb : FunDepEqaFam Feqa),
      in_ext_ext
        lib
        (fun lib1 (ext1 : lib_extends lib1 lib) =>
           in_ext_ext
             (Flib lib1 ext1)
             (fun lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1)) =>
                forall (z : lib_extends lib2 lib),
                  G lib1 ext1 lib2 ext2 z (Feqb lib1 ext1 lib2 ext2 z))).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (DepLibExt lib Flib)
                (fun d => lib-per-fam(lib_ext_lib2 d,Feqa (lib_ext_lib1 d) (lib_ext_ext1 d) (lib_ext_lib2 d) (lib_ext_ext2 d) (lib_ext_extz d),o))
                (fun d eqb =>
                   G (lib_ext_lib1 d) (lib_ext_ext1 d)
                     (lib_ext_lib2 d) (lib_ext_ext2 d)
                     (lib_ext_extz d)
                     eqb)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x as [lib1 ext1 lib2 ext2 extz]; simpl in *.
    pose proof (h lib1 ext1 lib2 ext2 extz) as h; exrepnd.
    exists eqb; auto. }

  exrepnd.
  exists (fun lib1 ext1 lib2 ext2 z => f (MkDepLibExt lib1 ext1 lib2 ext2 z)).
  repeat introv.
  apply (C0 (MkDepLibExt lib' e lib'0 e0 z)).
Qed.

Definition fun_lib_dep_eqa {o}
           {lib   : @library o}
           {Flib  : FunLibExt lib}
           (Feqa  : FunDepEqa Flib)
  : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {ext1 : lib_extends lib1 lib
            , {lib2 : library
            , {ext2 : lib_extends lib2 (Flib lib1 ext1)
            , {extz : lib_extends lib2 lib
            , {z : lib_extends lib' lib2
            , Feqa lib1 ext1 lib2 ext2 extz lib' z t1 t2 }}}}}} ).
  introv; tcsp.
Defined.

Definition FunDeqEqa_cond
           {o} {lib : @library o}
           {Flib  : FunLibExt lib}
           (Feqa  : FunDepEqa Flib) :=
  forall lib1a ext1a lib2a ext2a extza
         lib1b ext1b lib2b ext2b extzb
         lib' xta xtb,
    (Feqa lib1a ext1a lib2a ext2a extza lib' xta)
    <=2=>
    (Feqa lib1b ext1b lib2b ext2b extzb lib' xtb).

Lemma fun_lib_dep_eqa_to {o} {lib : @library o}
      {Flib : FunLibExt lib}
      {Feqa : FunDepEqa Flib}
      (cond : FunDeqEqa_cond Feqa)
      {lib'}
      {x : lib_extends lib' lib}
      {a a'}
      (e    : fun_lib_dep_eqa Feqa lib' x a a')
      (lib1 : library)
      (ext1 : lib_extends lib1 lib)
      (lib2 : library)
      (ext2 : lib_extends lib2 (Flib lib1 ext1))
      (extz : lib_extends lib2 lib)
      (z    : lib_extends lib' lib2) :
  Feqa lib1 ext1 lib2 ext2 extz lib' z a a'.
Proof.
  unfold fun_lib_dep_eqa in *; simpl in *; exrepnd.
  eapply cond; eauto.
Qed.

Definition fun_lib_dep_eqb {o}
           {lib  : @library o}
           {Flib : FunLibExt lib}
           {Feqa : FunDepEqa Flib}
           (cond : FunDeqEqa_cond Feqa)
           (Feqb : FunDepEqaFam Feqa)
  : lib-per-fam(lib,fun_lib_dep_eqa Feqa,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) a a' (e : fun_lib_dep_eqa Feqa lib' x a a') t1 t2 =>
            {lib1 : library
            , {ext1 : lib_extends lib1 lib
            , {lib2 : library
            , {ext2 : lib_extends lib2 (Flib lib1 ext1)
            , {extz : lib_extends lib2 lib
            , {z : lib_extends lib' lib2
            , Feqb lib1 ext1 lib2 ext2 extz lib' z a a'
                   (fun_lib_dep_eqa_to cond e lib1 ext1 lib2 ext2 extz z)
                   t1 t2 }}}}}} ).
  repeat introv; tcsp.
  split; introv h; exrepnd;
    exists lib1 ext1 lib2 ext2 extz z; simpl in *;
      eapply lib_per_fam_cond; eauto.
Defined.

Lemma nuprl_type_family_ext_implies_FunDeqEq_cond {o} :
  forall (lib : @library o)
         (Flib : FunLibExt lib)
         (Feqa : FunDepEqa Flib)
         (Feqb : FunDepEqaFam Feqa)
         Cons
         (cond : constructor_inj Cons)
         A v B
         C w D
         (G : forall lib1 (ext1 : lib_extends lib1 lib)
                     lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1))
                     (z : lib_extends lib2 lib), Prop),
    in_ext_ext
      lib
      (fun lib1 ext1 =>
         in_ext_ext
           (Flib lib1 ext1)
           (fun lib2 ext2 =>
              forall (z : lib_extends lib2 lib),
                type_family_ext
                  Cons nuprl lib2 (Cons A v B) (Cons C w D)
                  (Feqa lib1 ext1 lib2 ext2 z)
                  (Feqb lib1 ext1 lib2 ext2 z)
                  # G lib1 ext1 lib2 ext2 z))
    -> FunDeqEqa_cond Feqa.
Proof.
  introv cond h; repeat introv.
  pose proof (h _ ext1a _ ext2a extza) as u; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ xta) in u0.
  pose proof (h _ ext1b _ ext2b extzb) as z; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ xtb) in z0.
  clear h.
  eapply @type_family_ext_nuprl_uniquely_valued_eqas in u0; try exact z0; auto; simpl in *.
  pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
  unfold raise_ext_per in u0; simpl in *.
  split; intro h.
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
Qed.

Lemma nuprli_type_family_ext_implies_FunDeqEq_cond {o} :
  forall (lib : @library o)
         (Flib : FunLibExt lib)
         (Feqa : FunDepEqa Flib)
         (Feqb : FunDepEqaFam Feqa)
         Cons
         (cond : constructor_inj Cons)
         i
         A v B
         C w D
         (G : forall lib1 (ext1 : lib_extends lib1 lib)
                     lib2 (ext2 : lib_extends lib2 (Flib lib1 ext1))
                     (z : lib_extends lib2 lib), Prop),
    in_ext_ext
      lib
      (fun lib1 ext1 =>
         in_ext_ext
           (Flib lib1 ext1)
           (fun lib2 ext2 =>
              forall (z : lib_extends lib2 lib),
                type_family_ext
                  Cons (nuprli i) lib2 (Cons A v B) (Cons C w D)
                  (Feqa lib1 ext1 lib2 ext2 z)
                  (Feqb lib1 ext1 lib2 ext2 z)
                  # G lib1 ext1 lib2 ext2 z))
    -> FunDeqEqa_cond Feqa.
Proof.
  introv cond h; repeat introv.
  pose proof (h _ ext1a _ ext2a extza) as u; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ xta) in u0.
  pose proof (h _ ext1b _ ext2b extzb) as z; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ xtb) in z0.
  clear h.
  eapply @type_family_ext_nuprli_uniquely_valued_eqas in u0; try exact z0; auto; simpl in *.
  pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
  unfold raise_ext_per in u0; simpl in *.
  split; intro h.
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
Qed.
