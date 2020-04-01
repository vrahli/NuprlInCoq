Require Export per_props_fam.

Lemma type_family_ext_nuprl_uniquely_valued_eqas {o} :
  forall (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons nuprl uk lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons nuprl uk lib (Cons A v B) (Cons C w D) eqa2 eqb2
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
  pose proof (tfa4 _ e) as tfa4.
  pose proof (tfb4 _ e) as tfb4.
  simpl in *.
  apply nuprl_refl in tfa4.
  apply nuprl_refl in tfb4.
  eapply nuprl_uniquely_valued; eauto.

  assert (ccequivc_ext lib' A1 A0) as ceq1 by (eauto 4 with slow).
  eapply nuprl_value_respecting_left;[|apply ccequivc_ext_sym;eauto].
  eapply nuprl_value_respecting_right;[|apply ccequivc_ext_sym;eauto].
  auto.
Qed.

Lemma type_family_ext_nuprl_uniquely_valued_eqbs {o} :
  forall (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons nuprl uk lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons nuprl uk lib (Cons A v B) (Cons C w D) eqa2 eqb2
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
         uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons (nuprli i) uk lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons (nuprli i) uk lib (Cons A v B) (Cons C w D) eqa2 eqb2
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
  pose proof (tfa4 _ e) as tfa4.
  pose proof (tfb4 _ e) as tfb4.
  simpl in *.
  apply nuprli_refl in tfa4.
  apply nuprli_refl in tfb4.
  eapply (nuprli_uniquely_valued _ _ i i); eauto.

  assert (ccequivc_ext lib' A1 A0) as ceq1 by (eauto 4 with slow).
  eapply nuprli_value_respecting_left;[|apply ccequivc_ext_sym;eauto].
  eapply nuprli_value_respecting_right;[|apply ccequivc_ext_sym;eauto].
  auto.
Qed.

Lemma type_family_ext_nuprli_uniquely_valued_eqbs {o} :
  forall i (Cons : forall (A : @CTerm o) v, @CVTerm o [v] -> @CTerm o)
         uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o))
         (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    constructor_inj Cons
    -> type_family_ext Cons (nuprli i) uk lib (Cons A v B) (Cons C w D) eqa1 eqb1
    -> type_family_ext Cons (nuprli i) uk lib (Cons A v B) (Cons C w D) eqa2 eqb2
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
  eapply (nuprli_uniquely_valued _ _ i i); eauto.

  assert (ccequivc_ext lib' (substc a v0 B0) (substc a v1 B1)) as ceq1.
  { apply bcequivc_ext1.
    eapply bcequivc_ext_trans;[|eapply lib_extends_preserves_bcequivc_ext; eauto].
    eapply bcequivc_ext_sym; eapply lib_extends_preserves_bcequivc_ext; eauto. }
  eapply nuprli_value_respecting_left;[|eauto].
  eapply nuprli_value_respecting_right;[|eauto].
  auto.
Qed.

(*Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa {o} :
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
Qed.*)

(*Definition bar_and_fam_per2lib_per_fam {o}
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
Defined.*)

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
  forall uk (lib : @library o)
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
                  Cons nuprl uk lib2 (Cons A v B) (Cons C w D)
                  (Feqa lib1 ext1 lib2 ext2 z)
                  (Feqb lib1 ext1 lib2 ext2 z)
                  # G lib1 ext1 lib2 ext2 z))
    -> FunDeqEqa_cond Feqa.
Proof.
  introv cond h; repeat introv.
  pose proof (h _ ext1a _ ext2a extza) as u; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ xta) in u0.
  pose proof (h _ ext1b _ ext2b extzb) as z; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ xtb) in z0.
  clear h.
  eapply @type_family_ext_nuprl_uniquely_valued_eqas in u0; try exact z0; auto; simpl in *.
  pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
  unfold raise_ext_per in u0; simpl in *.
  split; intro h.
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
Qed.

Lemma nuprli_type_family_ext_implies_FunDeqEq_cond {o} :
  forall uk (lib : @library o)
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
                  Cons (nuprli i) uk lib2 (Cons A v B) (Cons C w D)
                  (Feqa lib1 ext1 lib2 ext2 z)
                  (Feqb lib1 ext1 lib2 ext2 z)
                  # G lib1 ext1 lib2 ext2 z))
    -> FunDeqEqa_cond Feqa.
Proof.
  introv cond h; repeat introv.
  pose proof (h _ ext1a _ ext2a extza) as u; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ xta) in u0.
  pose proof (h _ ext1b _ ext2b extzb) as z; simpl in *; repnd.
  apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ xtb) in z0.
  clear h.
  eapply @type_family_ext_nuprli_uniquely_valued_eqas in u0; try exact z0; auto; simpl in *.
  pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
  unfold raise_ext_per in u0; simpl in *.
  split; intro h.
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
  { eapply lib_per_cond; apply u0; eapply lib_per_cond; exact h. }
Qed.

Definition equality_swap_invariant {o} lib (A : @CTerm o) v B :=
  forall a sw,
    in_ext
      lib
      (fun lib' =>
         member uk1 lib' a A
         -> ccequivc_ext_bar
              lib'
              (substc (mkc_swap_cs sw a) v B)
              (substc a v B)).

Definition equality_swap_invariant_cond {o} uk lib (A : @CTerm o) v B v' B' :=
  match uk with
  | uk0 => True
  | uk1 =>
    equality_swap_invariant lib A v B
    # equality_swap_invariant lib A v' B'
  end.

Lemma is_swap_invariant_nuprl_imp {o} :
  forall {lib} (eqa : lib-per(lib,o)) A1 A2 v B,
    in_open_bar_ext lib (fun lib' x => nuprl uk1 lib' A1 A2 (eqa lib' x))
    -> is_swap_invariant eqa v B
    -> equality_swap_invariant lib A1 v B.
Proof.
  introv h q ext mem.
  apply in_open_bar_ext_in_open_bar.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ ext) in h; simpl in h.
  eapply in_open_bar_ext_pres; eauto; clear h; introv h.
  eapply member_monotone in mem; eauto.
  pose proof (q a sw _ (lib_extends_trans e ext)) as q; simpl in q; autodimp q hyp.
  eapply equality_eq; eauto; apply nuprl_refl in h; auto.
Qed.
Hint Resolve is_swap_invariant_nuprl_imp : slow.

Lemma is_swap_invariant_cond_nuprl_imp {o} :
  forall uk {lib} (eqa : lib-per(lib,o)) A1 A2 v B v' B',
    in_open_bar_ext lib (fun lib' x => nuprl uk lib' A1 A2 (eqa lib' x))
    -> is_swap_invariant_cond uk eqa v B v' B'
    -> equality_swap_invariant_cond uk lib A1 v B v' B'.
Proof.
  introv h q; destruct uk; simpl in *; tcsp; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve is_swap_invariant_cond_nuprl_imp : slow.

Lemma is_swap_invariant_cond_nuprli_imp {o} :
  forall i uk {lib} (eqa : lib-per(lib,o)) A1 A2 v B v' B',
    in_open_bar_ext lib (fun lib' x => nuprli i uk lib' A1 A2 (eqa lib' x))
    -> is_swap_invariant_cond uk eqa v B v' B'
    -> equality_swap_invariant_cond uk lib A1 v B v' B'.
Proof.
  introv h q; eapply is_swap_invariant_cond_nuprl_imp; eauto.
  eapply in_open_bar_ext_pres; eauto; clear h; introv h; eauto 3 with slow.
Qed.
Hint Resolve is_swap_invariant_cond_nuprli_imp : slow.

Lemma equality_swap_invariant_nuprl_imp {o} :
  forall {lib} (eqa : lib-per(lib,o)) A1 A2 v B,
    in_ext_ext lib (fun lib' x => nuprl uk1 lib' A1 A2 (eqa lib' x))
    -> equality_swap_invariant lib A1 v B
    -> is_swap_invariant eqa v B.
Proof.
  introv h q mem.
  pose proof (q a sw _ e) as q; simpl in q; autodimp q hyp;[].
  eapply equality_eq in mem; eauto.
  pose proof (h _ e) as h; simpl in h; apply nuprl_refl in h; auto.
Qed.
Hint Resolve equality_swap_invariant_nuprl_imp : slow.

Lemma equality_swap_invariant_cond_nuprl_imp {o} :
  forall uk {lib} (eqa : lib-per(lib,o)) A1 A2 v B v' B',
    in_ext_ext lib (fun lib' x => nuprl uk lib' A1 A2 (eqa lib' x))
    -> equality_swap_invariant_cond uk lib A1 v B v' B'
    -> is_swap_invariant_cond uk eqa v B v' B'.
Proof.
  introv h q; destruct uk; simpl in *; tcsp; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_swap_invariant_cond_nuprl_imp : slow.

Lemma equality_swap_invariant_cond_nuprli_imp {o} :
  forall i uk {lib} (eqa : lib-per(lib,o)) A1 A2 v B v' B',
    in_ext_ext lib (fun lib' x => nuprli i uk lib' A1 A2 (eqa lib' x))
    -> equality_swap_invariant_cond uk lib A1 v B v' B'
    -> is_swap_invariant_cond uk eqa v B v' B'.
Proof.
  introv h q; eapply equality_swap_invariant_cond_nuprl_imp; eauto.
  introv; pose proof (h _ e) as h; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve equality_swap_invariant_cond_nuprli_imp : slow.

Lemma if_in_open_bar_equality_swap_invariant {o} :
  forall lib (A : @CTerm o) v B,
    in_open_bar lib (fun lib' => equality_swap_invariant lib' A v B)
    -> equality_swap_invariant lib A v B.
Proof.
  introv h ext mem.
  apply in_open_bar_ext_in_open_bar.
  apply (lib_extends_preserves_in_open_bar _ _ _ ext) in h; simpl in h.
  eapply in_open_bar_ext_comb2; eauto; clear h.
  apply in_ext_ext_implies_in_open_bar_ext; introv ext' h.
  apply h; eauto 3 with slow.
Qed.

Lemma in_open_bar_prod {o} :
  forall lib (F G : @library o -> Prop),
    in_open_bar lib (fun lib => F lib # G lib)
    <=> (in_open_bar lib F # in_open_bar lib G).
Proof.
  introv; split.
  { introv h; dands; eapply in_open_bar_pres; eauto; clear h; introv ext h; tcsp. }
  { intro h; repnd; eapply in_open_bar_comb; eauto; clear h.
    eapply in_open_bar_pres; eauto; clear h0; introv ext h q; tcsp. }
Qed.

Lemma if_in_open_bar_equality_swap_invariant_cond {o} :
  forall uk lib (A : @CTerm o) v B v' B',
    in_open_bar lib (fun lib' => equality_swap_invariant_cond uk lib' A v B v' B')
    -> equality_swap_invariant_cond uk lib A v B v' B'.
Proof.
  introv h; destruct uk; simpl in *; tcsp.
  apply in_open_bar_prod in h; repnd.
  dands; apply if_in_open_bar_equality_swap_invariant; auto.
Qed.

Lemma lib_extends_preserves_equality_swap_invariant {o} :
  forall lib lib' (A : @CTerm o) v B,
    lib_extends lib' lib
    -> equality_swap_invariant lib A v B
    -> equality_swap_invariant lib' A v B.
Proof.
  introv ext h xt mem.
  apply h; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_equality_swap_invariant : slow.

Lemma lib_extends_preserves_equality_swap_invariant_cond {o} :
  forall uk lib lib' (A : @CTerm o) v B v' B',
    lib_extends lib' lib
    -> equality_swap_invariant_cond uk lib A v B v' B'
    -> equality_swap_invariant_cond uk lib' A v B v' B'.
Proof.
  introv ext h; destruct uk; simpl in *; tcsp; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_equality_swap_invariant_cond : slow.

Lemma bcequivc_ext_implies_ccequivc_ext_bar {o} :
  forall lib (a b : @CTerm o) v B v' B',
    bcequivc_ext lib [v] B [v'] B'
    -> ccequivc_ext_bar lib (substc a v' B') (substc b v' B')
    -> ccequivc_ext_bar lib (substc a v B) (substc b v B).
Proof.
  introv bceq ceq.
  eapply in_open_bar_pres; eauto; clear ceq; introv ext ceq; eauto 3 with slow.
  eapply lib_extends_preserves_bcequivc_ext in bceq; eauto.
  clear dependent lib.
  eapply ccequivc_ext_trans;[apply bcequivc_ext_implies_ccequivc_ext;eauto|].
  eapply ccequivc_ext_trans;[eauto|].
  apply ccequivc_ext_sym; apply bcequivc_ext_implies_ccequivc_ext;eauto.
Qed.
Hint Resolve bcequivc_ext_implies_ccequivc_ext_bar : slow.

Lemma bcequivc_ext_is_swap_invariant_implies_ccequivc_ext {o} :
  forall sw {lib} (eqa : lib-per(lib,o)) {lib'} (x : lib_extends lib' lib) a v B v' B',
    bcequivc_ext lib' [v] B [v'] B'
    -> is_swap_invariant eqa v' B'
    -> eqa lib' x a a
    -> ccequivc_ext_bar lib' (substc (mkc_swap_cs sw a) v B) (substc a v B).
Proof.
  introv bceq isw h.
  pose proof (isw a sw _ x h) as isw; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve bcequivc_ext_is_swap_invariant_implies_ccequivc_ext : slow.

Lemma ccequivc_ext_bar_refl {o} :
  forall lib (t : @CTerm o),
    ccequivc_ext_bar lib t t.
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_bar_refl : slow.

Lemma equality_swap_invariant_mk_cv {o} :
  forall lib (A : @CTerm o) v B,
    equality_swap_invariant lib A v (mk_cv [v] B).
Proof.
  introv ext h; autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve equality_swap_invariant_mk_cv : slow.

Lemma equality_swap_invariant_cond_mk_cv {o} :
  forall uk lib (A : @CTerm o) v1 B1 v2 B2,
    equality_swap_invariant_cond uk lib A v1 (mk_cv [v1] B1) v2 (mk_cv [v2] B2).
Proof.
  introv; destruct uk; simpl in *; tcsp; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_swap_invariant_cond_mk_cv : slow.

Lemma is_swap_invariant_mk_cv {o} :
  forall lib (eqa : lib-per(lib,o)) v B,
    is_swap_invariant eqa v (mk_cv [v] B).
Proof.
  introv h; autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve is_swap_invariant_mk_cv : slow.

Lemma is_swap_invariant_cond_mk_cv {o} :
  forall uk lib (eqa : lib-per(lib,o)) v1 B1 v2 B2,
    is_swap_invariant_cond uk eqa v1 (mk_cv [v1] B1) v2 (mk_cv [v2] B2).
Proof.
  introv; destruct uk; simpl in *; tcsp; dands; eauto 3 with slow.
Qed.
Hint Resolve is_swap_invariant_cond_mk_cv : slow.

Lemma equality_swap_invariant_cond_uk0 {o} :
  forall lib (A : @CTerm o) v1 B1 v2 B2,
    equality_swap_invariant_cond uk0 lib A v1 B1 v2 B2.
Proof.
  tcsp.
Qed.
Hint Resolve equality_swap_invariant_cond_uk0 : slow.

Lemma is_swap_invariant_cond_uk0 {o} :
  forall lib (eqa : lib-per(lib,o)) v1 B1 v2 B2,
    is_swap_invariant_cond uk0 eqa v1 B1 v2 B2.
Proof.
  tcsp.
Qed.
Hint Resolve is_swap_invariant_cond_uk0 : slow.
