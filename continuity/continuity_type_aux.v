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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export csubst2.
Require Export continuity_defs.
Require Export list.  (* Why?? *)

Lemma alpha_eq_bterm_refl {o} :
  forall (b : @BTerm o),
    alpha_eq_bterm b b.
Proof.
  destruct b as [l t].
  apply alpha_eq_bterm_congr; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_bterm_refl : slow.

Lemma alphaeqbt_vs_nil_refl {o} :
  forall (b : @BTerm o),
    alphaeqbt_vs [] b b.
Proof.
  introv.
  apply alphaeqbt_eq; eauto 3 with slow.
Qed.
Hint Resolve alphaeqbt_vs_nil_refl : slow.

Ltac gen_newvar :=
  match goal with
    | [ |- context[newvarlst ?l] ] => remember (newvarlst l)
    | [ |- context[newvar ?x] ] => remember (newvar x)
  end.

Lemma oneswapvar_eq1 :
  forall a b, oneswapvar a b a = b.
Proof.
  introv.
  unfold oneswapvar; boolvar; sp.
Qed.

Lemma oneswapvar_neq :
  forall a b v, v <> a -> v <> b -> oneswapvar a b v = v.
Proof.
  introv ni1 ni2.
  unfold oneswapvar; boolvar; sp.
Qed.

Lemma newvar_prop2 {p} :
  forall v (t : @NTerm p), LIn v (free_vars t) -> newvar t <> v.
Proof.
  introv i e; subst.
  apply newvar_prop in i; sp.
Qed.
Hint Resolve newvar_prop2 : slow.


Definition agree_upto_b_type {o} vi (b f g : @NTerm o) : NTerm :=
  mk_isect
    (mk_set
       mk_int
       vi
       (mk_member (absolute_value (mk_var vi)) (mk_natk_aux vi b)))
    vi
    (mk_equality
       (mk_apply f (mk_var vi))
       (mk_apply g (mk_var vi))
       mk_int).

Definition continuous_type_aux_aux {o} vb vg vi vf (F f : @NTerm o) :=
  mk_product
    mk_tnat
    vb
    (mk_isect
       int2int
       vg
       (mk_isect
          (agree_upto_b_type
             vi
             (mk_var vb)
             f
             (mk_var vg))
          vf
          (mk_equality
             (mk_apply F f)
             (mk_apply F (mk_var vg))
             mk_int))).


Lemma alphaeq_continuous_type_aux_aux {o} :
  forall vb1 vb2 vg1 vg2 vi1 vi2 vf1 vf2 (F f : @NTerm o),
    closed F
    -> closed f

    -> vi1 <> vb1
    -> vi1 <> vg1
    -> vg1 <> vb1
    -> vf1 <> vg1

    -> vi2 <> vb2
    -> vi2 <> vg2
    -> vg2 <> vb2
    -> vf2 <> vg2

    -> alphaeq
         (continuous_type_aux_aux vb1 vg1 vi1 vf1 F f)
         (continuous_type_aux_aux vb2 vg2 vi2 vf2 F f).
Proof.
  introv clF clf;
  introv ni1 ni2 ni3 ni4 ni5 ni6 ni7 ni8.
  constructor; simpl; auto.
  introv j.
  destruct n;[|destruct n]; try (complete cpx); unfold selectbt; simpl.
  { apply alphaeqbt_eq; auto. }
  pose proof (ex_fresh_var ([vb1,vb2,vg1,vg2,vi1,vi2,vf1,vf2,
                             @newvar o mk_int,
                             @newvar o (mk_less_than (mk_var vi1) (mk_var vb1)),
                             @newvar o (mk_less_than (mk_var vi2) (mk_var vb2))]
                              ++ allvars f
                              ++ allvars F)) as fv; exrepnd.
  allsimpl; allrw not_over_or; repnd; GC.
  apply (aeqbt _ [v]); try (complete (simpl; auto)).
  { apply disjoint_singleton_l; intro k; allsimpl; repndors; subst; tcsp.
    allrw app_nil_r; allrw in_app_iff; allsimpl; repndors; subst; tcsp.
    { allrw in_app_iff; allsimpl; repndors; tcsp. }
    { allrw in_app_iff; allsimpl; repndors; tcsp.
      allrw in_app_iff; allsimpl; repndors; tcsp. }
  }

  simpl.
  allrw oneswapvar_eq1.
  allrw (oneswapvar_neq vb1 v vi1); auto;[].
  allrw (oneswapvar_neq vb1 v vg1); auto;[].
  allrw (oneswapvar_neq vb2 v vi2); auto;[].
  allrw (oneswapvar_neq vb2 v vg2); auto;[].
  repeat (rw (oneswapvar_neq vb1 v (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1))));
          auto; try (apply newvar_prop2; simpl; tcsp);[]);[].
  repeat (rw (oneswapvar_neq vb2 v (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2))));
          auto; try (apply newvar_prop2; simpl; tcsp);[]);[].

  constructor; simpl; tcsp; fold_terms.
  introv i.
  destruct n;[|destruct n]; try (complete cpx); unfold selectbt; simpl;
  eauto 3 with slow;[|].

  { apply alphaeqbt_eq.
    apply alphaeqbt_nilv2.
    apply alphaeq_eq.
    constructor; simpl; auto.
    introv k.
    destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    { apply alphaeqbt_eq; auto. }
    pose proof (ex_fresh_var ([oneswapvar vb1 v (newvar (@mk_int o)),
                               oneswapvar vb2 v (newvar (@mk_int o))])) as fv; exrepnd.
    apply (aeqbt _ [v0]); simpl; auto.
    { apply disjoint_singleton_l; intro k; allsimpl.
      allrw not_over_or; repndors; tcsp. }
    { apply alphaeq_refl. }
  }

  { pose proof (ex_fresh_var ([v, vg1, vi1, vg2, vi2, vb1, vf1, vb2, vf2,
                               oneswapvar vb1 v vf1,
                               oneswapvar vb2 v vf2,
                               oneswapvar vb1 v nvarx,
                               oneswapvar vb2 v nvarx,
                               newvar (mk_less_than (mk_var vi1) (@mk_var o vb1)),
                               newvar (mk_less_than (mk_var vi2) (@mk_var o vb2))
                              ]
                                ++ allvars (cswap [(vb1, v)] f)
                                ++ allvars (cswap [(vb1, v)] F)
                                ++ allvars (cswap [(vb2, v)] f)
                                ++ allvars (cswap [(vb2, v)] F)
                                ++ allvars f
                                ++ allvars F
                             )
               ) as fv; exrepnd.
    allsimpl; allrw not_over_or; repnd; GC.
    apply (aeqbt _ [v0]); allsimpl; tcsp.

    { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp.
      allrw app_nil_r; allrw in_app_iff; allsimpl; allrw not_over_or;
      allrw in_app_iff; allsimpl; repndors; tcsp.
      allrw in_app_iff; allsimpl; repndors; tcsp. }

    allrw oneswapvar_eq1.
    allrw (oneswapvar_neq vg1 v0 vi1); auto;[].
    allrw (oneswapvar_neq vg1 v0 v); auto;[].
    allrw (oneswapvar_neq vg1 v0 vf1); auto;[].
    allrw (oneswapvar_neq vg2 v0 vi2); auto;[].
    allrw (oneswapvar_neq vg2 v0 v); auto;[].
    allrw (oneswapvar_neq vg2 v0 vf2); auto;[].

    constructor; allsimpl; tcsp.
    introv i.
    destruct n;[|destruct n]; try (complete cpx); unfold selectbt; simpl;
    fold_terms;[|].

    { apply alphaeqbt_eq.
      apply alphaeqbt_nilv2.
      apply alphaeq_eq.
      constructor; simpl; auto.
      introv k.
      destruct n;[|destruct n]; cpx; unfold selectbt; simpl;[|].

      { apply alphaeqbt_eq.
        apply alphaeqbt_nilv2.
        apply alphaeq_eq.
        constructor; simpl; auto.
        introv k.
        destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
        { apply alphaeqbt_eq; auto. }

        pose proof (ex_fresh_var ([vi1, vi2, v,
                                   oneswapvar vg1 v0 (oneswapvar vb1 v nvarx),
                                   oneswapvar vg1 v0 (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1))),
                                   oneswapvar vg2 v0 (oneswapvar vb2 v nvarx),
                                   oneswapvar vg2 v0 (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))
                                  ]
                                 )
                   ) as fv; exrepnd.
        allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
        apply (aeqbt _ [v1]); simpl; auto.
        { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }

        allrw oneswapvar_eq1.
        allrw (oneswapvar_neq vi1 v1 v); auto;[].
        allrw (oneswapvar_neq vi2 v1 v); auto;[].

        rw (oneswapvar_neq vi1 v1
                           (oneswapvar vg1 v0
                                       (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1)))));
          tcsp;
          [|complete (unfold oneswapvar; boolvar; tcsp; apply newvar_prop2; simpl; sp)].

        rw (oneswapvar_neq vi2 v1
                           (oneswapvar vg2 v0
                                       (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))));
          tcsp;
          [|complete (unfold oneswapvar; boolvar; tcsp; apply newvar_prop2; simpl; sp)].

        fold_terms.
        constructor; simpl; auto.
        introv k.
        destruct n;[|destruct n;[|destruct n] ]; cpx; unfold selectbt; simpl;
        eauto 3 with slow;[].

        (*
        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.
          constructor; simpl; auto.
          introv p.
          destruct n;[|destruct n;[|destruct n;[|destruct n] ] ]; cpx; unfold selectbt; simpl;
          eauto 3 with slow;[].

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alpha_eq_refl.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }

          { apply alphaeqbt_eq; auto. }

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            constructor; simpl; auto.
            introv p.
            destruct n; cpx; unfold selectbt; simpl; tcsp.
            apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }
        }

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.
          constructor; simpl; auto.
          introv p.
          destruct n;[|destruct n;[|destruct n;[|destruct n] ] ]; cpx; unfold selectbt; simpl.

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }

          { apply alphaeqbt_eq; auto. }

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            constructor; simpl; auto.
            introv p.
            destruct n; cpx; unfold selectbt; simpl; tcsp.
            apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw oneswapvar_eq1; tcsp. }
        }
*)

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.
          constructor; simpl; auto.
          fold_terms.
          introv p.
          destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp; eauto 3 with slow;[].

          (*
          { apply alphaeqbt_eq; auto. }
*)

          { pose proof (ex_fresh_var ([ v1, v,
                                        oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v nvarx)),
                                        oneswapvar vg1 v0 (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1))),
                                        oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v nvarx)),
                                        oneswapvar vg2 v0 (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))
                                      ]
                                     )
                       ) as fv; exrepnd.
            allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
            apply (aeqbt _ [v2]); simpl; auto.
            { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }

            fold_terms;[].
            constructor; simpl; auto.

            allrw oneswapvar_eq1.
            allrw (oneswapvar_neq v1 v2 v); auto;[].

            introv p.
            destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp; eauto 3 with slow;[|].

            { apply alphaeqbt_eq.
              apply alphaeqbt_nilv2.
              apply alphaeq_eq.
              constructor; simpl; auto.
              introv q.
              destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp.

              { apply alphaeqbt_eq.
                apply alphaeqbt_nilv2.
                apply alphaeq_eq.
                constructor; simpl; auto.
                introv r.
                destruct n;[|destruct n;[|destruct n;[|destruct n] ] ]; cpx; unfold selectbt; simpl; tcsp;
                eauto 3 with slow;[].

                (*
                { apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  allrw oneswapvar_eq1; tcsp. }

                { apply alphaeqbt_eq; auto. }

                { apply alphaeqbt_eq; auto. }
*)

                { apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  constructor; simpl; auto.
                  introv r.
                  destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp;
                  eauto 3 with slow;[].

                  (*
                  { apply alphaeqbt_eq; auto. }
*)

                  { apply alphaeqbt_eq.
                    apply alphaeqbt_nilv2.
                    apply alphaeq_eq.
                    constructor; simpl; auto.
                    introv r.
                    destruct n; cpx; unfold selectbt; simpl; tcsp.

                    { apply alphaeqbt_eq.
                      apply alphaeqbt_nilv2.
                      apply alphaeq_eq.
                      constructor; simpl; auto.
                      introv s.
                      destruct n; cpx; unfold selectbt; simpl; tcsp.

                      { pose proof (ex_fresh_var ([ oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v nvarx))),
                                                    oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v nvarx)))
                                                  ]
                                                 )
                                   ) as fv; exrepnd.
                        allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
                        apply (aeqbt _ [v3]); simpl; auto.
                        { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }
                        fold_terms;[].

                        allrw oneswapvar_eq1; tcsp.
                      }
                    }
                  }
                }
              }

              { pose proof (ex_fresh_var ([ oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v (newvar (@mk_void o))))),
                                            oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v (newvar (@mk_void o)))))
                                          ]
                                         )
                           ) as fv; exrepnd.
                allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
                apply (aeqbt _ [v3]); simpl; auto.
                { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }
                fold_terms;[].

                constructor; simpl; auto.
                introv r.
                destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp;
                eauto 3 with slow;[].

                (*
                { apply alphaeqbt_eq; auto. }
*)

                { apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  constructor; simpl; auto.
                  introv r.
                  destruct n; cpx; unfold selectbt; simpl; tcsp;[].

                  apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  constructor; simpl; auto.
                  introv q.
                  destruct n; cpx; unfold selectbt; simpl; tcsp;[].

                  pose proof (ex_fresh_var ([ oneswapvar
                                                (oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v (newvar (@mk_void o)))))) v3
                                                (oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v nvarx)))),
                                              oneswapvar
                                                (oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v (newvar (@mk_void o)))))) v3
                                                (oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v nvarx))))
                                            ]
                                           )
                             ) as fv; exrepnd.
                  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
                  apply (aeqbt _ [v4]); simpl; auto.
                  { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }
                  fold_terms;[].
                  allrw oneswapvar_eq1; tcsp.
                }
              }
            }

            { pose proof (ex_fresh_var ([ v, v2,
                                          oneswapvar v1 v2 (oneswapvar vg1 v0 (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1)))),
                                          oneswapvar v1 v2 (oneswapvar vg2 v0 (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))),
                                          oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v nvarx))),
                                          oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v nvarx)))
                                        ]
                                       )
                         ) as fv; exrepnd.
              allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
              apply (aeqbt _ [v3]); simpl; auto.
              { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }
              fold_terms;[].

              rw (oneswapvar_neq v1 v2
                                 (oneswapvar vg1 v0
                                             (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1)))));
                tcsp;[].

              rw (oneswapvar_neq v1 v2
                                 (oneswapvar vg2 v0
                                             (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))));
                tcsp;[].

              constructor; simpl; auto.
              introv r.
              destruct n;[|destruct n;[|destruct n;[|destruct n] ] ]; cpx; unfold selectbt; simpl; tcsp;
              eauto 3 with slow;[| |].

              { apply alphaeqbt_eq.
                apply alphaeqbt_nilv2.
                apply alphaeq_eq.
                allrw oneswapvar_eq1; tcsp.

                rw (oneswapvar_neq
                      (oneswapvar vg1 v0
                                  (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1))))
                      v3 v2);
                    tcsp;[].

                rw (oneswapvar_neq
                      (oneswapvar vg2 v0
                                  (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2))))
                      v3 v2);
                    tcsp; eauto 3 with slow.
              }

              { apply alphaeqbt_eq.
                apply alphaeqbt_nilv2.
                apply alphaeq_eq.
                unfold oneswapvar; boolvar; eauto 3 with slow; sp.
              }

              (*
              { apply alphaeqbt_eq; auto. }
*)

              { apply alphaeqbt_eq.
                apply alphaeqbt_nilv2.
                apply alphaeq_eq.
                constructor; simpl; auto.
                introv r.
                destruct n;[|destruct n]; cpx; unfold selectbt; simpl; tcsp;
                eauto 3 with slow;[].

                (*
                { apply alphaeqbt_eq; auto. }
*)

                { apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  constructor; simpl; auto.
                  introv r.
                  destruct n; cpx; unfold selectbt; simpl; tcsp.

                  apply alphaeqbt_eq.
                  apply alphaeqbt_nilv2.
                  apply alphaeq_eq.
                  constructor; simpl; auto.
                  introv q.
                  destruct n; cpx; unfold selectbt; simpl; tcsp.

                  pose proof (ex_fresh_var ([ oneswapvar
                                                (oneswapvar vg1 v0 (newvar (mk_less_than (mk_var vi1) (@mk_var o vb1)))) v3
                                                (oneswapvar v1 v2 (oneswapvar vi1 v1 (oneswapvar vg1 v0 (oneswapvar vb1 v nvarx)))),
                                              oneswapvar
                                                (oneswapvar vg2 v0 (newvar (mk_less_than (mk_var vi2) (@mk_var o vb2)))) v3
                                                (oneswapvar v1 v2 (oneswapvar vi2 v1 (oneswapvar vg2 v0 (oneswapvar vb2 v nvarx))))
                                            ]
                                           )
                             ) as fv; exrepnd.
                  allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
                  apply (aeqbt _ [v4]); simpl; auto.
                  { apply disjoint_singleton_l; intro k; allsimpl; repndors; tcsp. }
                  fold_terms;[].
                  allrw oneswapvar_eq1; tcsp.
                }
              }
            }
          }
        }
      }

      { pose proof (ex_fresh_var ([ vi1, vi2, v0, vg1, vb1, v, vg2, vb2
                                  ]
                                    ++ allvars (cswap [(vg1, v0)] (cswap [(vb1, v)] f))
                                    ++ allvars (cswap [(vg2, v0)] (cswap [(vb2, v)] f))
                                    ++ allvars f
                                 )
                   ) as fv; exrepnd.
        allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
        apply (aeqbt _ [v1]); simpl; auto.
        { apply disjoint_singleton_l; intro k; allsimpl;
          allrw in_app_iff; allsimpl;
          repndors; tcsp. }
        fold_terms;[].
        allrw oneswapvar_eq1; tcsp.
        constructor; simpl; auto.

        introv k.
        destruct n;[|destruct n;[|destruct n ] ]; cpx; unfold selectbt; simpl; tcsp;
        eauto 3 with slow;[|].

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.

          constructor; simpl; auto.
          introv p.
          destruct n;[|destruct n ]; cpx; unfold selectbt; simpl; tcsp;
          eauto 3 with slow;[].

          { apply alphaeqbt_eq.
            apply alphaeqbt_nilv2.
            apply alphaeq_eq.
            allrw @cswap_cswap; allsimpl.
            apply (alphaeq_trans _ f).
            { apply alphaeq_cswap_cl2; simpl; repeat (rw disjoint_cons_l);
              simpl; allrw not_over_or; dands; try (rw clf); tcsp.
              repeat (rw no_repeats_cons); dands; simpl; tcsp. }
            { apply alphaeq_sym.
              apply alphaeq_cswap_cl2; simpl; repeat (rw disjoint_cons_l);
              simpl; allrw not_over_or; dands; try (rw clf); tcsp.
              repeat (rw no_repeats_cons); dands; simpl; tcsp. }
          }

          (*
          { apply alphaeqbt_eq; apply alphaeqbt_nilv2; auto. }
*)
        }

        { rw (oneswapvar_neq vi1 v1 v0); auto.
          rw (oneswapvar_neq vi2 v1 v0); auto.
          apply alphaeqbt_eq; apply alphaeqbt_nilv2; auto. }

        (*
        { apply alphaeqbt_eq; apply alphaeqbt_nilv2; auto. }
*)
      }
    }

    { rw (oneswapvar_neq vg1 v0 (oneswapvar vb1 v vf1));
      auto; [|unfold oneswapvar; boolvar; complete sp].

      rw (oneswapvar_neq vg2 v0 (oneswapvar vb2 v vf2));
      auto; [|unfold oneswapvar; boolvar; complete sp].

      pose proof (ex_fresh_var ([ v0, vg1, vb1, vg2, vb2,
                                  oneswapvar vb1 v vf1,
                                  oneswapvar vb2 v vf2
                                ]
                                  ++ allvars (cswap [(vg1, v0)] (cswap [(vb1, v)] F))
                                  ++ allvars (cswap [(vg1, v0)] (cswap [(vb1, v)] f))
                                  ++ allvars (cswap [(vg2, v0)] (cswap [(vb2, v)] F))
                                  ++ allvars (cswap [(vg2, v0)] (cswap [(vb2, v)] f))
                                  ++ allvars F
                               )
                 ) as fv; exrepnd.
      allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
      apply (aeqbt _ [v1]); simpl; auto.
      { apply disjoint_singleton_l; intro k; allsimpl;
        allrw in_app_iff; allsimpl; repndors; tcsp. }
      fold_terms;[].
      allrw oneswapvar_eq1; tcsp.
      constructor; simpl; auto.

      introv p.
      destruct n;[|destruct n;[|destruct n] ]; cpx; unfold selectbt; simpl; tcsp;
      eauto 3 with slow;[|].

      { apply alphaeqbt_eq.
        apply alphaeqbt_nilv2.
        apply alphaeq_eq.

        constructor; simpl; auto.

        introv q.
        destruct n;[|destruct n ]; cpx; unfold selectbt; simpl; tcsp;
        eauto 3 with slow;[|].

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.

          apply (alphaeq_trans _ F).

          { pose proof (alphaeq_cswap_cl2 F [(vb1,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb1,v)] F) [(vg1,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clF; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg1,v0)] (cswap [(vb1,v)] F)) [(oneswapvar vb1 v vf1, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clF; simpl; tcsp. }
            eauto with slow. }

          { pose proof (alphaeq_cswap_cl2 F [(vb2,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb2,v)] F) [(vg2,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clF; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg2,v0)] (cswap [(vb2,v)] F)) [(oneswapvar vb2 v vf2, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clF; simpl; tcsp. }
            eauto with slow. }
        }

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.

          apply (alphaeq_trans _ f).

          { pose proof (alphaeq_cswap_cl2 f [(vb1,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb1,v)] f) [(vg1,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clf; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg1,v0)] (cswap [(vb1,v)] f)) [(oneswapvar vb1 v vf1, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clf; simpl; tcsp. }
            eauto with slow. }

          { pose proof (alphaeq_cswap_cl2 f [(vb2,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb2,v)] f) [(vg2,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clf; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg2,v0)] (cswap [(vb2,v)] f)) [(oneswapvar vb2 v vf2, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clf); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clf; simpl; tcsp. }
            eauto with slow. }
        }
      }

      { apply alphaeqbt_eq.
        apply alphaeqbt_nilv2.
        apply alphaeq_eq.

        constructor; simpl; auto.
        introv q.
        destruct n;[|destruct n ]; cpx; unfold selectbt; simpl; tcsp;
        eauto 3 with slow;[|].

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.

          apply (alphaeq_trans _ F).

          { pose proof (alphaeq_cswap_cl2 F [(vb1,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb1,v)] F) [(vg1,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clF; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg1,v0)] (cswap [(vb1,v)] F)) [(oneswapvar vb1 v vf1, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clF; simpl; tcsp. }
            eauto with slow. }

          { pose proof (alphaeq_cswap_cl2 F [(vb2,v)]) as h1.
            repeat (autodimp h1 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp;[].

            pose proof (alphaeq_cswap_cl2 (cswap [(vb2,v)] F) [(vg2,v0)]) as h2.
            repeat (autodimp h2 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1; rw clF; simpl; tcsp. }

            pose proof (alphaeq_cswap_cl2 (cswap [(vg2,v0)] (cswap [(vb2,v)] F)) [(oneswapvar vb2 v vf2, v1)]) as h3.
            repeat (autodimp h3 hyp); simpl; repeat (rw disjoint_singleton_l);
            simpl; try (allrw clF); tcsp.
            { apply alphaeq_eq in h2; apply alphaeq_preserves_free_vars in h2; rw h2.
              apply alphaeq_eq in h1; apply alphaeq_preserves_free_vars in h1; rw h1.
              rw clF; simpl; tcsp. }
            eauto with slow. }
        }

        { apply alphaeqbt_eq.
          apply alphaeqbt_nilv2.
          apply alphaeq_eq.

          unfold oneswapvar; boolvar; tcsp; eauto 3 with slow.
        }
      }

      (*
      { apply alphaeqbt_eq; auto. }
*)
    }
  }
Qed.
