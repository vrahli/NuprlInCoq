(*

  Copyright 2014 Cornell University

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


Require Export cequiv_props.

(* Incomplete version of hyp version of rwg *)
Ltac rwg_h H rel :=
  let xrr := fresh "XRR" in
  match type of rel with
    | ?Rr ?a ?b =>
      match type of H with
        (* 1 *)
        | ?R a =>
          assert (respects1 Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr _ _ rel) in H; clear xrr

        (* 2 *)
        | ?R a _ =>
          assert (respects2_l Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr a _ b rel) in H; clear xrr
        | ?R _ a =>
          assert (respects2_r Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr _ a b rel) in H; clear xrr

        (* 3 *)
        | ?R a _ _ =>
          assert (respects3_l Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr a _ _ b rel) in H; clear xrr
        | ?R _ a _ =>
          assert (respects3_m Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr _ a _ b rel) in H; clear xrr
        | ?R _ _ a =>
          assert (respects3_r Rr R)
            as xrr by (eauto with respects; idtac "missing hint:1");
            apply (xrr _ _ a b rel) in H; clear xrr
      end
  end.

Ltac betared :=
  match goal with
    (* on conclusion *)
    | [ lib : library |- context[mkc_apply2 (mkc_lam ?v ?b) ?a1 ?a2] ] =>
      let h := fresh "h" in
      generalize (cequivc_beta2 lib v b a1 a2); intro h; rwg h; clear h

    | [ lib : library |- context[mkc_apply (mkc_lam ?v ?b) ?a] ] =>
      let h := fresh "h" in
      generalize (cequivc_beta lib v b a); intro h; rwg h; clear h

    (* on hypothesis *)
    | [ lib : library, H : context[mkc_apply2 (mkc_lam ?v ?b) ?a1 ?a2] |- _ ] =>
      let h := fresh "h" in
      generalize (cequivc_beta2 lib v b a1 a2); intro h; rwg_h H h; clear h

    | [ lib : library, H : context[mkc_apply (mkc_lam ?v ?b) ?a] |- _ ] =>
      let h := fresh "h" in
      generalize (cequivc_beta lib v b a); intro h; rwg_h H h; clear h

    | [ lib : library |- context[mk_apply2 (mk_lam ?v ?b) ?a1 ?a2] ] =>
      let ispa1 := fresh "ispa1" in
      let ispa2 := fresh "ispa2" in
      let ispb  := fresh "ispb"  in
      let h     := fresh "h"     in
      assert (isprog a1) as ispa1 by eauto 10 with isprog;
        assert (isprog a2) as ispa2 by eauto 10 with isprog;
        assert (isprog_vars [v] b) as ispb by eauto 10 with isprog;
        generalize (cequiv_beta2 lib v b a1 a2 ispa1 ispa2 ispb);
        intro h; rwg h; clear ispa1 ispa2 ispb h

    | [ lib : library |- context[mk_apply (mk_lam ?v ?b) ?a] ] =>
      let ispa := fresh "ispa" in
      let ispb := fresh "ispb"  in
      let h    := fresh "h"     in
      assert (isprog a) as ispa by eauto 10 with isprog;
        assert (isprog_vars [v] b) as ispb by eauto 10 with isprog;
        generalize (cequiv_beta_isp lib v b a ispb ispa);
        intro h; rwg h; clear ispa ispb h
  end.
