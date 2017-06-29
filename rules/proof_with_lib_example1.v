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

  Authors: Vincent Rahli

*)


Require Export proof_with_lib.



Definition opabs_myint : opabs := Build_opabs "myint" [] [].

Definition cmds1 {o} : @commands o :=
  [
    (* We add the 'member' abstraction *)
    COM_add_def
      opabs_member
      [(nvart, 0), (nvarT, 0)]
      (mk_so_equality (sovar nvart []) (sovar nvart []) (sovar nvarT []))
      opabs_member_correct,

    (* We prove that 'member' is well-formed *)
    COM_start_proof
      "member_wf"
      (mk_uall
         (mk_uni 0)
         nvarT
         (mk_uall
            (mk_var nvarT)
            nvart
            (mk_member
               (mk_abs opabs_member [nobnd (mk_var nvart), nobnd (mk_var nvarT)])
               (mk_uni 0))))
      (eq_refl, eq_refl),
    COM_update_proof
      "member_wf"
      []
      (proof_step_isect_member_formation (nvar "T") 1),
    COM_update_proof
      "member_wf"
      [1]
      (proof_step_isect_member_formation (nvar "t") 0),
    COM_update_proof
      "member_wf"
      [1,1]
      (proof_step_cut
         (nvar "w")
         (mk_cequiv
            (mk_abs opabs_member [nobnd (mk_var (nvar "t")), nobnd (mk_var (nvar "T"))])
            (mk_equality (mk_var (nvar "t")) (mk_var (nvar "t")) (mk_var (nvar "T"))))),
    COM_find_holes "member_wf",
    COM_update_proof
      "member_wf"
      [1,1,1]
      (proof_step_cequiv_computation 1),
    COM_update_proof
      "member_wf"
      [1,1,2]
      (proof_step_cequiv_subst_concl
         (nvar "x")
         (mk_equality (vterm (nvar "x")) (vterm (nvar "x")) (mk_uni 0))
         (mk_abs opabs_member [nobnd (mk_var (nvar "t")), nobnd (mk_var (nvar "T"))])
         (mk_equality (mk_var (nvar "t")) (mk_var (nvar "t")) (mk_var (nvar "T")))),
    COM_update_proof
      "member_wf"
      [1,1,2,2]
      (proof_step_hypothesis (nvar "w")),
    COM_update_proof
      "member_wf"
      [2]
      (proof_step_universe_equality),
    COM_update_proof
      "member_wf"
      [1,2]
      (proof_step_unhide_equality (nvar "T")),
    COM_update_proof
      "member_wf"
      [1,2,1]
      (proof_step_hypothesis_equality),
    COM_update_proof
      "member_wf"
      [1,1,2,1]
      (proof_step_equality_equality),
    COM_update_proof
      "member_wf"
      [1,1,2,1,1]
      (proof_step_unhide_equality (nvar "T")),
    COM_update_proof
      "member_wf"
      [1,1,2,1,1,1]
      (proof_step_hypothesis_equality),
    COM_update_proof
      "member_wf"
      [1,1,2,1,2]
      (proof_step_unhide_equality (nvar "t")),
    COM_update_proof
      "member_wf"
      [1,1,2,1,2,1]
      (proof_step_hypothesis_equality),
    COM_update_proof
      "member_wf"
      [1,1,2,1,3]
      (proof_step_unhide_equality (nvar "t")),
    COM_update_proof
      "member_wf"
      [1,1,2,1,3,1]
      (proof_step_hypothesis_equality),
    COM_find_holes "member_wf",
    COM_finish_proof "member_wf",

    (* We prove that Z is inhabited (by 17 here) *)
    COM_start_proof
      "int_member"
      mk_int
      (eq_refl, eq_refl),
    COM_update_proof
      "int_member"
      []
      (proof_step_introduction (mk_integer 17)),
    COM_update_proof
      "int_member"
      [1]
      (proof_step_integer_equality),
    COM_finish_proof "int_member",
    COM_find_holes "int_member",

    (* We prove that 'int_member' computes to 17 in 1 computation step *)
    COM_start_proof
      "int_member_cequiv"
      (mk_cequiv (mk_abs (opname2opabs "int_member") []) (mk_integer 17))
      (eq_refl, eq_refl),
    COM_update_proof
      "int_member_cequiv"
      []
      (proof_step_cequiv_computation 1),
    COM_find_holes "int_member_cequiv",
    COM_finish_proof "int_member_cequiv",

    (* We define a new abstraction on top of the one we got from "int_member"'s proof *)
    COM_add_def
      opabs_myint
      []
      (mk_simple_so_abs (opname2opabs "int_member"))
      (eq_refl, (eq_refl, (eq_refl, (eq_refl, eq_refl)))),

    (* We prove that 'myint' computes to 17 in 2 computation steps *)
    COM_start_proof
      "myint_cequiv"
      (mk_cequiv (mk_abs opabs_myint []) (mk_integer 17))
      (eq_refl, eq_refl),
    COM_update_proof
      "myint_cequiv"
      []
      (proof_step_cequiv_computation 2),
    COM_find_holes "myint_cequiv",
    COM_finish_proof "myint_cequiv",

    (* We prove once more that Z is inhabited.  We'll use our previous proof *)
    COM_start_proof
      "int_member_v2"
      mk_int
      (eq_refl, eq_refl),
    COM_update_proof
      "int_member_v2"
      []
      (proof_step_lemma "int_member"),
    COM_find_holes "int_member_v2",
    COM_finish_proof "int_member_v2"
  ].

Definition lib1 {o} : @UpdRes o := update_list_from_init cmds1.

Eval compute in lib1.

Time Eval compute in (update_list_from_init_with_validity cmds1).

(*
(*

***********************************************
                  TESTING
(compute wrapped in a Some below takes forever)
***********************************************

*)

Definition cmds2 {o} : @commands o :=
  [
    (* We prove that Z is inhabited (by 17 here) *)
    COM_start_proof
      "int_member"
      mk_int
      (eq_refl, eq_refl),
    COM_update_proof
      "int_member"
      []
      (proof_step_introduction (mk_integer 17)),
    COM_update_proof
      "int_member"
      [1]
      (proof_step_integer_equality),
    COM_finish_proof "int_member",
    COM_find_holes "int_member"
  ].

Definition lib2 {o} : @UpdRes o := update_list_from_init cmds2.

Eval compute in lib2.
Eval compute in (Library2ProofContext (upd_res_state lib2)).

Eval compute in (compute_atmost_k_steps
                   (Library2ProofContext (upd_res_state lib2))
                   1
                   (mk_abs (opname2opabs "int_member") [])).

Lemma reduces_to_of_compute_atmost_k_steps_if_eq {o} :
  forall lib k (t : @NTerm o) u,
    compute_atmost_k_steps lib k t = u
    -> reduces_to lib t u.
Proof.
  introv h; subst.
  apply reduces_to_of_compute_atmost_k_steps.
Qed.

Opaque reduces_to_of_compute_atmost_k_steps.

Eval compute in
    (@apply_proof_step_cequiv_computation
       _
       (Library2ProofContext (upd_res_state lib2))
       (mk_pre_bseq [] (pre_concl_ext
                          (mk_cequiv
                             (mk_abs (opname2opabs "int_member") [])
                             (mk_integer 17))))
       1).

Eval compute in
    (* this is fine *)
    (reduces_to_of_compute_atmost_k_steps [] 0 (mk_integer 1)).

Eval compute in
    (* the [Some] triggers the long computation!  WTF is going on? *)
    (Some (reduces_to_of_compute_atmost_k_steps [] 0 (mk_integer 1))).

Eval compute in
    (let ctxt := Library2ProofContext (upd_res_state lib2) in
     let a := mk_abs (opname2opabs "int_member") [] in
     let b := mk_integer 17 in
     let x := compute_atmost_k_steps ctxt 1 a in
(*     match term_dec_op x b with
     | Some p =>
*)
       Some (reduces_to_of_compute_atmost_k_steps ctxt 1 a)

(*       Some (reduces_to_of_compute_atmost_k_steps_if_eq ctxt 1 a b p)*)

     (*
                   Some ((*pre_proof_cequiv_computation
                           ctxt a b []*)
                           (eq_rect
                              _
                              _
                              (reduces_to_of_compute_atmost_k_steps ctxt 1 a)
                              _
                              p))*)

(*     | None => None
     end*)).
 *)
