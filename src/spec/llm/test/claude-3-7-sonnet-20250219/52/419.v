Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_spec_R (l : list R) (t : R) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x t then true else false) l.

Example test_below_threshold_R :
  below_threshold_spec_R
    [7.9; 7.9; 7.9; 7.9; -0.28791951724548404; -0.28791951724548404]
    1000
    true.
Proof.
  unfold below_threshold_spec_R.
  simpl.

  (* Show that each element is less than 1000 *)

  assert (H1: 7.9 < 1000) by lra.
  assert (H2: -0.28791951724548404 < 1000) by lra.

  repeat match goal with
  | |- context [if Rlt_dec ?x 1000 then true else false] =>
      destruct (Rlt_dec x 1000) eqn:?; [ | exfalso; lra]
  end.

  reflexivity.
Qed.