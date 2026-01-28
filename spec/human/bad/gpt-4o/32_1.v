Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

(* eval_poly coeffs x: computes the value of the polynomial coeffs at point x *)
Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * eval_poly cs x)%R
  end.

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop :=
  length input > 0 /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* Postcondition: output must be a root of the polynomial. *)
  eval_poly input output = 0%R.

Example problem_32_test_case_1 :
  let input := [-10; -2] in
  let output := -5%R in
  problem_32_pre input ->
  problem_32_spec input output.
Proof.
  intros [Hlen Heven].
  unfold problem_32_spec.
  simpl. (* eval_poly [-10; -2] (-5) = -10 + (-2)*(-5) *)
  lra.
Qed.

Close Scope R_scope.

Qed.