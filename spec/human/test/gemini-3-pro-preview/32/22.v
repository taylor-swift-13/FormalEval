Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.

(*
 * eval_poly coeffs x calculates the value of the polynomial coeffs at point x
 *)
Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
(* We explicitly use %nat scope for the length comparison to avoid type mismatch with R_scope *)
Definition problem_32_pre (input : list R) : Prop := (length input > 0)%nat /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* Postcondition: output must be a root of the polynomial. *)
  eval_poly input output = 0%R.

Example test_problem_32 : problem_32_spec [IZR (-7)%Z; IZR (-6)%Z] (-7/6).
Proof.
  unfold problem_32_spec.
  simpl.
  replace (IZR (-7)%Z) with (-7)%R by reflexivity.
  replace (IZR (-6)%Z) with (-6)%R by reflexivity.
  field.
Qed.