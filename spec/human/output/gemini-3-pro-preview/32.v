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

(* 
   Test case:
   input = [[-10%Z; -2%Z]] (converted to Reals using IZR)
   output = -5.0%R
*)
Example test_problem_32 : problem_32_spec [IZR (-10)%Z; IZR (-2)%Z] (-5).
Proof.
  (* Unfold the specification definition *)
  unfold problem_32_spec.
  
  (* Simplify the recursive evaluation of the polynomial *)
  simpl.
  
  (* 
     The goal is: (IZR (-10) + -5 * (IZR (-2) + -5 * 0)) = 0 
     We replace IZR constants with real constants to facilitate arithmetic.
  *)
  replace (IZR (-10)%Z) with (-10)%R by reflexivity.
  replace (IZR (-2)%Z) with (-2)%R by reflexivity.
  
  (* 
     Now the goal is: (-10 + -5 * (-2 + -5 * 0))%R = 0%R
     We can use the field tactic to solve this equality over Reals.
  *)
  field.
Qed.