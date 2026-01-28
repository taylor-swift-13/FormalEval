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
   input = [[-3%Z; -7%Z]] (converted to Reals using IZR)
   output = -3/7%R
*)
Example test_problem_32 : problem_32_spec [IZR (-3)%Z; IZR (-7)%Z] (-3/7).
Proof.
  (* Unfold the specification definition *)
  unfold problem_32_spec.
  
  (* Simplify the recursive evaluation of the polynomial *)
  simpl.
  
  (* 
     The goal is: (IZR (-3) + -3/7 * (IZR (-7) + -3/7 * 0)) = 0 
     We replace IZR constants with real constants to facilitate arithmetic.
  *)
  replace (IZR (-3)%Z) with (-3)%R by reflexivity.
  replace (IZR (-7)%Z) with (-7)%R by reflexivity.
  
  (* 
     Now the goal is: (-3 + -3/7 * (-7 + -3/7 * 0))%R = 0%R
     We can use the field tactic to solve this equality over Reals.
  *)
  field.
Qed.