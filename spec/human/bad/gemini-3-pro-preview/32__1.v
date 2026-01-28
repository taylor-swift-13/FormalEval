Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

(*
 * EvalPolyPred coeffs x res is true if and only if "res is the value of polynomial coeffs at point x"
 *)
Inductive EvalPolyPred : list R -> R -> R -> Prop :=
  | eval_poly_nil : forall x : R,
      (* Base case: Empty polynomial evaluates to 0 *)
      EvalPolyPred [] x 0
  | eval_poly_cons : forall (c : R) (cs : list R) (x res_tail : R),
      (* Inductive step: If we know the result of the tail... *)
      EvalPolyPred cs x res_tail ->
      (* ...then the result of (c :: cs) is c + x * res_tail *)
      EvalPolyPred (c :: cs) x (c + x * res_tail).

(* Pre: input list must be non-empty and have even length (as required by Spec) *)
(* Note: We use %nat to ensure the comparison is done on natural numbers, as R_scope is open *)
Definition problem_32_pre (input : list R) : Prop := (length input > 0)%nat /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* Postcondition: output must be a root of the polynomial. *)
  EvalPolyPred input output 0.

(* Test case: input = [-10; -2], output = -5.0 *)
Example test_case : problem_32_spec [-10; -2] (-5).
Proof.
  unfold problem_32_spec.
  (* 
     We want to prove: EvalPolyPred [-10; -2] (-5) 0 
     The polynomial is -10 + x * (-2). 
     At x = -5, value is -10 + (-5)*(-2) = 0.
     The recursive step for EvalPolyPred expects the result to be: head + x * tail_val
  *)
  
  (* Step 1: Match outer layer [-10; -2]. Head = -10. *)
  (* Tail is [-2]. Value of tail at -5 is -2. *)
  (* We replace 0 with the expanded form: -10 + (-5) * (-2) *)
  replace 0 with (-10 + (-5) * (-2)).
  - apply eval_poly_cons.
    
    (* Step 2: Match inner layer [-2]. Head = -2. *)
    (* Tail is []. Value of tail at -5 is 0. *)
    (* We replace -2 with the expanded form: -2 + (-5) * 0 *)
    replace (-2) with (-2 + (-5) * 0).
    + apply eval_poly_cons.
      
      (* Step 3: Base case [] *)
      apply eval_poly_nil.
      
    + (* Prove equality for step 2: -2 = -2 + (-5) * 0 *)
      field.
  - (* Prove equality for step 1: 0 = -10 + (-5) * (-2) *)
    field.
Qed.