Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

(*
  is_fibfib n res is an inductively defined proposition asserting "res is the n-th FibFib number".
  This definition is translated directly from the mathematical definition of the fibfib function.
*)
Inductive is_fibfib : nat -> nat -> Prop :=
  (* Base Case 1: The 0th FibFib number is 0 *)
  | ff_zero : is_fibfib 0 0

  (* Base Case 2: The 1st FibFib number is 0 *)
  | ff_one  : is_fibfib 1 0

  (* Base Case 3: The 2nd FibFib number is 1 *)
  | ff_two  : is_fibfib 2 1

  (*
    Inductive Step:
    If res_n, res_n1, res_n2 are the n-th, (n+1)-th, and (n+2)-th FibFib numbers respectively,
    then the (n+3)-th FibFib number is the sum of these three.
  *)
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

(*
  problem_63_spec is the program specification for the fibfib function.
  It states that for any input n, the result res must satisfy the is_fibfib predicate.
*)
Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

(* 
  Example Proof for the Test Case:
  Input: n = 2
  Output: res = 1
*)
Example test_fibfib_2 : problem_63_spec 2 1.
Proof.
  (* Unfold the specification definition *)
  unfold problem_63_spec.
  
  (* 
     The goal is now `is_fibfib 2 1`.
     Looking at the inductive definition of `is_fibfib`, 
     this corresponds exactly to the base case `ff_two`.
  *)
  apply ff_two.
Qed.