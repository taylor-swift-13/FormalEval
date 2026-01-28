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
  Input: n = 17
  Output: res = 5768
*)
Example test_fibfib_17 : problem_63_spec 17 5768.
Proof.
  unfold problem_63_spec.
  (* Construct the proof step-by-step from the base cases up to 17 *)
  pose (h0 := ff_zero).
  pose (h1 := ff_one).
  pose (h2 := ff_two).
  pose (h3 := ff_step 0 0 0 1 h0 h1 h2).
  pose (h4 := ff_step 1 0 1 1 h1 h2 h3).
  pose (h5 := ff_step 2 1 1 2 h2 h3 h4).
  pose (h6 := ff_step 3 1 2 4 h3 h4 h5).
  pose (h7 := ff_step 4 2 4 7 h4 h5 h6).
  pose (h8 := ff_step 5 4 7 13 h5 h6 h7).
  pose (h9 := ff_step 6 7 13 24 h6 h7 h8).
  pose (h10 := ff_step 7 13 24 44 h7 h8 h9).
  pose (h11 := ff_step 8 24 44 81 h8 h9 h10).
  pose (h12 := ff_step 9 44 81 149 h9 h10 h11).
  pose (h13 := ff_step 10 81 149 274 h10 h11 h12).
  pose (h14 := ff_step 11 149 274 504 h11 h12 h13).
  pose (h15 := ff_step 12 274 504 927 h12 h13 h14).
  pose (h16 := ff_step 13 504 927 1705 h13 h14 h15).
  pose (h17 := ff_step 14 927 1705 3136 h14 h15 h16).
  (* h17 has type is_fibfib 17 (927 + 1705 + 3136), which is is_fibfib 17 5768 *)
  exact h17.
Qed.