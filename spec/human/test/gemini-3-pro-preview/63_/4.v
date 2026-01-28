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
  Input: n = 8
  Output: res = 24
*)
Example test_fibfib_8 : problem_63_spec 8 24.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  
  assert (H3: is_fibfib 3 1).
  { replace 1 with (0 + 0 + 1) by reflexivity. apply (ff_step 0 0 0 1); assumption. }
  
  assert (H4: is_fibfib 4 2).
  { replace 2 with (0 + 1 + 1) by reflexivity. apply (ff_step 1 0 1 1); assumption. }
  
  assert (H5: is_fibfib 5 4).
  { replace 4 with (1 + 1 + 2) by reflexivity. apply (ff_step 2 1 1 2); assumption. }
  
  assert (H6: is_fibfib 6 7).
  { replace 7 with (1 + 2 + 4) by reflexivity. apply (ff_step 3 1 2 4); assumption. }
  
  assert (H7: is_fibfib 7 13).
  { replace 13 with (2 + 4 + 7) by reflexivity. apply (ff_step 4 2 4 7); assumption. }
  
  replace 24 with (4 + 7 + 13) by reflexivity.
  apply (ff_step 5 4 7 13); assumption.
Qed.