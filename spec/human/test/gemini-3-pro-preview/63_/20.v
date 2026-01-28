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
  Input: n = 18
  Output: res = 10609
*)
Example test_fibfib_18 : problem_63_spec 18 10609.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  
  assert (H3: is_fibfib 3 1).
  { replace 1 with (0 + 0 + 1) by reflexivity. apply (ff_step 0 0 0 1 H0 H1 H2). }

  assert (H4: is_fibfib 4 2).
  { replace 2 with (0 + 1 + 1) by reflexivity. apply (ff_step 1 0 1 1 H1 H2 H3). }

  assert (H5: is_fibfib 5 4).
  { replace 4 with (1 + 1 + 2) by reflexivity. apply (ff_step 2 1 1 2 H2 H3 H4). }

  assert (H6: is_fibfib 6 7).
  { replace 7 with (1 + 2 + 4) by reflexivity. apply (ff_step 3 1 2 4 H3 H4 H5). }

  assert (H7: is_fibfib 7 13).
  { replace 13 with (2 + 4 + 7) by reflexivity. apply (ff_step 4 2 4 7 H4 H5 H6). }

  assert (H8: is_fibfib 8 24).
  { replace 24 with (4 + 7 + 13) by reflexivity. apply (ff_step 5 4 7 13 H5 H6 H7). }

  assert (H9: is_fibfib 9 44).
  { replace 44 with (7 + 13 + 24) by reflexivity. apply (ff_step 6 7 13 24 H6 H7 H8). }

  assert (H10: is_fibfib 10 81).
  { replace 81 with (13 + 24 + 44) by reflexivity. apply (ff_step 7 13 24 44 H7 H8 H9). }

  assert (H11: is_fibfib 11 149).
  { replace 149 with (24 + 44 + 81) by reflexivity. apply (ff_step 8 24 44 81 H8 H9 H10). }

  assert (H12: is_fibfib 12 274).
  { replace 274 with (44 + 81 + 149) by reflexivity. apply (ff_step 9 44 81 149 H9 H10 H11). }

  assert (H13: is_fibfib 13 504).
  { replace 504 with (81 + 149 + 274) by reflexivity. apply (ff_step 10 81 149 274 H10 H11 H12). }

  assert (H14: is_fibfib 14 927).
  { replace 927 with (149 + 274 + 504) by reflexivity. apply (ff_step 11 149 274 504 H11 H12 H13). }

  assert (H15: is_fibfib 15 1705).
  { replace 1705 with (274 + 504 + 927) by reflexivity. apply (ff_step 12 274 504 927 H12 H13 H14). }

  assert (H16: is_fibfib 16 3136).
  { replace 3136 with (504 + 927 + 1705) by reflexivity. apply (ff_step 13 504 927 1705 H13 H14 H15). }

  assert (H17: is_fibfib 17 5768).
  { replace 5768 with (927 + 1705 + 3136) by reflexivity. apply (ff_step 14 927 1705 3136 H14 H15 H16). }

  assert (H18: is_fibfib 18 10609).
  { replace 10609 with (1705 + 3136 + 5768) by reflexivity. apply (ff_step 15 1705 3136 5768 H15 H16 H17). }

  exact H18.
Qed.