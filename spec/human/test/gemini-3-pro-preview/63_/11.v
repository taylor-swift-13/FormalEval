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

Example test_fibfib_23 : problem_63_spec 23 223317.
Proof.
  unfold problem_63_spec.
  assert (H0: is_fibfib 0 0) by apply ff_zero.
  assert (H1: is_fibfib 1 0) by apply ff_one.
  assert (H2: is_fibfib 2 1) by apply ff_two.
  assert (H3: is_fibfib 3 1) by (apply (ff_step _ _ _ _ H0 H1 H2)).
  assert (H4: is_fibfib 4 2) by (apply (ff_step _ _ _ _ H1 H2 H3)).
  assert (H5: is_fibfib 5 4) by (apply (ff_step _ _ _ _ H2 H3 H4)).
  assert (H6: is_fibfib 6 7) by (apply (ff_step _ _ _ _ H3 H4 H5)).
  assert (H7: is_fibfib 7 13) by (apply (ff_step _ _ _ _ H4 H5 H6)).
  assert (H8: is_fibfib 8 24) by (apply (ff_step _ _ _ _ H5 H6 H7)).
  assert (H9: is_fibfib 9 44) by (apply (ff_step _ _ _ _ H6 H7 H8)).
  assert (H10: is_fibfib 10 81) by (apply (ff_step _ _ _ _ H7 H8 H9)).
  assert (H11: is_fibfib 11 149) by (apply (ff_step _ _ _ _ H8 H9 H10)).
  assert (H12: is_fibfib 12 274) by (apply (ff_step _ _ _ _ H9 H10 H11)).
  assert (H13: is_fibfib 13 504) by (apply (ff_step _ _ _ _ H10 H11 H12)).
  assert (H14: is_fibfib 14 927) by (apply (ff_step _ _ _ _ H11 H12 H13)).
  assert (H15: is_fibfib 15 1705) by (apply (ff_step _ _ _ _ H12 H13 H14)).
  assert (H16: is_fibfib 16 3136) by (apply (ff_step _ _ _ _ H13 H14 H15)).
  assert (H17: is_fibfib 17 5768) by (apply (ff_step _ _ _ _ H14 H15 H16)).
  assert (H18: is_fibfib 18 10609) by (apply (ff_step _ _ _ _ H15 H16 H17)).
  assert (H19: is_fibfib 19 19513) by (apply (ff_step _ _ _ _ H16 H17 H18)).
  assert (H20: is_fibfib 20 35890) by (apply (ff_step _ _ _ _ H17 H18 H19)).
  assert (H21: is_fibfib 21 66012) by (apply (ff_step _ _ _ _ H18 H19 H20)).
  assert (H22: is_fibfib 22 121415) by (apply (ff_step _ _ _ _ H19 H20 H21)).
  assert (H23: is_fibfib 23 223317) by (apply (ff_step _ _ _ _ H20 H21 H22)).
  exact H23.
Qed.