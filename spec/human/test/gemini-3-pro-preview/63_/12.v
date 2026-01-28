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

Example test_fibfib_21 : problem_63_spec 21 66012.
Proof.
  unfold problem_63_spec.
  pose (p0 := ff_zero).
  pose (p1 := ff_one).
  pose (p2 := ff_two).
  pose (p3 := ff_step _ _ _ _ p0 p1 p2 : is_fibfib 3 1).
  pose (p4 := ff_step _ _ _ _ p1 p2 p3 : is_fibfib 4 2).
  pose (p5 := ff_step _ _ _ _ p2 p3 p4 : is_fibfib 5 4).
  pose (p6 := ff_step _ _ _ _ p3 p4 p5 : is_fibfib 6 7).
  pose (p7 := ff_step _ _ _ _ p4 p5 p6 : is_fibfib 7 13).
  pose (p8 := ff_step _ _ _ _ p5 p6 p7 : is_fibfib 8 24).
  pose (p9 := ff_step _ _ _ _ p6 p7 p8 : is_fibfib 9 44).
  pose (p10 := ff_step _ _ _ _ p7 p8 p9 : is_fibfib 10 81).
  pose (p11 := ff_step _ _ _ _ p8 p9 p10 : is_fibfib 11 149).
  pose (p12 := ff_step _ _ _ _ p9 p10 p11 : is_fibfib 12 274).
  pose (p13 := ff_step _ _ _ _ p10 p11 p12 : is_fibfib 13 504).
  pose (p14 := ff_step _ _ _ _ p11 p12 p13 : is_fibfib 14 927).
  pose (p15 := ff_step _ _ _ _ p12 p13 p14 : is_fibfib 15 1705).
  pose (p16 := ff_step _ _ _ _ p13 p14 p15 : is_fibfib 16 3136).
  pose (p17 := ff_step _ _ _ _ p14 p15 p16 : is_fibfib 17 5768).
  pose (p18 := ff_step _ _ _ _ p15 p16 p17 : is_fibfib 18 10609).
  pose (p19 := ff_step _ _ _ _ p16 p17 p18 : is_fibfib 19 19513).
  pose (p20 := ff_step _ _ _ _ p17 p18 p19 : is_fibfib 20 35890).
  pose (p21 := ff_step _ _ _ _ p18 p19 p20 : is_fibfib 21 66012).
  exact p21.
Qed.