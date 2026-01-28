Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

(* The is_fibfib predicate as defined in the specification *)
Inductive is_fibfib : nat -> nat -> Prop :=
  | ff_zero : is_fibfib 0 0
  | ff_one  : is_fibfib 1 0
  | ff_two  : is_fibfib 2 1
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

(* Example proof for input [2%Z] and output 1%Z *)
Example test_case_2 : problem_63_spec 2 1.
Proof.
  apply ff_two.
Qed.