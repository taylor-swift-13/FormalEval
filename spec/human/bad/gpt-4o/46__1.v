Require Import Coq.Arith.Arith.

(* Define the fib4 sequence using an iterative approach *)
Fixpoint fib4_iter (n : nat) (a b c d : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fib4_iter n' (b+c+d+a) a b c
  end.

Definition fib4 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | _ => fib4_iter (n - 4) 4 0 2 0
  end.

(* Inductive definition of fib4 sequence *)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

(* Specification for fib4 *)
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

(* Test case: fib4(5) = 4 *)
Example test_case_5 : problem_46_spec 5 4.
Proof.
  apply fib4_at_SSSS with (a := 2) (b := 0) (c := 0) (d := 2);
  try (apply fib4_at_2 || apply fib4_at_0 || apply fib4_at_1 || apply fib4_at_3).
Qed.

(* Test case: fib4(6) = 8 *)
Example test_case_6 : problem_46_spec 6 8.
Proof.
  apply fib4_at_SSSS with (a := 0) (b := 2) (c := 0) (d := 4);
  try (apply fib4_at_5 || apply fib4_at_2 || apply fib4_at_0 || apply fib4_at_4).
Qed.

(* Test case: fib4(7) = 14 *)
Example test_case_7 : problem_46_spec 7 14.
Proof.
  apply fib4_at_SSSS with (a := 0) (b := 4) (c := 8) (d := 2);
  try (apply fib4_at_6 || apply fib4_at_5 || apply fib4_at_2 || apply fib4_at_4).
Qed.