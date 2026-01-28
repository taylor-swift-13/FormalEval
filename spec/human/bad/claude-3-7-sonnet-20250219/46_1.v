Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Define fib4 as a function on nat as given *)
Fixpoint fib4 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | S (S (S (S n'))) => fib4 (S (S (S n'))) + fib4 (S (S n')) + fib4 (S n') + fib4 n'
  end.

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input output : nat) : Prop :=
  output = fib4 input.

Example problem_46_example_5 :
  problem_46_spec 5 4.
Proof.
  unfold problem_46_spec.
  simpl.
  (* Calculate fib4 5 = fib4 4 + fib4 3 + fib4 2 + fib4 1 *)
  (* fib4 4 = fib4 3 + fib4 2 + fib4 1 + fib4 0 *)
  (* fib4 3 = 0, fib4 2 = 2, fib4 1 = 0, fib4 0 = 0 *)
  (* so fib4 4 = 0 + 2 + 0 + 0 = 2 *)
  (* fib4 5 = 2 + 0 + 2 + 0 = 4 *)
  reflexivity.
Qed.

Example problem_46_example_6 :
  problem_46_spec 6 8.
Proof.
  unfold problem_46_spec.
  simpl.
  (* fib4 6 = fib4 5 + fib4 4 + fib4 3 + fib4 2 *)
  (* fib4 5=4, fib4 4=2, fib4 3=0, fib4 2=2 *)
  (* fib4 6=4+2+0+2=8 *)
  reflexivity.
Qed.

Example problem_46_example_7 :
  problem_46_spec 7 14.
Proof.
  unfold problem_46_spec.
  simpl.
  (* fib4 7 = fib4 6 + fib4 5 + fib4 4 + fib4 3 *)
  (* fib4 6=8, fib4 5=4, fib4 4=2, fib4 3=0 *)
  (* fib4 7=8+4+2+0=14 *)
  reflexivity.
Qed.