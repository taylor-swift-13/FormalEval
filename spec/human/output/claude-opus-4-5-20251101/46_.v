Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

(* 使用归纳关系表示 fib4 序列*)
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

(* Pre: no additional constraints for `fib4` *)
Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

(* Test case: input = 5, output = 4 *)
Example problem_46_test : problem_46_spec 5 4.
Proof.
  unfold problem_46_spec.
  (* fib4(5) = fib4(4) + fib4(3) + fib4(2) + fib4(1) *)
  (* fib4(4) = fib4(3) + fib4(2) + fib4(1) + fib4(0) = 0 + 2 + 0 + 0 = 2 *)
  (* fib4(5) = 2 + 0 + 2 + 0 = 4 *)
  
  (* First, we need to show fib4_at 4 2 *)
  assert (H4: fib4_at 4 2).
  {
    replace 2 with (0 + 0 + 2 + 0) by reflexivity.
    apply (fib4_at_SSSS 0 0 0 2 0).
    - apply fib4_at_0.
    - apply fib4_at_1.
    - apply fib4_at_2.
    - apply fib4_at_3.
  }
  
  (* Now show fib4_at 5 4 *)
  replace 4 with (0 + 2 + 0 + 2) by reflexivity.
  apply (fib4_at_SSSS 1 0 2 0 2).
  - apply fib4_at_1.
  - apply fib4_at_2.
  - apply fib4_at_3.
  - exact H4.
Qed.