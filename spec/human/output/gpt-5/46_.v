Require Import Coq.Arith.Arith.

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

Example problem_46_test : problem_46_spec 5 4.
Proof.
  unfold problem_46_spec.
  eapply fib4_at_SSSS with (i:=1) (a:=0) (b:=2) (c:=0) (d:=2).
  - exact fib4_at_1.
  - exact fib4_at_2.
  - exact fib4_at_3.
  - eapply fib4_at_SSSS with (i:=0) (a:=0) (b:=0) (c:=2) (d:=0).
    + exact fib4_at_0.
    + exact fib4_at_1.
    + exact fib4_at_2.
    + exact fib4_at_3.
Qed.