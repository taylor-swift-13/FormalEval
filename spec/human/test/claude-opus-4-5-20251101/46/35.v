Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint fib4_aux (n : nat) (a b c d : Z) : Z :=
  match n with
  | O => a
  | S n' => fib4_aux n' b c d (a + b + c + d)
  end.

Definition fib4_Z (n : nat) : Z :=
  fib4_aux n 0 0 2 0.

Definition problem_46_pre (input : list Z) : Prop := True.

Definition problem_46_spec (input : list Z) (output : Z) : Prop :=
  match input with
  | [n] => output = fib4_Z (Z.to_nat n)
  | _ => False
  end.

Example test_fib4_99 : problem_46_spec [99%Z] 2411315463631208843587520078%Z.
Proof.
  unfold problem_46_spec.
  unfold fib4_Z.
  native_compute.
  reflexivity.
Qed.