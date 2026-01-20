Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.

Open Scope Z_scope.

Fixpoint fib_nat (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S _ as m) => fib_nat m + fib_nat (pred m)
  end.

Definition fib_spec (n : Z) (result : Z) : Prop :=
  n >= 0 /\
  result = fib_nat (Z.to_nat n).

Example fib_test_36 : fib_spec 36%Z 14930352%Z.
Proof.
  unfold fib_spec.
  split.
  - lia.
  - native_cast_no_check (eq_refl 14930352%Z).
Qed.