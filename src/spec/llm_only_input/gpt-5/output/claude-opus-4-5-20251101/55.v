Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Fixpoint fib_nat (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S _ as m) => fib_nat m + fib_nat (Nat.pred m)
  end.

Definition fib_spec (n : Z) (result : Z) : Prop :=
  n >= 0 /\
  result = fib_nat (Z.to_nat n).

Example fib_spec_10: fib_spec 10%Z 55%Z.
Proof.
  unfold fib_spec.
  split.
  - lia.
  - vm_compute; reflexivity.
Qed.