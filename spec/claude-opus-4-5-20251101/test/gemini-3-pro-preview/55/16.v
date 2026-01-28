Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

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

Example test_fib_13 : fib_spec 13 233.
Proof.
  unfold fib_spec.
  split.
  - (* Prove 13 >= 0 *)
    lia.
  - (* Prove 233 = fib_nat (Z.to_nat 13) *)
    simpl.
    reflexivity.
Qed.