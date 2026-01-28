Require Import ZArith.
Open Scope Z_scope.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  let fix loop (k : nat) (a b c : Z) : Z :=
    match k with
    | O => a
    | S k' => loop k' b c (a + b + c)
    end
  in
  res = loop (Z.to_nat n) 0 0 1.

Example fibfib_test_case : fibfib_spec 71 1127444240280152749.
Proof.
  vm_compute.
  reflexivity.
Qed.