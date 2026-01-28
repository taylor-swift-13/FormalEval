Require Import ZArith.
Open Scope Z_scope.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  let fix aux (k : nat) (a b c : Z) : Z :=
    match k with
    | O => a
    | S k' => aux k' b c (a + b + c)
    end
  in
  res = aux (Z.to_nat n) 0 0 1.

Example fibfib_test_case : fibfib_spec 100 53324762928098149064722658.
Proof.
  vm_compute.
  reflexivity.
Qed.