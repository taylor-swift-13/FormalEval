Require Import ZArith.
Open Scope Z_scope.

Fixpoint fibfib_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S k => fibfib_aux k b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_aux (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 97 8569995677610263592944752.
Proof.
  vm_compute.
  reflexivity.
Qed.