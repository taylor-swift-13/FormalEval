Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | O => a
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_iter (Z.to_nat n) 0 0 1.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_case : fibfib_spec 31 29249425.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.