Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n + 1) * n / 2.

Example test_sum_to_n_2 : sum_to_n_spec 54 1485.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.