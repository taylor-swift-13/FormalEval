Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n + 1) * n / 2.

Example test_sum_to_n_499996 : sum_to_n_spec 499996 124998250006.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.