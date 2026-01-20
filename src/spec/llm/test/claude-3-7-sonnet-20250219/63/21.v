Require Import Arith.Arith.
Require Import Lia.

Definition fibfib_spec (b : bool) (res : nat) : Prop :=
  (b = false /\ res = 0) \/
  (b = true /\ res = 0).

Example test_fibfib_spec : fibfib_spec false 0.
Proof.
  unfold fibfib_spec.
  left.
  split; reflexivity.
Qed.