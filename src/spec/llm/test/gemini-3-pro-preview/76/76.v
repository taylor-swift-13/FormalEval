Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 82 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 1.
    split.
    + lia.
    + reflexivity.
  - intros _.
    reflexivity.
Qed.