Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2188 2188 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 1.
    split.
    + lia.
    + simpl. reflexivity.
  - intros _.
    reflexivity.
Qed.