Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 0 0 0 true.
Proof.
  unfold any_int_spec.
  split.
  - intros _.
    left.
    lia.
  - intros _.
    reflexivity.
Qed.