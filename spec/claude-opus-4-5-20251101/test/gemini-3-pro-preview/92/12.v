Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-2) (-2) (-4) true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> (-2 = -2 + -4 \/ -2 = -2 + -4 \/ -4 = -2 + -2) *)
    intros _.
    right. right.
    lia.
  - (* Right to Left: (-2 = -2 + -4 \/ -2 = -2 + -4 \/ -4 = -2 + -2) -> true = true *)
    intros _.
    reflexivity.
Qed.