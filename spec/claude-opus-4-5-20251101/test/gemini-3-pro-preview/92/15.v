Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-3) (-4) (-7) true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> (-3 = -4 + -7 \/ -4 = -3 + -7 \/ -7 = -4 + -3) *)
    intros _.
    right. right.
    lia.
  - (* Right to Left: (-3 = -4 + -7 \/ -4 = -3 + -7 \/ -7 = -4 + -3) -> true = true *)
    intros _.
    reflexivity.
Qed.