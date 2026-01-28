Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-5) (-1) (-6) true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> (-5 = -1 + -6 \/ -1 = -5 + -6 \/ -6 = -1 + -5) *)
    intros _.
    right. right.
    lia.
  - (* Right to Left: (-5 = -1 + -6 \/ -1 = -5 + -6 \/ -6 = -1 + -5) -> true = true *)
    intros _.
    reflexivity.
Qed.