Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-2) 5 7 true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> (-2 = 5 + 7 \/ 5 = -2 + 7 \/ 7 = 5 + -2) *)
    intros _.
    right. left.
    lia.
  - (* Right to Left: (-2 = 5 + 7 \/ 5 = -2 + 7 \/ 7 = 5 + -2) -> true = true *)
    intros _.
    reflexivity.
Qed.