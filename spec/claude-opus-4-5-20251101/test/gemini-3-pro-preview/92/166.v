Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-1) 9 298 false.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: (-1 = 9 + 298 \/ 9 = -1 + 298 \/ 298 = 9 + -1) -> false = true *)
    intros H.
    lia.
Qed.