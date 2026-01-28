Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 0 20 (-10) false.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: (0 = 20 + -10 \/ 20 = 0 + -10 \/ -10 = 20 + 0) -> false = true *)
    intros H.
    lia.
Qed.