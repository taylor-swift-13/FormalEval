Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 6 11 11 false.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: (6 = 11 + 11 \/ 11 = 6 + 11 \/ 11 = 11 + 6) -> false = true *)
    intros H.
    lia.
Qed.