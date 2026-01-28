Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 4 2 2 true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> (4 = 2 + 2 \/ 2 = 4 + 2 \/ 2 = 2 + 4) *)
    intros _.
    left.
    lia.
  - (* Right to Left: (4 = 2 + 2 \/ 2 = 4 + 2 \/ 2 = 2 + 4) -> true = true *)
    intros _.
    reflexivity.
Qed.