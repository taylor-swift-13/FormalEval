Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int: any_int_spec 2 3 1 true.
Proof.
  unfold any_int_spec.
  split.
  - (* Left to Right: true = true -> ... *)
    intros _.
    (* Goal: 2 = 3 + 1 \/ 3 = 2 + 1 \/ 1 = 3 + 2 *)
    (* The second disjunct (3 = 2 + 1) is true *)
    right. left.
    reflexivity.
  - (* Right to Left: ... -> true = true *)
    intros _.
    reflexivity.
Qed.