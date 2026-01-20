Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 6 7 7 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | H]]; lia.
Qed.