Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 1 300 2 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    lia.
Qed.