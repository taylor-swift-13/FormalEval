Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (res : bool) : Prop :=
  res = true <-> (x = y + z \/ y = x + z \/ z = x + y).

Example test_any_int : any_int_spec 2 3 1 true.
Proof.
  unfold any_int_spec.
  split.
  - intros _.
    right. left.
    reflexivity.
  - intros _.
    reflexivity.
Qed.