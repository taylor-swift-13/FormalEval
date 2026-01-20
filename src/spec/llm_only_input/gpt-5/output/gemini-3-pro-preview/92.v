Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (res : bool) : Prop :=
  res = true <-> (x = y + z \/ y = x + z \/ z = x + y).

Example any_int_spec_test :
  any_int_spec 2%Z 3%Z 1%Z true.
Proof.
  unfold any_int_spec.
  split.
  - intros _. right. left. lia.
  - intros _. reflexivity.
Qed.