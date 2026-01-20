Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [-999999999999999999998%Z; -9999%Z] 0%Z) (nth 1%nat [-999999999999999999998%Z; -9999%Z] 0%Z) (-1000000000000000009997%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.