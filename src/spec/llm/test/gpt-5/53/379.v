Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec
    (if nth 0%nat [false; true] false then 1%Z else 0%Z)
    (if nth 1%nat [false; true] false then 1%Z else 0%Z)
    1%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.