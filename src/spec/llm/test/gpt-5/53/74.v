Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [125%Z; 119%Z] 0%Z) (nth 1%nat [125%Z; 119%Z] 0%Z) 244%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.