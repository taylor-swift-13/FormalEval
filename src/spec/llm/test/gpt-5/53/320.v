Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [1000000000000000000%Z; 999996%Z] 0%Z) (nth 1%nat [1000000000000000000%Z; 999996%Z] 0%Z) 1000000000000999996%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.