Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [-999996%Z; 1000000000000000000%Z] 0%Z) (nth 1%nat [-999996%Z; 1000000000000000000%Z] 0%Z) 999999999999000004%Z.
Proof.
  unfold add_spec.
  simpl.
  lia.
Qed.