Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec (nth 0%nat [-123456789098765432101234567890%Z; -101%Z] 0%Z)
           (nth 1%nat [-123456789098765432101234567890%Z; -101%Z] 0%Z)
           (-123456789098765432101234567991%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.