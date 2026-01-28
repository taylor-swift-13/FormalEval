Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition bool_to_Z (b : bool) : Z :=
  if b then 1 else 0.

Definition problem_55_pre (b : bool) : Prop := True.

Definition problem_55_spec (b : bool) (res : Z) : Prop :=
  res = bool_to_Z b.

Example problem_55_example_bool : problem_55_spec true 1%Z.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.

Example problem_55_testcase_Z :
  bool_to_Z true = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.