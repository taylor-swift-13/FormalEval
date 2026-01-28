Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example problem_77_example_1 : problem_77_spec 1000000%Z true.
Proof.
  unfold problem_77_spec.
  split.
  - intros _. exists 100%Z.
    vm_compute.
    reflexivity.
  - intros _. reflexivity.
Qed.