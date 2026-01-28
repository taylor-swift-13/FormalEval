Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example problem_77_test1 :
  problem_77_spec 1 true.
Proof.
  unfold problem_77_spec.
  split.
  - intros H. exists 1%Z. reflexivity.
  - intros [x Hx]. rewrite Hx. reflexivity.
Qed.