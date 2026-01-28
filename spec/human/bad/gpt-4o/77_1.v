Require Import ZArith.
Open Scope Z_scope.

Definition iscube (a : Z) : bool :=
  let n := Z.abs a in
  let m := Z.sqrt (Z.sqrt n) in
  (m * m * m =? n)%Z.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example problem_77_test1 : problem_77_spec 1%Z true.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    exists 1%Z.
    simpl.
    reflexivity.
  - intros [x H].
    simpl in H.
    apply Z.eqb_eq.
    rewrite <- H.
    reflexivity.
Qed.