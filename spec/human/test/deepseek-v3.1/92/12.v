Require Import QArith ZArith.
Open Scope Q_scope.
Open Scope Z_scope.

Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (exists zx zy zz : Z,
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\
      (zx = zy + zz \/ zy = zx + zz \/ zz = zx + zy)).

Example test_case_92 : problem_92_spec (-2 # 1) (-2 # 1) (-4 # 1) true.
Proof.
  unfold problem_92_spec.
  split.
  - intros _. exists (-2)%Z, (-2)%Z, (-4)%Z.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    right. right. auto with zarith.
  - intros H. reflexivity.
Qed.