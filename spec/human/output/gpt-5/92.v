Require Import QArith ZArith Lia.
Open Scope Q_scope.
Open Scope Z_scope.

Definition problem_92_pre (x y z : Q) : Prop := True.

Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (exists zx zy zz : Z,
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\
      (zx = zy + zz \/
       zy = zx + zz \/
       zz = zx + zy)).

Example problem_92_test :
  problem_92_spec (2 # 1) (3 # 1) (1 # 1) true.
Proof.
  unfold problem_92_spec.
  split.
  - intros _.
    exists 2%Z, 3%Z, 1%Z.
    repeat split; try reflexivity.
    right; left.
    lia.
  - intros _.
    reflexivity.
Qed.