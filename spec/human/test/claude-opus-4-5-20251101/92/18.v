Require Import QArith ZArith.
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

Example test_problem_92 : problem_92_spec (7 # 1) (1 # 1) (8 # 1) true.
Proof.
  unfold problem_92_spec.
  split.
  - intros _.
    exists 7%Z, 1%Z, 8%Z.
    split. { reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    right. right. reflexivity.
  - intros _. reflexivity.
Qed.