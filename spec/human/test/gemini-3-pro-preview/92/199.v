Require Import QArith ZArith.
Require Import Psatz.

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

Example test_problem_92 : problem_92_spec (9 # 1) (-1 # 1) (10 # 1) true.
Proof.
  unfold problem_92_spec.
  split.
  - intros _.
    exists 9%Z, (-1)%Z, 10%Z.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- left.
           lia.
  - intros _.
    reflexivity.
Qed.