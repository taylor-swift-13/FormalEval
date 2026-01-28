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

Example test_problem_92 : problem_92_spec (10 # 1) (-2 # 1) (20 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. discriminate.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    inversion Hx.
    inversion Hy.
    inversion Hz.
    subst.
    lia.
Qed.