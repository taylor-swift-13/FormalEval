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
  problem_92_spec (-20 # 1) (-4 # 1) (10 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    destruct H as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    inversion Hx; subst.
    inversion Hy; subst.
    inversion Hz; subst.
    destruct Hsum as [Hsum | [Hsum | Hsum]].
    + assert (-20%Z <> -4%Z + 10%Z) by lia. contradiction.
    + assert (-4%Z <> -20%Z + 10%Z) by lia. contradiction.
    + assert (10%Z <> -20%Z + -4%Z) by lia. contradiction.
Qed.