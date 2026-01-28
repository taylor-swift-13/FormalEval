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
  problem_92_spec (6 # 1) (7 # 1) (7 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. discriminate H.
  - intros Hex.
    exfalso.
    destruct Hex as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    inversion Hx; subst.
    inversion Hy; subst.
    inversion Hz; subst.
    destruct Hsum as [H1 | [H2 | H3]]; lia.
Qed.