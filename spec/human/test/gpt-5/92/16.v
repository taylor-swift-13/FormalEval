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
  problem_92_spec (50 # 1) (-20 # 1) (-30 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. discriminate H.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    apply (f_equal Qnum) in Hx.
    apply (f_equal Qnum) in Hy.
    apply (f_equal Qnum) in Hz.
    cbn in Hx, Hy, Hz.
    symmetry in Hx; symmetry in Hy; symmetry in Hz.
    subst zx zy zz.
    exfalso.
    destruct Hsum as [H|[H|H]]; lia.
Qed.