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
  problem_92_spec (-5 # 1) (-3 # 1) (-3 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    apply f_equal with (f:=Qnum) in Hx.
    apply f_equal with (f:=Qnum) in Hy.
    apply f_equal with (f:=Qnum) in Hz.
    simpl in Hx, Hy, Hz.
    symmetry in Hx; symmetry in Hy; symmetry in Hz.
    destruct Hsum as [Hsum|[Hsum|Hsum]].
    + rewrite Hx, Hy, Hz in Hsum. lia.
    + rewrite Hy, Hx, Hz in Hsum. lia.
    + rewrite Hz, Hx, Hy in Hsum. lia.
Qed.