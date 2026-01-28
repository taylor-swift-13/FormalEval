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
  problem_92_spec ((-2) # 1) ((-1) # 1) ((-4) # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    exfalso.
    pose proof (f_equal Qnum Hx) as Hx'.
    pose proof (f_equal Qnum Hy) as Hy'.
    pose proof (f_equal Qnum Hz) as Hz'.
    simpl in Hx', Hy', Hz'.
    destruct Hsum as [Hsum|[Hsum|Hsum]].
    + rewrite <- Hx' in Hsum. rewrite <- Hy' in Hsum. rewrite <- Hz' in Hsum. lia.
    + rewrite <- Hy' in Hsum. rewrite <- Hx' in Hsum. rewrite <- Hz' in Hsum. lia.
    + rewrite <- Hz' in Hsum. rewrite <- Hx' in Hsum. rewrite <- Hy' in Hsum. lia.
Qed.