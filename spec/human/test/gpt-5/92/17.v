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
  problem_92_spec (-5 # 1) (10 # 1) (-5 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H; discriminate H.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    exfalso.
    pose proof (f_equal Qnum Hx) as Nx.
    pose proof (f_equal Qnum Hy) as Ny.
    pose proof (f_equal Qnum Hz) as Nz.
    simpl in Nx, Ny, Nz.
    rewrite <- Nx in Hsum.
    rewrite <- Ny in Hsum.
    rewrite <- Nz in Hsum.
    destruct Hsum as [H|[H|H]]; lia.
Qed.