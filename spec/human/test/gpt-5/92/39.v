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
  problem_92_spec (10 # 1) (6 # 1) (6 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. inversion H.
  - intros Hex.
    exfalso.
    destruct Hex as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    pose proof (f_equal Qnum Hx) as Nx.
    pose proof (f_equal Qnum Hy) as Ny.
    pose proof (f_equal Qnum Hz) as Nz.
    simpl in Nx, Ny, Nz.
    symmetry in Nx.
    symmetry in Ny.
    symmetry in Nz.
    destruct Hsum as [H1 | [H2 | H3]].
    + rewrite Nx, Ny, Nz in H1. lia.
    + rewrite Nx, Ny, Nz in H2. lia.
    + rewrite Nx, Ny, Nz in H3. lia.
Qed.