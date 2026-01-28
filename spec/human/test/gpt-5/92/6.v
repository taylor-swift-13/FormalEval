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
  problem_92_spec (11 # 5) (11 # 5) (11 # 5) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. discriminate.
  - intros [zx [zy [zz [Hx [Hy [Hz _]]]]]].
    apply (f_equal Qden) in Hx.
    simpl in Hx.
    discriminate.
Qed.