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
  problem_92_spec (50 # 1) (-19 # 1) (-30 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hex.
    destruct Hex as [zx [zy [zz [Hx [Hy [Hz Hor]]]]]].
    destruct Hor as [Hsum | [Hsum | Hsum]].
    + exfalso.
      assert ((50 # 1) = (-19 # 1) + (-30 # 1)) as Heq.
      { rewrite Hx. rewrite Hy. rewrite Hz. rewrite Hsum. reflexivity. }
      simpl in Heq. discriminate Heq.
    + exfalso.
      assert ((-19 # 1) = (50 # 1) + (-30 # 1)) as Heq.
      { rewrite Hx. rewrite Hy. rewrite Hz. rewrite Hsum. reflexivity. }
      simpl in Heq. discriminate Heq.
    + exfalso.
      assert ((-30 # 1) = (50 # 1) + (-19 # 1)) as Heq.
      { rewrite Hx. rewrite Hy. rewrite Hz. rewrite Hsum. reflexivity. }
      simpl in Heq. discriminate Heq.
Qed.