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
  problem_92_spec (-4 # 1) (4 # 1) (51 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    destruct H as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    apply f_equal with (f:=Qnum) in Hx.
    apply f_equal with (f:=Qnum) in Hy.
    apply f_equal with (f:=Qnum) in Hz.
    simpl in Hx, Hy, Hz.
    exfalso.
    destruct Hsum as [H1 | [H2 | H3]].
    + rewrite <- Hx in H1.
      rewrite <- Hy in H1.
      rewrite <- Hz in H1.
      lia.
    + rewrite <- Hx in H2.
      rewrite <- Hy in H2.
      rewrite <- Hz in H2.
      lia.
    + rewrite <- Hx in H3.
      rewrite <- Hy in H3.
      rewrite <- Hz in H3.
      lia.
Qed.