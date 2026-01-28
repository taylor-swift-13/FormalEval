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
  problem_92_spec (-5 # 1) (8 # 1) (10 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    apply (f_equal Qnum) in Hx; simpl in Hx.
    apply (f_equal Qnum) in Hy; simpl in Hy.
    apply (f_equal Qnum) in Hz; simpl in Hz.
    destruct Hsum as [H|[H|H]].
    + exfalso. rewrite <- Hx in H. rewrite <- Hy in H. rewrite <- Hz in H. lia.
    + exfalso. rewrite <- Hy in H. rewrite <- Hx in H. rewrite <- Hz in H. lia.
    + exfalso. rewrite <- Hz in H. rewrite <- Hx in H. rewrite <- Hy in H. lia.
Qed.