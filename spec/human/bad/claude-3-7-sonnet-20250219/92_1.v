Require Import QArith ZArith.
Open Scope Q_scope.
Open Scope Z_scope.

Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (exists zx zy zz : Z,
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\
      (zx = zy + zz \/
       zy = zx + zz \/
       zz = zx + zy)).

Example test_problem_92 : problem_92_spec (2 # 1) (3 # 1) (1 # 1) true.
Proof.
  unfold problem_92_spec.
  split.
  - intros H.
    (* From b = true, rewrite to get true = true *)
    rewrite H.
    exists 2, 3, 1.
    repeat split; reflexivity.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    subst x y z.
    simpl.
    reflexivity.
Qed.