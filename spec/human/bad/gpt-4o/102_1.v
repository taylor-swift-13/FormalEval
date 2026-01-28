(* 导入 Coq 的整数库 ZArith *)
Require Import Coq.ZArith.ZArith.

(* 打开 Z 的作用域，这样就可以直接使用像 +, -, <= 等符号，而不用写 Z.add, Z.sub, Z.le *)
Open Scope Z_scope.

(* x 与 y 均为正整数 *)
Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

(* 
   定义 choose_num 函数的规约 (Specification)
   它描述了输入 x, y 和输出 res 之间必须满足的关系。
*)
Definition problem_102_spec (x y res : Z) : Prop :=

  (* 情况一：当区间 [x, y] 中存在偶数时 *)
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须是这个区间内最大的偶数 *)
    (Z.even res = true/\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y ->  Z.even z' = false)) )
  /\
  (* 情况二：当区间 [x, y] 中不存在偶数时 *)
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须等于 -1 *)
    res = -1 ).

Fixpoint choose_num (x y : Z) : Z :=
  if Z.leb x y then
    if Z.even y then y
    else choose_num x (y - 1)
  else -1.

Lemma choose_num_correct : forall x y,
  problem_102_pre x y ->
  problem_102_spec x y (choose_num x y).
Proof.
  intros x y [Hx Hy].
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Heven]]].
    assert (Hxy: x <= y) by lia.
    induction y.
    + simpl in *.
      lia.
    + simpl.
      destruct (Z.leb x (Z.succ y)) eqn:Hxy'.
      * destruct (Z.even (Z.succ y)) eqn:Heveny.
        -- split; try assumption.
           split; [lia | split; [lia |]].
           intros z' [Hres Hz'y].
           apply Z.even_spec in Heveny as [k' Hk'].
           subst.
           assert (z' <= Z.succ (2 * k')) by lia.
           destruct (Z.even z') eqn:Hz'even; auto.
           apply Z.even_spec in Hz'even as [k'' Hk''].
           lia.
        -- apply IHy.
           ++ lia.
           ++ exists z.
              split; [lia | split; [lia | assumption]].
      * exfalso.
        apply Z.leb_gt in Hxy'.
        lia.
  - intros H.
    induction y.
    + simpl.
      destruct (Z.leb x 0) eqn:Hxy.
      * exfalso.
        apply Z.leb_le in Hxy.
        lia.
      * reflexivity.
    + simpl.
      destruct (Z.leb x (Z.succ y)) eqn:Hxy.
      * destruct (Z.even (Z.succ y)) eqn:Heveny.
        -- exfalso.
           apply H.
           exists (Z.succ y).
           split; try lia.
           split; try lia.
           assumption.
        -- apply IHy.
           intros [z [Hz1 [Hz2 Heven]]].
           apply H.
           exists z.
           split; try lia.
           split; try lia.
           assumption.
      * reflexivity.
Qed.

Example test_case_1 : choose_num 12 15 = 14.
Proof.
  simpl. reflexivity.
Qed.

Example test_case_2 : choose_num 13 12 = -1.
Proof.
  simpl. reflexivity.
Qed.