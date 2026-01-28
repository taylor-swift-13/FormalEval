(* 导入整数库 ZArith 和列表库 List *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

(* 输入两个列表长度必须相等 *)
Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0%Z = Z.abs (nth i game 0%Z - nth i guess 0%Z).

(* 比较函数定义 *)
Definition compare (game guess : list Z) : list Z :=
  map (fun pair => Z.abs (fst pair - snd pair)) (combine game guess).

(* 比较函数满足规约 *)
Lemma compare_correct : forall game guess,
  problem_152_pre game guess ->
  problem_152_spec game guess (compare game guess).
Proof.
  intros game guess Hpre.
  unfold problem_152_spec.
  split.
  - apply Hpre.
  - split.
    + unfold compare.
      rewrite length_map, length_combine.
      rewrite Hpre. reflexivity.
    + intros i Hi.
      unfold compare.
      rewrite nth_map.
      * rewrite nth_combine; try lia.
        unfold fst, snd.
        reflexivity.
      * rewrite length_combine.
        rewrite Hpre.
        apply Hi.
Qed.

(* 测试用例 *)
Example test_compare :
  problem_152_spec [1; 2; 3; 4; 5; 1] [1; 2; 3; 4; 2; -2] [0; 0; 0; 0; 3; 3].
Proof.
  apply compare_correct.
  unfold problem_152_pre.
  reflexivity.
Qed.

Qed.