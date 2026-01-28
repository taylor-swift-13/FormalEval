Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 输入两个列表长度必须相等 *)
Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

(*
  compare_spec 定义了 'compare' 函数的规约。
*)
Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0%Z = Z.abs (nth i game 0%Z - nth i guess 0%Z).

(* 测试用例的证明 *)
Example test_case_1 : 
  problem_152_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z] 
                  [1%Z; 2%Z; 3%Z; 4%Z; 2%Z; -2%Z] 
                  [0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 3%Z].
Proof.
  unfold problem_152_spec.
  repeat split.
  - reflexivity.  (* 长度相等 *)
  - reflexivity.  (* 结果长度正确 *)
  - intros i Hi.
    (* 由于列表长度为6，i的范围是0到5 *)
    assert (i < 6)%nat as Hbound by lia.
    repeat (destruct i as [|i]; [simpl; compute; reflexivity | try lia]).
    (* 处理剩余的i值 *)
    destruct i; simpl; compute; reflexivity.
    destruct i; simpl; compute; reflexivity.
    destruct i; simpl; compute; reflexivity.
    destruct i; simpl; compute; reflexivity.
    destruct i; simpl; compute; reflexivity.
    (* 如果i >= 6，与前提矛盾 *)
    lia.
Qed.