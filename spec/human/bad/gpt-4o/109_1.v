(* 导入所需的库 *)
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.

(* 定义 move_one_ball 的实现 *)
Definition move_one_ball (arr : list Z) : bool :=
  match arr with
  | [] => true
  | _ :: _ => check_all_shifts arr (length arr)
  end.

(* 定义一个测试用例 *)
Example move_one_ball_example : move_one_ball [3; 4; 5; 1; 2] = true.
Proof.
  unfold move_one_ball.
  simpl.

  (* 我们需要检查所有可能的移位操作 *)
  unfold check_all_shifts.
  simpl.

  (* 检查移位后的数组是否已排序 *)
  (* 原始数组 [3; 4; 5; 1; 2] *)
  assert (A0: is_sorted_bool [3; 4; 5; 1; 2] = false).
  { unfold is_sorted_bool. simpl.
    rewrite Z.leb_gt. reflexivity.
    lia. }

  (* 右移一次 [2; 3; 4; 5; 1] *)
  assert (A1: is_sorted_bool [2; 3; 4; 5; 1] = false).
  { unfold is_sorted_bool. simpl.
    rewrite Z.leb_le. reflexivity.
    lia. }

  (* 右移两次 [1; 2; 3; 4; 5] *)
  assert (A2: is_sorted_bool [1; 2; 3; 4; 5] = true).
  { unfold is_sorted_bool. simpl.
    rewrite Z.leb_le. reflexivity.
    lia. }

  (* 因为右移两次后是排序的，所以返回 True *)
  rewrite A0, A1, A2. simpl.
  reflexivity.
Qed.