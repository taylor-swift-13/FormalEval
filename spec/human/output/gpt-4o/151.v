(* 引入所需的库 *)
Require Import ZArith. (* 用于整数操作 *)
Require Import List.   (* 用于列表操作 *)
Require Import Bool.   (* 用于布尔操作, 比如 && *)
Import ListNotations.
Open Scope bool_scope. (* 打开布尔作用域以使用 && 符号 *)
Open Scope Z_scope.

(* 输入为任意整数列表，允许为空 *)
Definition problem_151_pre (l : list Z) : Prop := True.

(*
    problem_151_spec 是程序的规约 (Spec)。
  它是一个一阶逻辑断言，描述了输入 l (一个整数列表) 和输出 res (一个整数) 之间的关系。
  这个关系是：res 必须等于对输入列表 l 调用 sum_sq_odd 函数的结果。
*)
Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

(* 测试用例: 输入为空列表，输出应为0 *)
Example test_case_1 : problem_151_spec [] 0.
Proof.
  unfold problem_151_spec. (* 展开定义 *)
  simpl. (* 简化 fold_left *)
  reflexivity. (* 证明等式 *)
Qed.