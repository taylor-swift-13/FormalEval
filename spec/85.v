(* def add(lst):
"""Given a non-empty list of integers lst. add the even elements that are at odd indices..


Examples:
add([4, 2, 6, 7]) ==> 2
""" *)
(* 导入所需的库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(*
  sum_even_at_odd_indices l n
  一个辅助函数，用于计算列表 l 中，从索引 n 开始，
  位于奇数位置的偶数元素之和。
*)
Fixpoint sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0 (* 基本情况：空列表的和为 0 *)
  | h :: t => (* 递归情况：列表 l 由头部 h 和尾部 t 组成 *)
    (* 检查当前索引 n 是否为奇数，并且当前元素 h 是否为偶数 *)
    if andb (Nat.odd n) (Z.even h) then
      (* 如果是，则将当前元素 h 加入到对列表其余部分递归计算的结果中 *)
      h + sum_even_at_odd_indices t (S n)
    else
      (* 如果不是，则忽略当前元素，继续对列表其余部分进行递归计算 *)
      sum_even_at_odd_indices t (S n)
  end.

(*
  add_spec lst output
  程序 add 的规约。
  它规定了输入列表 lst 和输出 output 之间的一阶逻辑关系。
*)
Definition add_spec (lst : list Z) (output : Z) : Prop :=
  (* 前置条件: 输入列表 lst 不能为空 *)
  lst <> [] ->
  (* 后置条件: output 必须等于从索引 0 开始计算的“位于奇数位置的偶数元素之和” *)
  output = sum_even_at_odd_indices lst 0.