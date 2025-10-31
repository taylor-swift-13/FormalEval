(* def sum_squares(lst):
This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.

Examples:
For lst = [1,2,3] the output should be 6
For lst = [] the output should be 0
For lst = [-1,-5,2,-1,-5] the output should be -126
 *)
(* 引入所需的库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Import ListNotations.

(*
  sum_transformed 是一个辅助函数，它接受一个整数列表 l 和一个起始索引 n。
  它根据索引 n 对列表的头部元素进行转换，然后递归地对列表的其余部分进行求和。
*)
Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0 (* 空列表的和为 0 *)
  | h :: t =>
    (* 根据索引 n 的值对头部元素 h 进行转换 *)
    (if (n mod 3)%nat =? 0%nat then h * h (* 如果索引是 3 的倍数，则平方 *)
     (*
       [修正]: 将之前的 '&&' 替换为函数 'andb'
       如果索引是 4 的倍数但不是 3 的倍数，则立方
     *)
     else if andb ((n mod 4)%nat =? 0%nat) (negb ((n mod 3)%nat =? 0%nat)) then h * h * h
     else h) (* 否则，保持不变 *)
    + sum_transformed t (S n) (* 加上对列表其余部分递归调用的结果，索引加 1 *)
  end.

(*
  sum_squares_spec 定义了程序的规约。
  它是一个断言（Prop），说明了输入列表 lst 和输出结果 res 之间的关系。
  这个关系是：res 必须等于从索引 0 开始对 lst 调用 sum_transformed 的结果。
*)
Definition sum_squares_spec (lst : list Z) (res : Z) : Prop :=
  res = sum_transformed lst 0.