(* HumanEval 142 - Inductive Spec version *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

(* 按索引对元素做变换：
   - 索引是 3 的倍数 -> 平方
   - 索引是 4 的倍数且不是 3 的倍数 -> 立方
   - 其它保持不变
   最后对所有转换后的数求和。*)

Inductive sum_transformed_rel : list Z -> nat -> Z -> Prop :=
| str_nil : forall i, sum_transformed_rel [] i 0%Z
| str_cons : forall h t i s_tail term,
   (* term 是按规则对 h 应用后的值 *)
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

(* 规格：结果等于从索引 0 开始的 sum_transformed_rel 之和 *)
Definition sum_squares_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.



