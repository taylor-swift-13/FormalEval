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

(* 任意整数列表（允许为空） *)
Definition problem_142_pre (lst : list Z) : Prop := True.

(* 规格：结果等于从索引 0 开始的 sum_transformed_rel 之和 *)
Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_problem_142 : problem_142_spec [1; 2; 3] 6.
Proof.
  unfold problem_142_spec.
  (* Index 0, val 1. 0%3 = 0 -> term = 1*1 = 1. Remaining sum = 5. *)
  replace 6 with (1 + 5) by reflexivity.
  apply str_cons with (term := 1).
  {
    repeat split; intros H.
    - (* 0 mod 3 == 0 *) reflexivity.
    - (* 0 mod 3 != 0 ... *) simpl in H; destruct H; discriminate.
    - (* 0 mod 3 != 0 ... *) simpl in H; destruct H; discriminate.
  }
  (* Index 1, val 2. 1%3 != 0, 1%4 != 0 -> term = 2. Remaining sum = 3. *)
  replace 5 with (2 + 3) by reflexivity.
  apply str_cons with (term := 2).
  {
    repeat split; intros H.
    - (* 1 mod 3 == 0 *) simpl in H; discriminate.
    - (* 1 mod 3 != 0, 1 mod 4 == 0 *) simpl in H; destruct H as [_ H4]; discriminate.
    - (* 1 mod 3 != 0, 1 mod 4 != 0 *) reflexivity.
  }
  (* Index 2, val 3. 2%3 != 0, 2%4 != 0 -> term = 3. Remaining sum = 0. *)
  replace 3 with (3 + 0) by reflexivity.
  apply str_cons with (term := 3).
  {
    repeat split; intros H.
    - (* 2 mod 3 == 0 *) simpl in H; discriminate.
    - (* 2 mod 3 != 0, 2 mod 4 == 0 *) simpl in H; destruct H as [_ H4]; discriminate.
    - (* 2 mod 3 != 0, 2 mod 4 != 0 *) reflexivity.
  }
  (* End of list *)
  apply str_nil.
Qed.