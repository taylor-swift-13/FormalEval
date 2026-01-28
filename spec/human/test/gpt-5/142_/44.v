Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Lia.
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

Example test_case_sum_squares :
  problem_142_spec [3%Z; 6%Z; 9%Z; 12%Z; 15%Z; 21%Z; 24%Z; 27%Z; 30%Z] 31167%Z.
Proof.
  unfold problem_142_spec.
  replace 31167%Z with (9%Z + 31158%Z) by lia.
  apply (str_cons 3%Z [6%Z; 9%Z; 12%Z; 15%Z; 21%Z; 24%Z; 27%Z; 30%Z] 0%nat 31158%Z 9%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 31158%Z with (6%Z + 31152%Z) by lia.
  apply (str_cons 6%Z [9%Z; 12%Z; 15%Z; 21%Z; 24%Z; 27%Z; 30%Z] 1%nat 31152%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 31152%Z with (9%Z + 31143%Z) by lia.
  apply (str_cons 9%Z [12%Z; 15%Z; 21%Z; 24%Z; 27%Z; 30%Z] 2%nat 31143%Z 9%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 31143%Z with (144%Z + 30999%Z) by lia.
  apply (str_cons 12%Z [15%Z; 21%Z; 24%Z; 27%Z; 30%Z] 3%nat 30999%Z 144%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 30999%Z with (3375%Z + 27624%Z) by lia.
  apply (str_cons 15%Z [21%Z; 24%Z; 27%Z; 30%Z] 4%nat 27624%Z 3375%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 27624%Z with (21%Z + 27603%Z) by lia.
  apply (str_cons 21%Z [24%Z; 27%Z; 30%Z] 5%nat 27603%Z 21%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 27603%Z with (576%Z + 27027%Z) by lia.
  apply (str_cons 24%Z [27%Z; 30%Z] 6%nat 27027%Z 576%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 27027%Z with (27%Z + 27000%Z) by lia.
  apply (str_cons 27%Z [30%Z] 7%nat 27000%Z 27%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 30%Z [] 8%nat 0%Z 27000%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_nil 9%nat).
Qed.