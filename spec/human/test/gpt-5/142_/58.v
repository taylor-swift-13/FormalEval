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

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_case_sum_squares :
  problem_142_spec [0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 35%Z.
Proof.
  unfold problem_142_spec.
  replace 35%Z with (0%Z + 35%Z) by lia.
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 0%nat 35%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_r; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 1%nat 35%Z 0%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 3%Z; 0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 2%nat 35%Z 0%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 0%Z [3%Z; 0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 3%nat 35%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_r; reflexivity
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 3%Z [0%Z; 0%Z; 8%Z; 0%Z; 0%Z] 4%nat 8%Z 27%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 0%Z [0%Z; 8%Z; 0%Z; 0%Z] 5%nat 8%Z 0%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 0%Z [8%Z; 0%Z; 0%Z] 6%nat 8%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_r; reflexivity
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 8%Z [0%Z; 0%Z] 7%nat 0%Z 8%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 0%Z [0%Z] 8%nat 0%Z 0%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; rewrite Z.mul_0_r; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 0%Z [] 9%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_r; reflexivity
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.