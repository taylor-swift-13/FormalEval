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
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0 res.

Example test_sum_squares_123 :
  problem_142_spec [1%Z; 2%Z; 3%Z] 6%Z.
Proof.
  unfold problem_142_spec.
  (* Goal: sum_transformed_rel [1; 2; 3] 0 6 *)
  apply str_cons with (term := 1 * 1).
  - split.
    + intros _. reflexivity.
    + split.
      * intros [Hmod3false Hmod4true]. discriminate Hmod4true.
      * intros [Hmod3false Hmod4false]. discriminate Hmod3false.
  - apply str_cons with (term := 2).
    + split.
      * intros H. discriminate H.
      * split.
        { intros [Hmod3false Hmod4true]. discriminate Hmod4true. }
        { intros [Hmod3false Hmod4false]. reflexivity. }
    + apply str_cons with (term := 3).
      * split.
        { intros H. discriminate H. }
        { split.
          - intros [Hmod3false Hmod4true]. discriminate Hmod4true.
          - intros [Hmod3false Hmod4false]. reflexivity.
        }
      * apply str_nil.
Qed.