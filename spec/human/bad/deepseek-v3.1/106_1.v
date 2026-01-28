Require Import Nat.
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

(* 辅助函数定义 *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S m => (S m) * fact m
  end.

Definition sum_to_n (n : nat) : nat :=
  Nat.div (n * (n + 1)) 2.

(* 偶数判断函数 *)
Definition even (n : nat) : bool :=
  Nat.even n.

(* n 为自然数，无额外约束 *)
Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).

(* 主函数定义 *)
Fixpoint f (n : nat) : list nat :=
  match n with
  | O => []
  | S m => 
      let prev := f m in
      let i := S m in
      if even i then prev ++ [fact i]
      else prev ++ [sum_to_n i]
  end.

(* 验证测试用例 *)
Example test_f_5 : f 5 = [1; 2; 6; 24; 15].
Proof.
  compute.
  reflexivity.
Qed.

(* 辅助引理：nth_error 在列表追加时的行为 *)
Lemma nth_error_app_right : forall A (l1 l2 : list A) n,
  n >= length l1 ->
  nth_error (l1 ++ l2) n = nth_error l2 (n - length l1).
Proof.
  intros A l1 l2 n H.
  revert n H.
  induction l1 as [|x l1 IH]; intros n H.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - simpl in *. destruct n.
    + lia.
    + simpl. apply IH. lia.
Qed.

Lemma nth_error_app_left : forall A (l1 l2 : list A) n,
  n < length l1 ->
  nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  intros A l1 l2 n H.
  revert n H.
  induction l1 as [|x l1 IH]; intros n H.
  - simpl in H. lia.
  - destruct n.
    + reflexivity.
    + simpl. apply IH. simpl in H. lia.
Qed.

(* 完整的规范证明 *)
Theorem f_satisfies_spec : forall n, problem_106_pre n -> problem_106_spec n (f n).
Proof.
  intros n Hpre.
  unfold problem_106_spec.
  split.
  - (* 证明长度正确 *)
    induction n as [|n IH].
    + reflexivity.
    + simpl. rewrite app_length. simpl. lia.
  - (* 证明元素内容正确 *)
    intros i H1 H2.
    
    (* 对n进行归纳 *)
    induction n as [|n IH].
    + lia.
    + simpl.
      destruct (even (S n)) eqn:Heven.
      * (* 偶数情况 *)
        destruct (lt_eq_lt_dec i (S n)) as [[Hi|Hi]|Hi].
        -- (* i < S n *)
           rewrite nth_error_app_left.
           ++ apply IH; lia.
           ++ assert (Hlen: length (f n) = n).
              { clear IH H1 H2 i. induction n; simpl; rewrite app_length; simpl; lia. }
              rewrite Hlen. lia.
        -- (* i = S n *)
           subst i.
           rewrite nth_error_app_right.
           ++ simpl. rewrite Nat.sub_diag. simpl. reflexivity.
           ++ assert (Hlen: length (f n) = n).
              { clear IH. induction n; simpl; rewrite app_length; simpl; lia. }
              rewrite Hlen. lia.
        -- (* i > S n *) lia.
      * (* 奇数情况 *)
        destruct (lt_eq_lt_dec i (S n)) as [[Hi|Hi]|Hi].
        -- (* i < S n *)
           rewrite nth_error_app_left.
           ++ apply IH; lia.
           ++ assert (Hlen: length (f n) = n).
              { clear IH H1 H2 i. induction n; simpl; rewrite app_length; simpl; lia. }
              rewrite Hlen. lia.
        -- (* i = S n *)
           subst i.
           rewrite nth_error_app_right.
           ++ simpl. rewrite Nat.sub_diag. simpl. reflexivity.
           ++ assert (Hlen: length (f n) = n).
              { clear IH. induction n; simpl; rewrite app_length; simpl; lia. }
              rewrite Hlen. lia.
        -- (* i > S n *) lia.
Qed.

(* 直接验证规范 *)
Lemma spec_verification : problem_106_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold problem_106_spec.
  split.
  - reflexivity.
  - intros i H1 H2.
    destruct i as [|i].
    + lia.
    + destruct i as [|i].
      * lia.
      + destruct i as [|i].
        { simpl. reflexivity. }
        + destruct i as [|i].
          { simpl. reflexivity. }
          + destruct i as [|i].
            { simpl. reflexivity. }
            + lia.
Qed.