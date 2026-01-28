(* 引入 Coq 的自然数和列表库 *)
Require Import Nat.
Require Import List.
Require Import Factorial.
Import ListNotations.

(* n 为自然数，无额外约束 *)
Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).

(* 实现函数 f *)
Fixpoint f (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' =>
    let l := f n' in
    let i := S n' in
    let elem := if even i then fact i else Nat.div (i * (i + 1)) 2 in
    l ++ [elem]
  end.

(* 证明 f 满足 problem_106_spec *)
Lemma f_correct : forall n, problem_106_spec n (f n).
Proof.
  intros n.
  unfold problem_106_spec.
  induction n as [| n' IH].
  - simpl. split.
    + reflexivity.
    + intros i H1 H2. lia. (* No i satisfies 1 <= i <= 0 *)
  - simpl. destruct IH as [IHlen IHnth].
    split.
    + simpl. rewrite app_length. simpl. lia.
    + intros i H1 H2.
      destruct (Nat.eq_dec i (S n')) as [Heqi | Hnei].
      * subst. simpl. rewrite nth_error_app2.
        -- rewrite IHlen. simpl. lia.
        -- rewrite IHlen. simpl. lia.
        -- simpl. rewrite Nat.sub_diag. simpl. reflexivity.
      * apply IHnth.
        lia.
Qed.

(* 测试用例 *)
Example test_f_5 : f 5 = [1; 2; 6; 24; 15].
Proof.
  simpl. reflexivity.
Qed.

Qed.