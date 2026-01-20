Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial n'
  end.

Fixpoint sum_1_to_n (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_1_to_n n'
  end.

Definition f_element (i : nat) : Z :=
  if Nat.even i then factorial i
  else sum_1_to_n i.

Fixpoint f_list (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => f_list n' ++ [f_element n]
  end.

Definition f_spec (n : nat) (result : list Z) : Prop :=
  result = f_list n /\
  length result = n /\
  forall i : nat, (1 <= i <= n)%nat ->
    nth (i - 1) result 0 = f_element i.

Example test_f_list_15 : f_list 15 = [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z; 120%Z].
Proof.
  simpl.
  reflexivity.
Qed.

Lemma f_list_length : forall n, length (f_list n) = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite app_length. simpl. rewrite IHn. lia.
Qed.

Lemma nth_app_right : forall (A : Type) (l1 l2 : list A) (d : A) (n : nat),
  n = length l1 -> nth n (l1 ++ l2) d = nth 0 l2 d.
Proof.
  intros A l1 l2 d n Hlen.
  subst n.
  rewrite app_nth2.
  - rewrite Nat.sub_diag. reflexivity.
  - lia.
Qed.

Lemma nth_app_left : forall (A : Type) (l1 l2 : list A) (d : A) (n : nat),
  (n < length l1)%nat -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1 l2 d n Hlt.
  apply app_nth1. exact Hlt.
Qed.

Lemma f_list_nth : forall n i, (1 <= i <= n)%nat -> nth (i - 1) (f_list n) 0 = f_element i.
Proof.
  induction n.
  - intros i H. lia.
  - intros i H.
    simpl.
    destruct (Nat.eq_dec i (S n)).
    + subst i.
      rewrite nth_app_right with (l2 := [f_element (S n)]).
      * simpl. reflexivity.
      * rewrite f_list_length. lia.
    + assert (Hi : (1 <= i <= n)%nat) by lia.
      rewrite nth_app_left.
      * apply IHn. exact Hi.
      * rewrite f_list_length. lia.
Qed.

Example test_f_spec_15 : f_spec 15 [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z; 120%Z].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      assert (Heq : [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z; 120%Z] = f_list 15) by reflexivity.
      rewrite Heq.
      apply f_list_nth.
      exact Hi.
Qed.