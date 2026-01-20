Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.
Open Scope Z_scope.

Definition pow10Z (k : nat) : Z := Z.of_nat (Nat.pow 10 k).

Fixpoint sum_digits_aux (n : Z) (i : nat) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => Z.modulo (Z.div n (pow10Z i)) 10 + sum_digits_aux n (S i) k'
  end.

Definition sum_digits (n : Z) (k : nat) : Z := sum_digits_aux n 0 k.

Definition msd (n : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => Z.div n (pow10Z k')
  end.

Definition digits_len_prop (n : Z) (k : nat) : Prop :=
  0 <= n /\ ((n = 0 /\ k = 1)%nat \/ (n <> 0 /\ (pow10Z (Nat.pred k) <= n < pow10Z k)%Z)).

Definition signed_digit_sum (x : Z) (s : Z) : Prop :=
  (x >= 0 /\ exists k, digits_len_prop x k /\ s = sum_digits x k) \/
  (x < 0 /\ let n := Z.abs x in exists k, digits_len_prop n k /\ s = sum_digits n k - 2 * msd n k).

Definition good_number (x : Z) : Prop :=
  exists s, signed_digit_sum x s /\ 0 < s.

Inductive count_nums_rel : list Z -> Z -> Prop :=
| count_nil : count_nums_rel [] 0
| count_cons_good : forall x xs r,
    good_number x ->
    count_nums_rel xs r ->
    count_nums_rel (x :: xs) (r + 1)
| count_cons_bad : forall x xs r,
    ~ good_number x ->
    count_nums_rel xs r ->
    count_nums_rel (x :: xs) r.

Definition count_nums_spec (arr : list Z) (res : Z) : Prop :=
  count_nums_rel arr res.