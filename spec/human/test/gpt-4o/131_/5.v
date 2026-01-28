Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Inductive get_digits_rel : nat -> list nat -> Prop :=
| gdr_zero : get_digits_rel 0%nat nil
| gdr_step : forall n d ds, n > 0 -> d = n mod 10 ->
    get_digits_rel (n / 10) ds ->
    get_digits_rel n (d :: ds).

Inductive filter_odd_digits_rel : list nat -> list nat -> Prop :=
| fodr_nil : filter_odd_digits_rel nil nil
| fodr_odd : forall d ds res, Nat.odd d = true -> filter_odd_digits_rel ds res ->
    filter_odd_digits_rel (d :: ds) (d :: res)
| fodr_even : forall d ds res, Nat.odd d = false -> filter_odd_digits_rel ds res ->
    filter_odd_digits_rel (d :: ds) res.

Inductive product_rel : list nat -> nat -> Prop :=
| pr_nil : product_rel nil 1%nat
| pr_cons : forall d ds p p_tail, product_rel ds p_tail -> p = d * p_tail ->
    product_rel (d :: ds) p.

Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  exists ds odd_ds, get_digits_rel n ds /\
    filter_odd_digits_rel ds odd_ds /\
    (odd_ds = nil -> output = 0%nat) /\
    (odd_ds <> nil -> product_rel odd_ds output).

Example test_case_1:
  problem_131_spec 98765 315.
Proof.
  unfold problem_131_spec.
  exists [5;6;7;8;9], [5;7;9].
  split.
  - apply gdr_step with (d := 5) (ds := [6;7;8;9]).
    + apply Nat.lt_0_succ.
    + reflexivity.
    + apply gdr_step with (d := 6) (ds := [7;8;9]).
      * apply Nat.lt_0_succ.
      * reflexivity.
      * apply gdr_step with (d := 7) (ds := [8;9]).
        -- apply Nat.lt_0_succ.
        -- reflexivity.
        -- apply gdr_step with (d := 8) (ds := [9]).
           ++ apply Nat.lt_0_succ.
           ++ reflexivity.
           ++ apply gdr_step with (d := 9) (ds := nil).
              ** apply Nat.lt_0_succ.
              ** reflexivity.
              ** apply gdr_zero.
  - split.
    + apply fodr_odd.
      * unfold Nat.odd. reflexivity.
      * apply fodr_even.
        -- unfold Nat.odd. reflexivity.
        -- apply fodr_odd.
           ++ unfold Nat.odd. reflexivity.
           ++ apply fodr_even.
              ** unfold Nat.odd. reflexivity.
              ** apply fodr_odd.
                 --- unfold Nat.odd. reflexivity.
                 --- apply fodr_nil.
    + split.
      * intros H. inversion H.
      * intros _. apply pr_cons with (p_tail := 63).
        -- apply pr_cons with (p_tail := 9).
           ++ apply pr_cons with (p_tail := 1).
              ** apply pr_nil.
              ** simpl. reflexivity.
           ++ simpl. reflexivity.
        -- simpl. reflexivity.
Qed.