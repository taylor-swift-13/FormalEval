Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Lia.
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

Example problem_131_test_952 :
  problem_131_spec 952%nat 45%nat.
Proof.
  unfold problem_131_spec.
  exists [2%nat; 5%nat; 9%nat].
  exists [5%nat; 9%nat].
  repeat split.
  - eapply gdr_step with (d := 2%nat) (ds := [5%nat; 9%nat]).
    + lia.
    + assert (Hmod952 : 2%nat = 952%nat mod 10%nat).
      { compute. reflexivity. }
      exact Hmod952.
    + assert (Hdiv952 : 952%nat / 10%nat = 95%nat).
      { compute. reflexivity. }
      rewrite Hdiv952.
      eapply gdr_step with (d := 5%nat) (ds := [9%nat]).
      * lia.
      * assert (Hmod95 : 5%nat = 95%nat mod 10%nat).
        { compute. reflexivity. }
        exact Hmod95.
      * assert (Hdiv95 : 95%nat / 10%nat = 9%nat).
        { compute. reflexivity. }
        rewrite Hdiv95.
        eapply gdr_step with (d := 9%nat) (ds := nil).
        -- lia.
        -- assert (Hmod9 : 9%nat = 9%nat mod 10%nat).
           { compute. reflexivity. }
           exact Hmod9.
        -- assert (Hdiv9 : 9%nat / 10%nat = 0%nat).
           { apply Nat.div_small. lia. }
           rewrite Hdiv9. apply gdr_zero.
  - apply fodr_even.
    + compute. reflexivity.
    + apply fodr_odd.
      * compute. reflexivity.
      * apply fodr_odd.
        -- compute. reflexivity.
        -- apply fodr_nil.
  - intros H. discriminate H.
  - intros _. apply pr_cons with (p_tail := 9%nat).
    + apply pr_cons with (p_tail := 1%nat).
      * apply pr_nil.
      * simpl. reflexivity.
    + compute. reflexivity.
Qed.