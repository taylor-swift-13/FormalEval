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

Example problem_131_test_25 :
  problem_131_spec 25%nat 5%nat.
Proof.
  unfold problem_131_spec.
  exists [5%nat; 2%nat].
  exists [5%nat].
  repeat split.
  - eapply gdr_step with (d := 5%nat) (ds := [2%nat]).
    + lia.
    + assert (Hmod25 : 25%nat mod 10%nat = 5%nat) by (compute; reflexivity).
      rewrite Hmod25. reflexivity.
    + assert (Hdiv25 : 25%nat / 10%nat = 2%nat) by (compute; reflexivity).
      rewrite Hdiv25.
      eapply gdr_step with (d := 2%nat) (ds := nil).
      * lia.
      * assert (Hmod2 : 2%nat mod 10%nat = 2%nat).
        { apply Nat.mod_small. lia. }
        rewrite Hmod2. reflexivity.
      * assert (Hdiv2 : 2%nat / 10%nat = 0%nat).
        { apply Nat.div_small. lia. }
        rewrite Hdiv2. apply gdr_zero.
  - apply fodr_odd.
    + compute. reflexivity.
    + apply fodr_even.
      * compute. reflexivity.
      * apply fodr_nil.
  - intros H. discriminate H.
  - intros _. apply pr_cons with (p_tail := 1%nat).
    + apply pr_nil.
    + simpl. reflexivity.
Qed.