Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.micromega.Lia.
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

(* n 为正整数 *)
Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  exists ds odd_ds, get_digits_rel n ds /\
    filter_odd_digits_rel ds odd_ds /\
    (odd_ds = nil -> output = 0%nat) /\
    (odd_ds <> nil -> product_rel odd_ds output).

Example test_problem_131 : problem_131_spec 4 0.
Proof.
  unfold problem_131_spec.
  exists [4], [].
  repeat split.
  - apply gdr_step with (n := 4) (d := 4) (ds := nil).
    + lia.
    + reflexivity.
    + replace (4 / 10) with 0 by reflexivity.
      apply gdr_zero.
  - apply fodr_even.
    + reflexivity.
    + apply fodr_nil.
  - intro H. reflexivity.
  - intro H. contradiction.
Qed.