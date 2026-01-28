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

Lemma odd_5 : Nat.odd 5 = true.
Proof. reflexivity. Qed.

Lemma product_single : forall x, product_rel [x] x.
Proof.
  intros x.
  apply pr_cons with (d := x) (ds := nil) (p_tail := 1).
  - apply pr_nil.
  - simpl. auto with arith.
Qed.

Example test_case_5 : problem_131_pre 5 /\ problem_131_spec 5 5.
Proof.
  split.
  - unfold problem_131_pre. auto with arith.
  - unfold problem_131_spec.
    exists [5], [5].
    split.
    + apply gdr_step with (d := 5).
      * auto with arith.
      * reflexivity.
      * apply gdr_step with (d := 0).
        { auto with arith. }
        { reflexivity. }
        { apply gdr_zero. }
    + split.
      * apply fodr_odd.
        { apply odd_5. }
        { apply fodr_nil. }
      * split.
        { intros H. discriminate H. }
        { intros H. apply product_single. }
Qed.