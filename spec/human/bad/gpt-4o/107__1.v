Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.

Inductive to_digits_rel : nat -> list nat -> Prop :=
| tdr_zero : to_digits_rel 0%nat nil
| tdr_step : forall n d ds, n > 0 -> d = n mod 10 ->
    to_digits_rel (n / 10) ds ->
    to_digits_rel n (d :: ds).

Inductive is_palindrome_rel : nat -> Prop :=
| ipr_pal : forall n ds, n > 0 -> to_digits_rel n ds -> ds = rev ds -> is_palindrome_rel n.

Inductive is_even_rel : nat -> Prop :=
| ier_even : forall n, n mod 2 = 0 -> is_even_rel n.

Inductive is_even_pal_rel : nat -> Prop :=
| iepr_build : forall n, is_palindrome_rel n -> is_even_rel n -> is_even_pal_rel n.

Inductive is_odd_pal_rel : nat -> Prop :=
| iopr_build : forall n, is_palindrome_rel n -> ~ is_even_rel n -> is_odd_pal_rel n.

Inductive count_in_range_rel : (nat -> Prop) -> nat -> nat -> Prop :=
| cir_zero : forall (P : nat -> Prop), count_in_range_rel P 0%nat 0%nat
| cir_hit : forall (P : nat -> Prop) k n, P (S k) -> count_in_range_rel P k n ->
   count_in_range_rel P (S k) (S n)
| cir_miss : forall (P : nat -> Prop) k n, ~ P (S k) -> count_in_range_rel P k n ->
   count_in_range_rel P (S k) n.

(* n 为正整数 *)
Definition problem_107_pre (n : nat) : Prop := n > 0.

Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  let '(e, o) := output in
  count_in_range_rel is_even_pal_rel n e /\
  count_in_range_rel is_odd_pal_rel n o.

Lemma to_digits_works : forall n ds, to_digits_rel n ds -> ds = rev ds -> is_palindrome_rel n.
Proof.
  intros n ds H_rel H_rev.
  apply ipr_pal with (ds := ds).
  - induction H_rel; lia.
  - assumption.
  - assumption.
Qed.

Lemma count_is_even_pal_rel : forall n e o,
  count_in_range_rel is_even_pal_rel n e ->
  count_in_range_rel is_odd_pal_rel n o ->
  problem_107_spec n (e, o).
Proof.
  intros n e o H_even H_odd.
  unfold problem_107_spec. split; assumption.
Qed.

Example problem_107_example :
  problem_107_spec 123 (8, 13).
Proof.
  apply count_is_even_pal_rel.
  - (* Prove count_in_range_rel for even palindromes *)
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [1]); auto; apply tdr_zero | apply ier_even; auto] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [2]); auto; apply tdr_step with (d := 2); auto; apply tdr_zero | apply ier_even; auto] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [4]); auto; apply tdr_zero | apply ier_even; auto] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [6]); auto; apply tdr_zero | apply ier_even; auto] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [8]); auto; apply tdr_zero | apply ier_even; auto] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iepr_build; [apply to_digits_works with (ds := [11]); auto; apply tdr_step with (d := 1); auto; apply tdr_zero | apply ier_even; auto] |]).
    apply cir_zero.
  - (* Prove count_in_range_rel for odd palindromes *)
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [1]); auto; apply tdr_zero | intro H; inversion H] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [3]); auto; apply tdr_zero | intro H; inversion H] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [5]); auto; apply tdr_zero | intro H; inversion H] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [7]); auto; apply tdr_zero | intro H; inversion H] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [9]); auto; apply tdr_zero | intro H; inversion H] |]).
    repeat (apply cir_miss; [intro H; inversion H]).
    repeat (apply cir_hit; [apply iopr_build; [apply to_digits_works with (ds := [11]); auto; apply tdr_step with (d := 1); auto; apply tdr_zero | intro H; inversion H] |]).
    apply cir_zero.
Qed.