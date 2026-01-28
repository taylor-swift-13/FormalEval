Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Coq.ZArith.ZArith.
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

Definition problem_107_pre (n : nat) : Prop := n > 0.

Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  let '(e, o) := output in
  count_in_range_rel is_even_pal_rel n e /\
  count_in_range_rel is_odd_pal_rel n o.

Lemma palindrome_123_test : 
  let n := 123%nat in
  problem_107_spec n (8%nat, 13%nat).
Proof.
  unfold n.
  unfold problem_107_spec.
  split.
  - (* Even palindromes count = 8 *)
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. } 
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. { 
      constructor.
      - constructor. 
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - constructor. lia.
    }
    apply cir_zero.
  - (* Odd palindromes count = 13 *)
    apply cir_hit. {
      constructor.
      - constructor. 
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_miss. { intro H; inversion H; inversion H0; inversion H1; lia. }
    apply cir_hit. {
      constructor.
      - constructor.
        + constructor; [lia|reflexivity|constructor].
        + reflexivity.
      - intro H; inversion H; lia.
    }
    apply cir_zero.
Qed.