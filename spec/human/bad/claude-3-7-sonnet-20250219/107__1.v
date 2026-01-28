Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Coq.Arith.PeanoNat Lia.
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
| cir_zero : forall (P : nat -> Prop), count_in_range_rel P 0 0
| cir_hit : forall (P : nat -> Prop) k n,
    P (S k) ->
    count_in_range_rel P k n ->
    count_in_range_rel P (S k) (S n)
| cir_miss : forall (P : nat -> Prop) k n,
    ~ P (S k) ->
    count_in_range_rel P k n ->
    count_in_range_rel P (S k) n.

Definition problem_107_pre (n : nat) : Prop := n > 0.

Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  let '(e, o) := output in
  count_in_range_rel is_even_pal_rel n e /\
  count_in_range_rel is_odd_pal_rel n o.

(* Proper structural recursion for digits_of: accumulator version *)

Fixpoint digits_of_aux (n acc : list nat) : list nat :=
  match n with
  | 0 => acc
  | _ => digits_of_aux (n / 10) ((n mod 10) :: acc)
  end.

Definition digits_of (n : nat) : list nat :=
  digits_of_aux n [].

Lemma to_digits_rel_of_aux : forall n acc,
  to_digits_rel n acc -> digits_of_aux n [] = acc.
Proof.
  induction n using nat_strong_induction; intros acc H.
  inversion H; subst.
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn0; auto.
    + f_equal. congruence.
    + lia.
Qed.

Lemma to_digits_rel_of n :
  n > 0 ->
  to_digits_rel n (digits_of n).
Proof.
  intros Hgt.
  unfold digits_of.
  revert n.
  induction n using nat_ind2; intros n0.
  - inversion 1.
  - simpl.
    destruct n0.
    + inversion 1.
    + simpl.
      apply tdr_step.
      * lia.
      * reflexivity.
      * apply IHn; lia.
Qed.

Lemma rev_digits_of_involutive n :
  rev (digits_of n) = digits_of n.
Proof.
  unfold digits_of.
  induction n using nat_strong_induction.
  simpl.
  destruct n.
  - reflexivity.
  - rewrite <- rev_involutive.
    induction (digits_of_aux (S n) []).
    + reflexivity.
    + simpl.
      f_equal.
      apply IHl.
Qed.

Lemma digits_of_palindrome_iff n :
  n > 0 ->
  is_palindrome_rel n <-> (digits_of n = rev (digits_of n)).
Proof.
  intros Hgt.
  split.
  - intros (ds & Hn & Htd & Hrev).
    apply to_digits_rel_of_aux in Htd.
    subst ds.
    rewrite <- rev_involutive.
    symmetry; assumption.
  - intros Hpal.
    apply ipr_pal with (ds := digits_of n).
    + assumption.
    + apply to_digits_rel_of; assumption.
    + assumption.
Qed.

Lemma even_rel_iff n : is_even_rel n <-> n mod 2 = 0.
Proof.
  split.
  - inversion 1; trivial.
  - intros H. constructor; assumption.
Qed.

Lemma is_even_pal_rel_iff n :
  is_even_pal_rel n <-> is_palindrome_rel n /\ is_even_rel n.
Proof.
  split; intros [Hpal Hev] || intros [Hpal Hev]; try constructor; auto.
Qed.

Lemma is_odd_pal_rel_iff n :
  is_odd_pal_rel n <-> is_palindrome_rel n /\ ~ is_even_rel n.
Proof.
  split; intros [Hpal Hne] || intros [Hpal Hne]; try constructor; auto.
Qed.

(* We now prove count_in_range_rel holds for input = 123 and output = (8, 13) *)

(* List palindromes up to 123:
1,2,3,4,5,6,7,8,9,11,22,33,44,55,66,77,88,99,101,111,121

Even palindromes: 2,4,6,8,22,44,66,88 (8 total)
Odd palindromes: the rest (13 total)

We'll prove count_in_range_rel is_even_pal_rel 123 8 and
count_in_range_rel is_odd_pal_rel 123 13 by induction *)

Example problem_107_123_example :
  problem_107_spec 123 (8, 13).
Proof.
  unfold problem_107_spec.
  split.

  (* count even palindrome *)
  assert (Hcount_even: count_in_range_rel is_even_pal_rel 123 8).
  {
    induction 123 as [|k IH].
    - constructor.
    - destruct (classic (is_even_pal_rel (S k))) as [Hpos | Hneg].
      + apply cir_hit; assumption.
      + apply cir_miss; assumption.
  }

  (* count odd palindrome *)
  assert (Hcount_odd: count_in_range_rel is_odd_pal_rel 123 13).
  {
    induction 123 as [|k IH].
    - constructor.
    - destruct (classic (is_odd_pal_rel (S k))) as [Hpos | Hneg].
      + apply cir_hit; assumption.
      + apply cir_miss; assumption.
  }

  split; assumption.
Qed.