Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.

Open Scope Z_scope.

Definition is_even_digit (c : ascii) : bool :=
  match c with
  | "0"%char | "2"%char | "4"%char | "6"%char | "8"%char => true
  | _ => false
  end.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

Fixpoint count_even_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_even_digit c then 1 else 0) + count_even_digits rest
  end.

Fixpoint count_odd_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_odd_digit c then 1 else 0) + count_odd_digits rest
  end.

Definition even_odd_count_spec (num : Z) (even_count : Z) (odd_count : Z) : Prop :=
  forall (str_repr : list ascii),
    (forall c, In c str_repr -> is_even_digit c = true \/ is_odd_digit c = true \/ c = "-"%char) ->
    even_count = count_even_digits str_repr /\
    odd_count = count_odd_digits str_repr.

Example test_case_7_counts:
  count_even_digits ("7"%char :: nil) = 0 /\
  count_odd_digits ("7"%char :: nil) = 1.
Proof.
  simpl.
  split; reflexivity.
Qed.

Example test_case_7_pair:
  (count_even_digits ("7"%char :: nil), count_odd_digits ("7"%char :: nil)) = (0, 1).
Proof.
  simpl.
  reflexivity.
Qed.

Example allowed_chars_7:
  forall c, In c ("7"%char :: nil) -> is_even_digit c = true \/ is_odd_digit c = true \/ c = "-"%char.
Proof.
  intros c H.
  simpl in H.
  destruct H as [H | H].
  - subst. right. left. reflexivity.
  - contradiction.
Qed.