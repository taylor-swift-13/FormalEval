Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint count_prime_hex_digits (chars : list ascii) : nat :=
  match chars with
  | [] => 0
  | c :: rest => (if is_prime_hex_digit c then 1 else 0) + count_prime_hex_digits rest
  end.

Definition hex_key_spec (num : string) (result : nat) : Prop :=
  result = count_prime_hex_digits (string_to_list num).

Example test_hex_key_spec_AB : hex_key_spec "AB"%string 1%nat.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.

Example test_hex_key_spec_AB_Z :
  Z.of_nat (count_prime_hex_digits (string_to_list "AB"%string)) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_hex_key_spec_AB_resultZ :
  forall result, hex_key_spec "AB"%string result -> Z.of_nat result = 1%Z.
Proof.
  intros result H.
  unfold hex_key_spec in H.
  simpl in H.
  rewrite H.
  simpl.
  reflexivity.
Qed.