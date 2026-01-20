(* HumanEval 78 - Inductive Spec *)
Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Inductive is_prime_hex_digit : ascii -> Prop :=
| iphd_2 : is_prime_hex_digit "2"%char
| iphd_3 : is_prime_hex_digit "3"%char
| iphd_5 : is_prime_hex_digit "5"%char
| iphd_7 : is_prime_hex_digit "7"%char
| iphd_B : is_prime_hex_digit "B"%char
| iphd_D : is_prime_hex_digit "D"%char.

Inductive count_prime_hex_rel : list ascii -> nat -> Prop :=
| cphr_nil : count_prime_hex_rel nil 0%nat
| cphr_prime : forall h t n, is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (h :: t) (S n)
| cphr_not_prime : forall h t n, ~ is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (h :: t) n.

Definition hex_key_spec (s : list ascii) (output : nat) : Prop :=
  count_prime_hex_rel s output.

Example hex_key_spec_AB: hex_key_spec ("A"%char :: "B"%char :: nil) 1%nat.
Proof.
  unfold hex_key_spec.
  apply cphr_not_prime. intro H. inversion H.
  apply cphr_prime. constructor. constructor.
Qed.

