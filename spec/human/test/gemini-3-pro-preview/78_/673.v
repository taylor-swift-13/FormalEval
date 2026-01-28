Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Inductive is_prime_hex_digit : ascii -> Prop :=
| iphd_2 : is_prime_hex_digit "2"%char
| iphd_3 : is_prime_hex_digit "3"%char
| iphd_5 : is_prime_hex_digit "5"%char
| iphd_7 : is_prime_hex_digit "7"%char
| iphd_B : is_prime_hex_digit "B"%char
| iphd_D : is_prime_hex_digit "D"%char.

Inductive count_prime_hex_rel : string -> nat -> Prop :=
| cphr_nil : count_prime_hex_rel "" 0%nat
| cphr_prime : forall h t n, is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) (S n)
| cphr_not_prime : forall h t n, ~ is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) n.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  count_prime_hex_rel s output.

Ltac solve_count_prime :=
  unfold problem_78_spec;
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String ?c ?s) _ ] =>
      (apply cphr_prime; [ constructor | ]) ||
      (apply cphr_not_prime; [ let H := fresh in intro H; inversion H | ])
  end.

Example test_case_1 : problem_78_spec "1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBAA202002CEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1234567890ABCDEF12345BBAA20200" 61.
Proof.
  solve_count_prime.
Qed.