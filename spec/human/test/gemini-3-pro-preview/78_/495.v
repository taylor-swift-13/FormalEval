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

Example test_case_1 : problem_78_spec "73ABDBCB75322022EBDCEEFFAB4CDEF202020CBAABBBDDDDDDCCCCC111112345B67C1BB333AB4CDEF202020CBAABBB5DDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033CEEEF753BDCEEFAD2020123456789ABCDEABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555F0EAED44444555555A113DDBC20012212345B67CEEFAD890ABCDEF12345BBAA2020033444555555A7F9ABCDEF0BBB2BB333CA11D0D773BC5555" 178.
Proof.
  unfold problem_78_spec.
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String _ _) _ ] =>
      (apply cphr_prime; [ constructor | ]) ||
      (apply cphr_not_prime; [ intro H; inversion H | ])
  end.
Qed.