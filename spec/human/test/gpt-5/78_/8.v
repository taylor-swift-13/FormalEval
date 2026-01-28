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

Example problem_78_test_ABCDEF : problem_78_spec "ABCDEF" 2%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_not_prime "A"%char "BCDEF" 2%nat (fun H : is_prime_hex_digit "A"%char => match H with end) _).
  refine (cphr_prime "B"%char "CDEF" 1%nat iphd_B _).
  refine (cphr_not_prime "C"%char "DEF" 1%nat (fun H : is_prime_hex_digit "C"%char => match H with end) _).
  refine (cphr_prime "D"%char "EF" 0%nat iphd_D _).
  refine (cphr_not_prime "E"%char "F" 0%nat (fun H : is_prime_hex_digit "E"%char => match H with end) _).
  refine (cphr_not_prime "F"%char "" 0%nat (fun H : is_prime_hex_digit "F"%char => match H with end) _).
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_ABCDEF_Z_output : Z.of_nat 2 = 2%Z.
Proof.
  reflexivity.
Qed.