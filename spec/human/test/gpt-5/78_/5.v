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

Example problem_78_test_123456789ABCDEF0 : problem_78_spec "123456789ABCDEF0" 6%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_not_prime "1"%char "23456789ABCDEF0" 6 (fun H => match H with end) _).
  refine (cphr_prime "2"%char "3456789ABCDEF0" 5 iphd_2 _).
  refine (cphr_prime "3"%char "456789ABCDEF0" 4 iphd_3 _).
  refine (cphr_not_prime "4"%char "56789ABCDEF0" 4 (fun H => match H with end) _).
  refine (cphr_prime "5"%char "6789ABCDEF0" 3 iphd_5 _).
  refine (cphr_not_prime "6"%char "789ABCDEF0" 3 (fun H => match H with end) _).
  refine (cphr_prime "7"%char "89ABCDEF0" 2 iphd_7 _).
  refine (cphr_not_prime "8"%char "9ABCDEF0" 2 (fun H => match H with end) _).
  refine (cphr_not_prime "9"%char "ABCDEF0" 2 (fun H => match H with end) _).
  refine (cphr_not_prime "A"%char "BCDEF0" 2 (fun H => match H with end) _).
  refine (cphr_prime "B"%char "CDEF0" 1 iphd_B _).
  refine (cphr_not_prime "C"%char "DEF0" 1 (fun H => match H with end) _).
  refine (cphr_prime "D"%char "EF0" 0 iphd_D _).
  refine (cphr_not_prime "E"%char "F0" 0 (fun H => match H with end) _).
  refine (cphr_not_prime "F"%char "0" 0 (fun H => match H with end) _).
  refine (cphr_not_prime "0"%char "" 0 (fun H => match H with end) _).
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_123456789ABCDEF0_Z_output : Z.of_nat 6 = 6%Z.
Proof.
  reflexivity.
Qed.