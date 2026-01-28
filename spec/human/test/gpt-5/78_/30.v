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

Example problem_78_test_7767ABCD23777 : problem_78_spec "7767ABCD23777" 10%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_prime "7"%char "767ABCD23777" 9 _ _).
  exact iphd_7.
  refine (cphr_prime "7"%char "67ABCD23777" 8 _ _).
  exact iphd_7.
  refine (cphr_not_prime "6"%char "7ABCD23777" 8 _ _).
  intro H; inversion H.
  refine (cphr_prime "7"%char "ABCD23777" 7 _ _).
  exact iphd_7.
  refine (cphr_not_prime "A"%char "BCD23777" 7 _ _).
  intro H; inversion H.
  refine (cphr_prime "B"%char "CD23777" 6 _ _).
  exact iphd_B.
  refine (cphr_not_prime "C"%char "D23777" 6 _ _).
  intro H; inversion H.
  refine (cphr_prime "D"%char "23777" 5 _ _).
  exact iphd_D.
  refine (cphr_prime "2"%char "3777" 4 _ _).
  exact iphd_2.
  refine (cphr_prime "3"%char "777" 3 _ _).
  exact iphd_3.
  refine (cphr_prime "7"%char "77" 2 _ _).
  exact iphd_7.
  refine (cphr_prime "7"%char "7" 1 _ _).
  exact iphd_7.
  refine (cphr_prime "7"%char "" 0 _ _).
  exact iphd_7.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_7767ABCD23777_Z_output : Z.of_nat 10 = 10%Z.
Proof.
  reflexivity.
Qed.