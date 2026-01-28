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

Example problem_78_test_776B7ABCD23777 : problem_78_spec "776B7ABCD23777" 11%nat.
Proof.
  unfold problem_78_spec.
  apply (cphr_prime "7"%char "76B7ABCD23777" 10).
  exact iphd_7.
  apply (cphr_prime "7"%char "6B7ABCD23777" 9).
  exact iphd_7.
  apply (cphr_not_prime "6"%char "B7ABCD23777" 9).
  unfold not; intros H; inversion H.
  apply (cphr_prime "B"%char "7ABCD23777" 8).
  exact iphd_B.
  apply (cphr_prime "7"%char "ABCD23777" 7).
  exact iphd_7.
  apply (cphr_not_prime "A"%char "BCD23777" 7).
  unfold not; intros H; inversion H.
  apply (cphr_prime "B"%char "CD23777" 6).
  exact iphd_B.
  apply (cphr_not_prime "C"%char "D23777" 6).
  unfold not; intros H; inversion H.
  apply (cphr_prime "D"%char "23777" 5).
  exact iphd_D.
  apply (cphr_prime "2"%char "3777" 4).
  exact iphd_2.
  apply (cphr_prime "3"%char "777" 3).
  exact iphd_3.
  apply (cphr_prime "7"%char "77" 2).
  exact iphd_7.
  apply (cphr_prime "7"%char "7" 1).
  exact iphd_7.
  apply (cphr_prime "7"%char "" 0).
  exact iphd_7.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_776B7ABCD23777_Z_output : Z.of_nat 11 = 11%Z.
Proof.
  reflexivity.
Qed.