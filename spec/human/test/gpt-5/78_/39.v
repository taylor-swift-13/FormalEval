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

Example problem_78_test_1C679D999799A9B7CD23 : problem_78_spec "1C679D999799A9B7CD23" 8%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_not_prime "1"%char "C679D999799A9B7CD23" 8 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "C"%char "679D999799A9B7CD23" 8 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "6"%char "79D999799A9B7CD23" 8 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "7"%char "9D999799A9B7CD23" 7 _ _).
  exact iphd_7.
  refine (cphr_not_prime "9"%char "D999799A9B7CD23" 7 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "D"%char "999799A9B7CD23" 6 _ _).
  exact iphd_D.
  refine (cphr_not_prime "9"%char "99799A9B7CD23" 6 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "9799A9B7CD23" 6 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "799A9B7CD23" 6 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "7"%char "99A9B7CD23" 5 _ _).
  exact iphd_7.
  refine (cphr_not_prime "9"%char "9A9B7CD23" 5 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "A9B7CD23" 5 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "A"%char "9B7CD23" 5 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "B7CD23" 5 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "B"%char "7CD23" 4 _ _).
  exact iphd_B.
  refine (cphr_prime "7"%char "CD23" 3 _ _).
  exact iphd_7.
  refine (cphr_not_prime "C"%char "D23" 3 _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "D"%char "23" 2 _ _).
  exact iphd_D.
  refine (cphr_prime "2"%char "3" 1 _ _).
  exact iphd_2.
  refine (cphr_prime "3"%char "" 0 _ _).
  exact iphd_3.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_1C679D999799A9B7CD23_Z_output : Z.of_nat 8 = 8%Z.
Proof.
  reflexivity.
Qed.