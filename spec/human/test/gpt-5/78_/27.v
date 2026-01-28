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

Example problem_78_test_1679D99999ABCD23 : problem_78_spec "1679D99999ABCD23" 6%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_not_prime "1"%char "679D99999ABCD23" 6%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "6"%char "79D99999ABCD23" 6%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "7"%char "9D99999ABCD23" 5%nat _ _).
  exact iphd_7.
  refine (cphr_not_prime "9"%char "D99999ABCD23" 5%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "D"%char "99999ABCD23" 4%nat _ _).
  exact iphd_D.
  refine (cphr_not_prime "9"%char "9999ABCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "999ABCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "99ABCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "9ABCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "9"%char "ABCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_not_prime "A"%char "BCD23" 4%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "B"%char "CD23" 3%nat _ _).
  exact iphd_B.
  refine (cphr_not_prime "C"%char "D23" 3%nat _ _).
  unfold not; intros H; inversion H.
  refine (cphr_prime "D"%char "23" 2%nat _ _).
  exact iphd_D.
  refine (cphr_prime "2"%char "3" 1%nat _ _).
  exact iphd_2.
  refine (cphr_prime "3"%char "" 0%nat _ _).
  exact iphd_3.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_1679D99999ABCD23_Z_output : Z.of_nat 6 = 6%Z.
Proof.
  reflexivity.
Qed.