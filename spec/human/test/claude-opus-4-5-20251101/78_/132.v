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

Lemma not_prime_A : ~ is_prime_hex_digit "A"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_C : ~ is_prime_hex_digit "C"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_F : ~ is_prime_hex_digit "F"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_1 : ~ is_prime_hex_digit "1"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_4 : ~ is_prime_hex_digit "4"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_6 : ~ is_prime_hex_digit "6"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_0 : ~ is_prime_hex_digit "0"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_E : ~ is_prime_hex_digit "E"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_8 : ~ is_prime_hex_digit "8"%char.
Proof. intro H; inversion H. Qed.

Lemma not_prime_9 : ~ is_prime_hex_digit "9"%char.
Proof. intro H; inversion H. Qed.

Ltac solve_not_prime :=
  match goal with
  | |- ~ is_prime_hex_digit "A"%char => exact not_prime_A
  | |- ~ is_prime_hex_digit "C"%char => exact not_prime_C
  | |- ~ is_prime_hex_digit "F"%char => exact not_prime_F
  | |- ~ is_prime_hex_digit "1"%char => exact not_prime_1
  | |- ~ is_prime_hex_digit "4"%char => exact not_prime_4
  | |- ~ is_prime_hex_digit "6"%char => exact not_prime_6
  | |- ~ is_prime_hex_digit "0"%char => exact not_prime_0
  | |- ~ is_prime_hex_digit "E"%char => exact not_prime_E
  | |- ~ is_prime_hex_digit "8"%char => exact not_prime_8
  | |- ~ is_prime_hex_digit "9"%char => exact not_prime_9
  end.

Ltac solve_prime :=
  match goal with
  | |- is_prime_hex_digit "2"%char => exact iphd_2
  | |- is_prime_hex_digit "3"%char => exact iphd_3
  | |- is_prime_hex_digit "5"%char => exact iphd_5
  | |- is_prime_hex_digit "7"%char => exact iphd_7
  | |- is_prime_hex_digit "B"%char => exact iphd_B
  | |- is_prime_hex_digit "D"%char => exact iphd_D
  end.

Ltac solve_count :=
  match goal with
  | |- count_prime_hex_rel "" _ => exact cphr_nil
  | |- count_prime_hex_rel (String ?h ?t) (S ?n) =>
      apply cphr_prime; [solve_prime | solve_count]
  | |- count_prime_hex_rel (String ?h ?t) ?n =>
      apply cphr_not_prime; [solve_not_prime | solve_count]
  end.

Example test_hex_key_long : problem_78_spec "ACDF12345B67C2022EEEFAD890ABCDEF12345BBAA202001111887215E753BD9CEFF23BCCBBD4" 33%nat.
Proof.
  unfold problem_78_spec.
  solve_count.
Qed.