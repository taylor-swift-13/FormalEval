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

Lemma not_prime_7 : is_prime_hex_digit "7"%char.
Proof. exact iphd_7. Qed.

Lemma not_prime_5 : is_prime_hex_digit "5"%char.
Proof. exact iphd_5. Qed.

Lemma not_prime_3 : is_prime_hex_digit "3"%char.
Proof. exact iphd_3. Qed.

Lemma not_prime_B : is_prime_hex_digit "B"%char.
Proof. exact iphd_B. Qed.

Lemma not_prime_D : is_prime_hex_digit "D"%char.
Proof. exact iphd_D. Qed.

Lemma not_prime_2 : is_prime_hex_digit "2"%char.
Proof. exact iphd_2. Qed.

Lemma np_C : ~ is_prime_hex_digit "C"%char.
Proof. intro H; inversion H. Qed.

Lemma np_E : ~ is_prime_hex_digit "E"%char.
Proof. intro H; inversion H. Qed.

Lemma np_F : ~ is_prime_hex_digit "F"%char.
Proof. intro H; inversion H. Qed.

Lemma np_A : ~ is_prime_hex_digit "A"%char.
Proof. intro H; inversion H. Qed.

Lemma np_0 : ~ is_prime_hex_digit "0"%char.
Proof. intro H; inversion H. Qed.

Lemma np_1 : ~ is_prime_hex_digit "1"%char.
Proof. intro H; inversion H. Qed.

Lemma np_4 : ~ is_prime_hex_digit "4"%char.
Proof. intro H; inversion H. Qed.

Lemma np_6 : ~ is_prime_hex_digit "6"%char.
Proof. intro H; inversion H. Qed.

Lemma np_8 : ~ is_prime_hex_digit "8"%char.
Proof. intro H; inversion H. Qed.

Lemma np_9 : ~ is_prime_hex_digit "9"%char.
Proof. intro H; inversion H. Qed.

Example test_hex_key_long : problem_78_spec "753BDCEEFAD20201234567F89ABCDEF0" 14%nat.
Proof.
  unfold problem_78_spec.
  apply cphr_prime. exact iphd_7.
  apply cphr_prime. exact iphd_5.
  apply cphr_prime. exact iphd_3.
  apply cphr_prime. exact iphd_B.
  apply cphr_prime. exact iphd_D.
  apply cphr_not_prime. exact np_C.
  apply cphr_not_prime. exact np_E.
  apply cphr_not_prime. exact np_E.
  apply cphr_not_prime. exact np_F.
  apply cphr_not_prime. exact np_A.
  apply cphr_prime. exact iphd_D.
  apply cphr_prime. exact iphd_2.
  apply cphr_not_prime. exact np_0.
  apply cphr_prime. exact iphd_2.
  apply cphr_not_prime. exact np_0.
  apply cphr_not_prime. exact np_1.
  apply cphr_prime. exact iphd_2.
  apply cphr_prime. exact iphd_3.
  apply cphr_not_prime. exact np_4.
  apply cphr_prime. exact iphd_5.
  apply cphr_not_prime. exact np_6.
  apply cphr_prime. exact iphd_7.
  apply cphr_not_prime. exact np_F.
  apply cphr_not_prime. exact np_8.
  apply cphr_not_prime. exact np_9.
  apply cphr_not_prime. exact np_A.
  apply cphr_prime. exact iphd_B.
  apply cphr_not_prime. exact np_C.
  apply cphr_prime. exact iphd_D.
  apply cphr_not_prime. exact np_E.
  apply cphr_not_prime. exact np_F.
  apply cphr_not_prime. exact np_0.
  exact cphr_nil.
Qed.