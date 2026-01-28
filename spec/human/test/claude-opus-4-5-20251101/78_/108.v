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

Lemma not_prime_C : ~ is_prime_hex_digit "C"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_prime_E : ~ is_prime_hex_digit "E"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_prime_F : ~ is_prime_hex_digit "F"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_prime_A : ~ is_prime_hex_digit "A"%char.
Proof.
  intro H. inversion H.
Qed.

Example test_hex_key_CEEFAD : problem_78_spec "CEEFAD" 1%nat.
Proof.
  unfold problem_78_spec.
  apply cphr_not_prime.
  - exact not_prime_C.
  - apply cphr_not_prime.
    + exact not_prime_E.
    + apply cphr_not_prime.
      * exact not_prime_E.
      * apply cphr_not_prime.
        -- exact not_prime_F.
        -- apply cphr_not_prime.
           ++ exact not_prime_A.
           ++ apply cphr_prime.
              ** exact iphd_D.
              ** exact cphr_nil.
Qed.