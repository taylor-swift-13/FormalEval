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

Example problem_78_test_679D99999ABC : problem_78_spec "679D99999ABC" 3%nat.
Proof.
  unfold problem_78_spec.
  apply (cphr_not_prime "6"%char "79D99999ABC" 3).
  intro H; inversion H.
  apply (cphr_prime "7"%char "9D99999ABC" 2).
  exact iphd_7.
  apply (cphr_not_prime "9"%char "D99999ABC" 2).
  intro H; inversion H.
  apply (cphr_prime "D"%char "99999ABC" 1).
  exact iphd_D.
  apply (cphr_not_prime "9"%char "9999ABC" 1).
  intro H; inversion H.
  apply (cphr_not_prime "9"%char "999ABC" 1).
  intro H; inversion H.
  apply (cphr_not_prime "9"%char "99ABC" 1).
  intro H; inversion H.
  apply (cphr_not_prime "9"%char "9ABC" 1).
  intro H; inversion H.
  apply (cphr_not_prime "9"%char "ABC" 1).
  intro H; inversion H.
  apply (cphr_not_prime "A"%char "BC" 1).
  intro H; inversion H.
  apply (cphr_prime "B"%char "C" 0).
  exact iphd_B.
  apply (cphr_not_prime "C"%char "" 0).
  intro H; inversion H.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_679D99999ABC_Z_output : Z.of_nat 3 = 3%Z.
Proof.
  reflexivity.
Qed.