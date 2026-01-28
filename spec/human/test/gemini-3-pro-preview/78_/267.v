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

Example test_case_1 : problem_78_spec "11ABCD2020DDBCC22EEF" 9.
Proof.
  unfold problem_78_spec.
  (* 1 *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* 1 *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* A *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* B *)
  apply cphr_prime; [ apply iphd_B | ].
  (* C *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* D *)
  apply cphr_prime; [ apply iphd_D | ].
  (* 2 *)
  apply cphr_prime; [ apply iphd_2 | ].
  (* 0 *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* 2 *)
  apply cphr_prime; [ apply iphd_2 | ].
  (* 0 *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* D *)
  apply cphr_prime; [ apply iphd_D | ].
  (* D *)
  apply cphr_prime; [ apply iphd_D | ].
  (* B *)
  apply cphr_prime; [ apply iphd_B | ].
  (* C *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* C *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* 2 *)
  apply cphr_prime; [ apply iphd_2 | ].
  (* 2 *)
  apply cphr_prime; [ apply iphd_2 | ].
  (* E *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* E *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* F *)
  apply cphr_not_prime; [ intro H; inversion H | ].
  (* End *)
  apply cphr_nil.
Qed.