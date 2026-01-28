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

Example test_case_1 : problem_78_spec "753BDCEACDF12345B67C2022EECEFAD890ABCDEF132345BBAA202001111887215E753BD9CEFF23BC337312345B67CEEFAD890ABCDEF12345BBAA20200CBBD431BDCF0" 61.
Proof.
  unfold problem_78_spec.
  repeat (
    apply cphr_nil || 
    (apply cphr_prime; [ solve [ constructor ] | ]) || 
    (apply cphr_not_prime; [ solve [ intro H; inversion H ] | ])
  ).
Qed.