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

Ltac solve_hex_prime :=
  match goal with
  | [ |- is_prime_hex_digit _ ] =>
      first [ apply iphd_2 | apply iphd_3 | apply iphd_5 | apply iphd_7 | apply iphd_B | apply iphd_D ]
  | [ |- ~ is_prime_hex_digit _ ] =>
      let H := fresh "H" in intro H; inversion H
  end.

Ltac solve_count :=
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String _ _) _ ] =>
      first [
        apply cphr_prime; [ solve_hex_prime | ]
      | apply cphr_not_prime; [ solve_hex_prime | ]
      ]
  end.

Example test_case_1 : problem_78_spec "2022E753BDCEE7711ABACDF11118872159CEFFCEEFAD1213BCCBBD4CD2020DDB2BCC22EEFFEEACDF11118872159CEFFCEEFAD213BCCBBBD4DDCCBBAA" 48.
Proof.
  unfold problem_78_spec.
  solve_count.
Qed.