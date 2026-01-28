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

Ltac solve_prime :=
  first [ apply iphd_2 | apply iphd_3 | apply iphd_5 | apply iphd_7 | apply iphd_B | apply iphd_D ].

Ltac solve_not_prime :=
  let H := fresh "H" in
  intro H; inversion H.

Ltac solve_step :=
  match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String _ _) _ ] =>
      (apply cphr_prime; [ solve_prime | ]) ||
      (apply cphr_not_prime; [ solve_not_prime | ])
  end.

Example test_case_1 : problem_78_spec "753BDCEE7757353312345ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD977ABCDEF202020CBAABBBBB75322022EBDCEEFFA7F89ABCDEF0333A11DDBC5555CEFF23BCCBBD4C2022EEEFAD890ABCDEF12345BBAA2020033F0" 133.
Proof.
  unfold problem_78_spec.
  repeat solve_step.
Qed.