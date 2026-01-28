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

Example test_case_1 : problem_78_spec "123ABB333A11DDBCBCDEF202020CBAABBB73533A11DD7ABCDEF22022ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC5ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC5555555E02020CBAABBBBB333A11DDBC55ACDF11118872159CEFF23BCCBBD4DBC555547567CEEFAD890ABCDABCDEF20202CB5EF12345BBAA20200" 145.
Proof.
  unfold problem_78_spec.
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String _ _) (S _) ] =>
      (apply cphr_prime; [ constructor | ]) ||
      (apply cphr_not_prime; [ let H := fresh in intro H; inversion H | ])
  | [ |- count_prime_hex_rel (String _ _) _ ] =>
      apply cphr_not_prime; [ let H := fresh in intro H; inversion H | ]
  end.
Qed.