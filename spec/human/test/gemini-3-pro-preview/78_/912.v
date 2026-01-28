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

Example test_case_1 : problem_78_spec "1ACDF11118872159CEDFF23BCCBBACDF11118872159CEFFACDF1BB37137D1DDBC1118872159CEFF23BCCBB333A11DDBCBBBD44D4234567890ABCDEFA12345BBABA2020CEEFAD11ABCD20C290753BDDDBBCFFEEDDCCBBAA12345BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBCBBBD4437D1DDBC67890ABCDEBF12345BBAA202000" 122.
Proof.
  unfold problem_78_spec.
  repeat (
    match goal with
    | [ |- count_prime_hex_rel "" _ ] => apply cphr_nil
    | [ |- count_prime_hex_rel (String _ _) _ ] => 
      (apply cphr_prime; [constructor | ]) || 
      (apply cphr_not_prime; [intro H; inversion H | ])
    end).
Qed.