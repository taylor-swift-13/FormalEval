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

Ltac solve_prime_hex :=
  first [ apply iphd_2 | apply iphd_3 | apply iphd_5 | apply iphd_7 | apply iphd_B | apply iphd_D ].

Ltac solve_not_prime_hex :=
  let H := fresh in intro H; inversion H.

Ltac solve_count_step :=
  match goal with
  | |- count_prime_hex_rel "" 0 => apply cphr_nil
  | |- count_prime_hex_rel (String ?h ?t) ?n =>
    (apply cphr_prime; [ solve [ solve_prime_hex ] | ]) ||
    (apply cphr_not_prime; [ solve [ solve_not_prime_hex ] | ])
  end.

Example test_case_1 : problem_78_spec "1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDFBB11ABCD22020DDBB2CC22EECEA11118872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200" 105.
Proof.
  unfold problem_78_spec.
  repeat solve_count_step.
Qed.