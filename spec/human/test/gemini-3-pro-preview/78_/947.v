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

Example test_case_1 : problem_78_spec "CEEEFAA12345CEA753BDD67891234567890ABCDEF12345BACDF11118872753BD159CEFF723BCBCD21234567890ABCDEFA12345BBAA20200DBBCC22EECEACACDF11118872159CEFFACDF11118872159CDEFF23BCCBB3137D1DDBB1CBB333A11DDB12345753BD6789123567890ABCDEF123B45BBAA22020A2202ECBBBD44BB333A191DDBFCBBBD4F212345BBAA220ED" 136.
Proof.
  unfold problem_78_spec.
  repeat (
    match goal with
    | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
    | [ |- count_prime_hex_rel (String _ _) _ ] =>
      first [
        apply cphr_prime; [ solve [ constructor ] | ]
      | apply cphr_not_prime; [ solve [ let H := fresh "H" in intro H; inversion H ] | ]
      ]
    end).
Qed.