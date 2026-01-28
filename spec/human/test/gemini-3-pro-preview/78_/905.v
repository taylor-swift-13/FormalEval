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

Example test_case_1 : problem_78_spec "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDACDF11118872753BD159CEFF723BCCBB333A191BD7BB11ABCD22020DDBB2CC22EECEA5F3BDCEEFAD20201234512134567582290ABCDEFAACDF11118872159CEFF23BCCBBD4A006789CDEF04EFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ACDF1111887C2159CEFFACDF11118872159CEFF12345753BD6789123567890ABCDEF123B45BBAA22020A2202E23BCCBB333A11DDBCBBBD44ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA3137D1DDBB31CEFFEEDDCCBBAADEF0" 228.
Proof.
  unfold problem_78_spec.
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String ?c ?s) _ ] =>
      first [ 
        apply cphr_prime; [ constructor | ]
      | apply cphr_not_prime; [ intro H; inversion H | ]
      ]
  end.
Qed.