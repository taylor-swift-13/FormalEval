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

Example test_case_1 : problem_78_spec "2022E753BDC123ABB333A11DDBCBCDEF202020CBAABBB73533A11DDBC555547567CEEFAD890ABCDEF12345BBAA20201234567CEEFA7ABCDEF20ABCDEF202020CBAABBBBB333A11DDBC555520222E2020CBAABBBBB333A11DDBCACDF111188727159CEFFCEEFAD12113BCCBBD4EE11ACDF1123ABB333A11DDBCBCDEF2020200CBAAB2BB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BB3AA20200AD21753BDCEE753BDCF03BCCBBBD4ABCD2020D45B67C2022EEEFAD890ABCDEF12345BBAA20200CC22EEFFEEDDCCBBAAEFEADC55553BACDF11118872159CEEFFCEEFAD213BCCBBD4DD89073533ABCDEF12345BBBAA20200EE7711ABCD2020DDB2BCC22EEFFEEDDCCBBAA" 255.
Proof.
  unfold problem_78_spec.
  repeat match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String _ _) _ ] =>
      first [ 
        apply cphr_prime; [ constructor | ]
      | apply cphr_not_prime; [ let H := fresh in intro H; inversion H | ]
      ]
  end.
Qed.