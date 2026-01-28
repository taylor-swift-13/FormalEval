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

Definition test_input := "753BDCEACDF12345B67C2022EEEFAD890ABCDEF12345BBAA202001111887215E753BD9CEFF23BC337312345B67CEEFABD890ABCDEF12345BBACDF12345B67C2022EEEFAD123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC555547567CEEFAD890ABCDEF12345BBAA20200890AB123ABB333A11DDBCBCDEF20202C0CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF231234567890ABCDEF12345BBAA20200BCCBBD4AA20200CBBD431BDCF0".

Example test_case_1 : problem_78_spec test_input 186.
Proof.
  unfold problem_78_spec, test_input.
  Ltac step :=
    match goal with
    | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
    | [ |- count_prime_hex_rel (String "2"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_2 | ]
    | [ |- count_prime_hex_rel (String "3"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_3 | ]
    | [ |- count_prime_hex_rel (String "5"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_5 | ]
    | [ |- count_prime_hex_rel (String "7"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_7 | ]
    | [ |- count_prime_hex_rel (String "B"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_B | ]
    | [ |- count_prime_hex_rel (String "D"%char _) _ ] => 
        apply cphr_prime; [ apply iphd_D | ]
    | [ |- count_prime_hex_rel (String ?c _) _ ] => 
        apply cphr_not_prime; [ 
          let H := fresh in intro H; inversion H 
        | ]
    end.
  repeat step.
Qed.