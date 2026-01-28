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

Example test_case_1 : problem_78_spec "ABDBC55" 5.
Proof.
  unfold problem_78_spec.
  (* 'A' is not prime *)
  apply cphr_not_prime.
  - intro H; inversion H.
  - (* 'B' is prime *)
    apply cphr_prime.
    + apply iphd_B.
    + (* 'D' is prime *)
      apply cphr_prime.
      * apply iphd_D.
      * (* 'B' is prime *)
        apply cphr_prime.
        -- apply iphd_B.
        -- (* 'C' is not prime *)
           apply cphr_not_prime.
           ++ intro H; inversion H.
           ++ (* '5' is prime *)
              apply cphr_prime.
              ** apply iphd_5.
              ** (* '5' is prime *)
                 apply cphr_prime.
                 --- apply iphd_5.
                 --- (* End of string *)
                     apply cphr_nil.
Qed.