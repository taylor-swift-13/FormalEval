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

Example test_case_1 : problem_78_spec "123BDB3137D1DDBB1CE" 13.
Proof.
  unfold problem_78_spec.
  (* '1' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* '2' is prime *)
  apply cphr_prime. apply iphd_2.
  (* '3' is prime *)
  apply cphr_prime. apply iphd_3.
  (* 'B' is prime *)
  apply cphr_prime. apply iphd_B.
  (* 'D' is prime *)
  apply cphr_prime. apply iphd_D.
  (* 'B' is prime *)
  apply cphr_prime. apply iphd_B.
  (* '3' is prime *)
  apply cphr_prime. apply iphd_3.
  (* '1' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* '3' is prime *)
  apply cphr_prime. apply iphd_3.
  (* '7' is prime *)
  apply cphr_prime. apply iphd_7.
  (* 'D' is prime *)
  apply cphr_prime. apply iphd_D.
  (* '1' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* 'D' is prime *)
  apply cphr_prime. apply iphd_D.
  (* 'D' is prime *)
  apply cphr_prime. apply iphd_D.
  (* 'B' is prime *)
  apply cphr_prime. apply iphd_B.
  (* 'B' is prime *)
  apply cphr_prime. apply iphd_B.
  (* '1' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* 'C' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* 'E' is not prime *)
  apply cphr_not_prime. intro H; inversion H.
  (* End of string *)
  apply cphr_nil.
Qed.