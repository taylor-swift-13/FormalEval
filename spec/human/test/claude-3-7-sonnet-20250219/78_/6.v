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

Example example_112233445566778899AABBCCDDEEFF00 : problem_78_spec "112233445566778899AABBCCDDEEFF00" 12%nat.
Proof.
  unfold problem_78_spec.
  (* proceed by repeated application as per the string *)
  apply cphr_not_prime. intros H; inversion H. (* '1' *)
  apply cphr_not_prime. intros H; inversion H. (* '1' *)
  apply cphr_prime. constructor. (* '2' *)
  apply cphr_prime. constructor. (* '2' *)
  apply cphr_prime. constructor. (* '3' *)
  apply cphr_prime. constructor. (* '3' *)
  apply cphr_not_prime. intros H; inversion H. (* '4' *)
  apply cphr_not_prime. intros H; inversion H. (* '4' *)
  apply cphr_prime. constructor. (* '5' *)
  apply cphr_prime. constructor. (* '5' *)
  apply cphr_not_prime. intros H; inversion H. (* '6' *)
  apply cphr_not_prime. intros H; inversion H. (* '6' *)
  apply cphr_prime. constructor. (* '7' *)
  apply cphr_prime. constructor. (* '7' *)
  apply cphr_not_prime. intros H; inversion H. (* '8' *)
  apply cphr_not_prime. intros H; inversion H. (* '8' *)
  apply cphr_not_prime. intros H; inversion H. (* '9' *)
  apply cphr_not_prime. intros H; inversion H. (* '9' *)
  apply cphr_not_prime. intros H; inversion H. (* 'A' *)
  apply cphr_not_prime. intros H; inversion H. (* 'A' *)
  apply cphr_prime. constructor. (* 'B' *)
  apply cphr_prime. constructor. (* 'B' *)
  apply cphr_not_prime. intros H; inversion H. (* 'C' *)
  apply cphr_not_prime. intros H; inversion H. (* 'C' *)
  apply cphr_prime. constructor. (* 'D' *)
  apply cphr_prime. constructor. (* 'D' *)
  apply cphr_not_prime. intros H; inversion H. (* 'E' *)
  apply cphr_not_prime. intros H; inversion H. (* 'E' *)
  apply cphr_not_prime. intros H; inversion H. (* 'F' *)
  apply cphr_not_prime. intros H; inversion H. (* 'F' *)
  apply cphr_not_prime. intros H; inversion H. (* '0' *)
  apply cphr_not_prime. intros H; inversion H. (* '0' *)
  apply cphr_nil.
Qed.