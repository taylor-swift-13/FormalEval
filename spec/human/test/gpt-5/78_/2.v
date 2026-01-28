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

Example problem_78_test_1077E : problem_78_spec "1077E" 2%nat.
Proof.
  unfold problem_78_spec.
  refine (cphr_not_prime "1"%char "077E" 2 _ _).
  - unfold not; intros H; inversion H.
  - refine (cphr_not_prime "0"%char "77E" 2 _ _).
    + unfold not; intros H; inversion H.
    + refine (cphr_prime "7"%char "7E" 1 _ _).
      * exact iphd_7.
      * refine (cphr_prime "7"%char "E" 0 _ _).
        -- exact iphd_7.
        -- refine (cphr_not_prime "E"%char "" 0 _ _).
           ++ unfold not; intros H; inversion H.
           ++ apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_1077E_Z_output : Z.of_nat 2 = 2%Z.
Proof.
  reflexivity.
Qed.