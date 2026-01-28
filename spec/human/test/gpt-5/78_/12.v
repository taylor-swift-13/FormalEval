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

Example problem_78_test_67ABCD23 : problem_78_spec "67ABCD23" 5%nat.
Proof.
  unfold problem_78_spec.
  refine (
    cphr_not_prime "6"%char "7ABCD23" 5
      (fun H : is_prime_hex_digit "6"%char => match H with end)
      (
        cphr_prime "7"%char "ABCD23" 4 iphd_7
          (
            cphr_not_prime "A"%char "BCD23" 4
              (fun H : is_prime_hex_digit "A"%char => match H with end)
              (
                cphr_prime "B"%char "CD23" 3 iphd_B
                  (
                    cphr_not_prime "C"%char "D23" 3
                      (fun H : is_prime_hex_digit "C"%char => match H with end)
                      (
                        cphr_prime "D"%char "23" 2 iphd_D
                          (
                            cphr_prime "2"%char "3" 1 iphd_2
                              (
                                cphr_prime "3"%char "" 0 iphd_3
                                  cphr_nil
                              )
                          )
                      )
                  )
              )
          )
      )
  ).
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_67ABCD23_Z_output : Z.of_nat 5 = 5%Z.
Proof.
  reflexivity.
Qed.