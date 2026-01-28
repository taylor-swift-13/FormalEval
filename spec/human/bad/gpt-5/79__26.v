Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Inductive nat_to_binary_string_aux_rel : nat -> nat -> string -> Prop :=
  | ntbsar_zero_fuel : forall n, nat_to_binary_string_aux_rel n 0 ""
  | ntbsar_zero_n : forall fuel, nat_to_binary_string_aux_rel 0 (S fuel) "0"
  | ntbsar_one : forall fuel, nat_to_binary_string_aux_rel 1 (S fuel) "1"
  | ntbsar_even : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = true ->
      n_half = n / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' s' ->
      nat_to_binary_string_aux_rel n fuel (s' ++ "0")
  | ntbsar_odd : forall fuel fuel' n n_half s',
      fuel = S fuel' ->
      n <> 0 -> n <> 1 ->
      Nat.even n = false ->
      n_half = (n - 1) / 2 ->
      nat_to_binary_string_aux_rel n_half fuel' s' ->
      nat_to_binary_string_aux_rel n fuel (s' ++ "1").

Inductive nat_to_binary_string_rel : nat -> string -> Prop :=
  | ntbsr_zero : nat_to_binary_string_rel 0 "0"
  | ntbsr_pos : forall n s,
      n <> 0 ->
      nat_to_binary_string_aux_rel n n s ->
      nat_to_binary_string_rel n s.

Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  exists s,
    nat_to_binary_string_rel decimal s /\
    output = "db" ++ s ++ "db".

Example problem_79_pre_test_0 : problem_79_pre 100003.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 100003 "db11000011010100011db".
Proof.
  unfold problem_79_spec.
  exists "11000011010100011".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + assert (H1: nat_to_binary_string_aux_rel 1 99987 "1").
      { apply ntbsar_one. }
      assert (H2: nat_to_binary_string_aux_rel 3 99988 "11").
      { apply (ntbsar_odd 99988 99987 3 1 "1").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H1.
      }
      assert (H3: nat_to_binary_string_aux_rel 6 99989 "110").
      { apply (ntbsar_even 99989 99988 6 3 "11").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H2.
      }
      assert (H4: nat_to_binary_string_aux_rel 12 99990 "1100").
      { apply (ntbsar_even 99990 99989 12 6 "110").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H3.
      }
      assert (H5: nat_to_binary_string_aux_rel 24 99991 "11000").
      { apply (ntbsar_even 99991 99990 24 12 "1100").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H4.
      }
      assert (H6: nat_to_binary_string_aux_rel 48 99992 "110000").
      { apply (ntbsar_even 99992 99991 48 24 "11000").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H5.
      }
      assert (H7: nat_to_binary_string_aux_rel 97 99993 "1100001").
      { apply (ntbsar_odd 99993 99992 97 48 "110000").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H6.
      }
      assert (H8: nat_to_binary_string_aux_rel 195 99994 "11000011").
      { apply (ntbsar_odd 99994 99993 195 97 "1100001").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H7.
      }
      assert (H9: nat_to_binary_string_aux_rel 390 99995 "110000110").
      { apply (ntbsar_even 99995 99994 390 195 "11000011").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H8.
      }
      assert (H10: nat_to_binary_string_aux_rel 781 99996 "1100001101").
      { apply (ntbsar_odd 99996 99995 781 390 "110000110").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H9.
      }
      assert (H11: nat_to_binary_string_aux_rel 1562 99997 "11000011010").
      { apply (ntbsar_even 99997 99996 1562 781 "1100001101").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H10.
      }
      assert (H12: nat_to_binary_string_aux_rel 3125 99998 "110000110101").
      { apply (ntbsar_odd 99998 99997 3125 1562 "11000011010").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H11.
      }
      assert (H13: nat_to_binary_string_aux_rel 6250 99999 "1100001101010").
      { apply (ntbsar_even 99999 99998 6250 3125 "110000110101").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H12.
      }
      assert (H14: nat_to_binary_string_aux_rel 12500 100000 "11000011010100").
      { apply (ntbsar_even 100000 99999 12500 6250 "1100001101010").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H13.
      }
      assert (H15: nat_to_binary_string_aux_rel 25000 100001 "110000110101000").
      { apply (ntbsar_even 100001 100000 25000 12500 "11000011010100").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H14.
      }
      assert (H16: nat_to_binary_string_aux_rel 50001 100002 "1100001101010001").
      { apply (ntbsar_odd 100002 100001 50001 25000 "110000110101000").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H15.
      }
      assert (H17: nat_to_binary_string_aux_rel 100003 100003 "11000011010100011").
      { apply (ntbsar_odd 100003 100002 100003 50001 "1100001101010001").
        - reflexivity.
        - discriminate.
        - discriminate.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - exact H16.
      }
      exact H17.
  - simpl. reflexivity.
Qed.