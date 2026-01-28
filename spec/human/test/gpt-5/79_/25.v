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

Example problem_79_pre_test_0 : problem_79_pre 1024.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 1024 "db10000000000db".
Proof.
  unfold problem_79_spec.
  exists "10000000000".
  split.
  - apply ntbsr_pos with (s := "10000000000").
    + intro H; discriminate.
    + assert (H1 : nat_to_binary_string_aux_rel 1 1014 "1").
      { apply (ntbsar_one 1013). }
      assert (H2 : nat_to_binary_string_aux_rel 2 1015 "10").
      { apply (ntbsar_even 1015 1014 2 1 "1").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H1.
      }
      assert (H3 : nat_to_binary_string_aux_rel 4 1016 "100").
      { apply (ntbsar_even 1016 1015 4 2 "10").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H2.
      }
      assert (H4 : nat_to_binary_string_aux_rel 8 1017 "1000").
      { apply (ntbsar_even 1017 1016 8 4 "100").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H3.
      }
      assert (H5 : nat_to_binary_string_aux_rel 16 1018 "10000").
      { apply (ntbsar_even 1018 1017 16 8 "1000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H4.
      }
      assert (H6 : nat_to_binary_string_aux_rel 32 1019 "100000").
      { apply (ntbsar_even 1019 1018 32 16 "10000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H5.
      }
      assert (H7 : nat_to_binary_string_aux_rel 64 1020 "1000000").
      { apply (ntbsar_even 1020 1019 64 32 "100000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H6.
      }
      assert (H8 : nat_to_binary_string_aux_rel 128 1021 "10000000").
      { apply (ntbsar_even 1021 1020 128 64 "1000000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H7.
      }
      assert (H9 : nat_to_binary_string_aux_rel 256 1022 "100000000").
      { apply (ntbsar_even 1022 1021 256 128 "10000000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H8.
      }
      assert (H10 : nat_to_binary_string_aux_rel 512 1023 "1000000000").
      { apply (ntbsar_even 1023 1022 512 256 "100000000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H9.
      }
      assert (H11 : nat_to_binary_string_aux_rel 1024 1024 "10000000000").
      { apply (ntbsar_even 1024 1023 1024 512 "1000000000").
        - reflexivity.
        - intro H; discriminate.
        - intro H; discriminate.
        - simpl; reflexivity.
        - simpl; reflexivity.
        - exact H10.
      }
      exact H11.
  - simpl. reflexivity.
Qed.