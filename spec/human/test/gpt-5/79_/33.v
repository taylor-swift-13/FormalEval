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

Example problem_79_pre_test_0 : problem_79_pre 259.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 259 "db100000011db".
Proof.
  unfold problem_79_spec.
  exists "100000011".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + eapply ntbsar_odd with (fuel' := 258) (n_half := 129) (s' := "10000001").
      * reflexivity.
      * discriminate.
      * discriminate.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * eapply ntbsar_odd with (fuel' := 257) (n_half := 64) (s' := "1000000").
        -- reflexivity.
        -- discriminate.
        -- discriminate.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- eapply ntbsar_even with (fuel' := 256) (n_half := 32) (s' := "100000").
           ++ reflexivity.
           ++ discriminate.
           ++ discriminate.
           ++ simpl. reflexivity.
           ++ simpl. reflexivity.
           ++ eapply ntbsar_even with (fuel' := 255) (n_half := 16) (s' := "10000").
              ** reflexivity.
              ** discriminate.
              ** discriminate.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** eapply ntbsar_even with (fuel' := 254) (n_half := 8) (s' := "1000").
                 --- reflexivity.
                 --- discriminate.
                 --- discriminate.
                 --- simpl. reflexivity.
                 --- simpl. reflexivity.
                 --- eapply ntbsar_even with (fuel' := 253) (n_half := 4) (s' := "100").
                     +++ reflexivity.
                     +++ discriminate.
                     +++ discriminate.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ eapply ntbsar_even with (fuel' := 252) (n_half := 2) (s' := "10").
                         *** reflexivity.
                         *** discriminate.
                         *** discriminate.
                         *** simpl. reflexivity.
                         *** simpl. reflexivity.
                         *** eapply ntbsar_even with (fuel' := 251) (n_half := 1) (s' := "1").
                             ---- reflexivity.
                             ---- discriminate.
                             ---- discriminate.
                             ---- simpl. reflexivity.
                             ---- simpl. reflexivity.
                             ---- apply ntbsar_one.
  - simpl. reflexivity.
Qed.