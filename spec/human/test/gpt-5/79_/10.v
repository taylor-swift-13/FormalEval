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

Example problem_79_pre_test_0 : problem_79_pre 1023.
Proof.
  unfold problem_79_pre.
  exact I.
Qed.

Example problem_79_spec_test_0 : problem_79_spec 1023 "db1111111111db".
Proof.
  unfold problem_79_spec.
  exists "1111111111".
  split.
  - apply ntbsr_pos.
    + intro H. inversion H.
    + eapply ntbsar_odd with (fuel' := 1022) (n_half := 511) (s' := "111111111").
      * reflexivity.
      * intro H. inversion H.
      * intro H. inversion H.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * eapply ntbsar_odd with (fuel' := 1021) (n_half := 255) (s' := "11111111").
        -- reflexivity.
        -- intro H. inversion H.
        -- intro H. inversion H.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- eapply ntbsar_odd with (fuel' := 1020) (n_half := 127) (s' := "1111111").
           ++ reflexivity.
           ++ intro H. inversion H.
           ++ intro H. inversion H.
           ++ simpl. reflexivity.
           ++ simpl. reflexivity.
           ++ eapply ntbsar_odd with (fuel' := 1019) (n_half := 63) (s' := "111111").
              ** reflexivity.
              ** intro H. inversion H.
              ** intro H. inversion H.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** eapply ntbsar_odd with (fuel' := 1018) (n_half := 31) (s' := "11111").
                 --- reflexivity.
                 --- intro H. inversion H.
                 --- intro H. inversion H.
                 --- simpl. reflexivity.
                 --- simpl. reflexivity.
                 --- eapply ntbsar_odd with (fuel' := 1017) (n_half := 15) (s' := "1111").
                     +++ reflexivity.
                     +++ intro H. inversion H.
                     +++ intro H. inversion H.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ eapply ntbsar_odd with (fuel' := 1016) (n_half := 7) (s' := "111").
                         *** reflexivity.
                         *** intro H. inversion H.
                         *** intro H. inversion H.
                         *** simpl. reflexivity.
                         *** simpl. reflexivity.
                         *** eapply ntbsar_odd with (fuel' := 1015) (n_half := 3) (s' := "11").
                             ---- reflexivity.
                             ---- intro H. inversion H.
                             ---- intro H. inversion H.
                             ---- simpl. reflexivity.
                             ---- simpl. reflexivity.
                             ---- eapply ntbsar_odd with (fuel' := 1014) (n_half := 1) (s' := "1").
                                  **** reflexivity.
                                  **** intro H. inversion H.
                                  **** intro H. inversion H.
                                  **** simpl. reflexivity.
                                  **** simpl. reflexivity.
                                  **** apply (ntbsar_one 1013).
  - simpl. reflexivity.
Qed.