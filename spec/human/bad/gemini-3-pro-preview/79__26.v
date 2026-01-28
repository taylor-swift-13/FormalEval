Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

(* Definition of the relation as provided in the specification *)
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

(* Proof for the test case input = 100003, output = "db11000011010100011db" *)
Example test_case_0 : problem_79_spec 100003 "db11000011010100011db".
Proof.
  unfold problem_79_spec.
  exists "11000011010100011".
  split.
  - apply ntbsr_pos.
    + discriminate.
    + (* We define local tactics to automate the steps and use vm_compute for efficiency *)
      Ltac t_odd :=
        eapply ntbsar_odd;
        [ reflexivity
        | discriminate
        | try discriminate
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | ].
      Ltac t_even :=
        eapply ntbsar_even;
        [ reflexivity
        | discriminate
        | try discriminate
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | ].

      (* Sequence of steps for 100003 down to 1 *)
      t_odd.  (* 100003 *)
      t_odd.  (* 50001 *)
      t_even. (* 25000 *)
      t_even. (* 12500 *)
      t_even. (* 6250 *)
      t_odd.  (* 3125 *)
      t_even. (* 1562 *)
      t_odd.  (* 781 *)
      t_even. (* 390 *)
      t_odd.  (* 195 *)
      t_odd.  (* 97 *)
      t_even. (* 48 *)
      t_even. (* 24 *)
      t_even. (* 12 *)
      t_even. (* 6 *)
      t_odd.  (* 3 *)
      apply ntbsar_one.
  - simpl. reflexivity.
Qed.