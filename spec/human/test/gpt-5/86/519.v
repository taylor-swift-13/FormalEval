Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char c t)
  end.

Fixpoint sort_chars (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char h (sort_chars t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.

Definition problem_86_pre (s : string) : Prop := True.

Definition problem_86_spec (s s_out : string) : Prop :=
  s_out = anti_shuffle_impl s.

Definition ch (n : nat) : string := String (Ascii.ascii_of_nat n) EmptyString.

Definition problem_86_input : string :=
  "passs" ++ ch 9 ++ ch 12 ++ "ZYXWVUTSRQPONMLKA" ++ ch 13 ++ ch 11 ++ "A By C   D E F     G H I      ythono rd".

Definition problem_86_output : string :=
  anti_shuffle_impl problem_86_input.

Example problem_86_test: problem_86_spec problem_86_input problem_86_output.
Proof.
  unfold problem_86_spec, problem_86_output, anti_shuffle_impl.
  reflexivity.
Qed.