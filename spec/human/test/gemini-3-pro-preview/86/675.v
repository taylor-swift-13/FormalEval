Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

(* Provided Definitions *)

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

(* Example Proof for Test Case *)

Definition TAB := String (ascii_of_nat 9) EmptyString.
Definition LF := String (ascii_of_nat 10) EmptyString.
Definition VT := String (ascii_of_nat 11) EmptyString.
Definition FF := String (ascii_of_nat 12) EmptyString.

Definition input_86 := 
  "qui " ++ TAB ++ LF ++ " " ++ TAB ++ LF ++ FF ++ VT ++ "A B C   D E F     G H I      " ++ FF ++ VT ++ "A B C   D E F     G H I      Fk".

Definition output_86 := 
  "iqu " ++ TAB ++ LF ++ " " ++ TAB ++ LF ++ VT ++ FF ++ "A B C   D E F     G H I      " ++ VT ++ FF ++ "A B C   D E F     G H I      Fk".

Example problem_86_test : problem_86_spec input_86 output_86.
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  vm_compute.
  reflexivity.
Qed.