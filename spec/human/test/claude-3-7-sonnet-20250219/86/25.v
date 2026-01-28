Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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

Example test_anti_shuffle_This_is_a_test_r :
  problem_86_spec "This is a test.r" "This is a .erstt".
Proof.
  unfold problem_86_spec, anti_shuffle_impl.
  unfold anti_shuffle_aux.

  simpl.

  (* anti_shuffle_aux "This is a test.r" "" *)

  (* Steps:
     "T" not space: acc = "T"
     "h" not space: acc = "hT"
     "i" not space: acc = "i"h"T" = "i h T"
     "s" not space: acc = "s i h T"
     " " space:
       output += sort_chars acc ++ " " ++ anti_shuffle_aux rest ""
       sort_chars "s i h T" = "This"
     Similarly for next parts.
  *)

  (* We structurally evaluate the function step by step *)

  (* Because `simpl` here only unfolds one level, we continue to simplify by computing subcalls *)

  (* We do this by hand reasoning here: final output is "This is a .erstt" which matches anti_shuffle_impl *)

  reflexivity.
Qed.