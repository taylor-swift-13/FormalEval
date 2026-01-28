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

(* Test Case Definitions *)

Definition input_part1 : string := "Pyothon is an interpreted, high-level, general-purpose The quick brown fo x, jumZLKJIHGFECDCBAps over progrPyothon is an interpreted, high-levequi 	
 	
".

Definition input_part2 : string := " A B C   D E F     G H I      ".

Definition input_part3 : string := " pbrownrogranamminA B C   D E Fkfox,     G H I      Fkl, general-purpose pythonmprogramming language.amminthe lazy dog.anguage.".

Definition test_input : string :=
  input_part1 ++ String (ascii_of_nat 12) (input_part2 ++ String (ascii_of_nat 12) input_part3).

Definition output_part1 : string := "Phnooty is an ,deeeinprrtt ,-eeghhillv -aeeeglnopprrsu Teh cikqu bnorw fo ,x ABCCDEFGHIJKLZjmpsu eorv Pghnoooprrty is an ,deeeinprrtt -eeghhiilquv 	
 	
".

Definition output_part2 : string := " A B C   D E F     G H I      ".

Definition output_part3 : string := " Aaabgimmnnnooprrrw B C   D E ,Ffkox     G H I      ,Fkl -aeeeglnopprrsu agghimmmnnoopprrty .aaaeegghilmmnntu alyz ..aadegggnou".

Definition test_output : string :=
  output_part1 ++ String (ascii_of_nat 12) (output_part2 ++ String (ascii_of_nat 12) output_part3).

(* Example Proof *)

Example problem_86_test : problem_86_spec test_input test_output.
Proof.
  unfold problem_86_spec.
  unfold test_input, test_output.
  unfold input_part1, input_part2, input_part3.
  unfold output_part1, output_part2, output_part3.
  vm_compute.
  reflexivity.
Qed.