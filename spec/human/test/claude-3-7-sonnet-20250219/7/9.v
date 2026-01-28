Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if String.eqb sub EmptyString then true else false
  | String _ rest =>
      if String.prefix sub s then true
      else contains_substring rest sub
  end.

Fixpoint filter_by_substring_impl (input : list string) (sub : string) : list string :=
  match input with
  | [] => []
  | h :: t =>
    if contains_substring h sub then
      h :: filter_by_substring_impl t sub
    else
      filter_by_substring_impl t sub
  end.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  output = filter_by_substring_impl input sub.

Example test_case_1 :
  problem_7_spec ["a"; "ab"; "abc"; "abcd"; "abcde"; "bcde"; "cde"] ["abcd"; "abcde"; "bcde"; "cde"] "cd".
Proof.
  unfold problem_7_spec. simpl.
  (* contains_substring "a" "cd" = false *)
  (* contains_substring "ab" "cd" = false *)
  (* contains_substring "abc" "cd" = false *)
  (* contains_substring "abcd" "cd" = true *)
  (* contains_substring "abcde" "cd" = true *)
  (* contains_substring "bcde" "cd" = true *)
  (* contains_substring "cde" "cd" = true *)
  reflexivity.
Qed.