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
  problem_7_spec ["123"; "456"; "789"; "101112"; "456"] ["123"; "101112"] "12".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "123" "12" *)
  (* prefix "12" "123" = true *)
  (* so include "123" *)
  simpl.
  (* filter tail ["456"; "789"; "101112"; "456"] "12" *)

  (* "456": contains_substring "456" "12" *)
  (* prefix "12" "456" = false *)
  (* contains_substring "56" "12" false *)
  (* contains_substring "6" "12" false *)
  (* contains_substring EmptyString "12" false *)
  simpl.
  (* skip "456" *)

  (* "789": contains_substring "789" "12" *)
  (* similarly false *)
  simpl.

  (* "101112": contains_substring "101112" "12" *)
  (* prefix "12" "101112" false *)
  (* contains_substring "01112" "12" *)
  (* prefix "12" "01112" false *)
  (* contains_substring "1112" "12" *)
  (* prefix "12" "1112" false *)
  (* contains_substring "112" "12" *)
  (* prefix "12" "112" false *)
  (* contains_substring "12" "12" prefix "12" "12" true *)
  (* so true *)
  simpl.

  (* include "101112" *)

  (* last "456": no *)
  simpl.

  reflexivity.
Qed.