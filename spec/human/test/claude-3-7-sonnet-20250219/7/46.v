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
  problem_7_spec
    ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"; "Washington"]
    ["San Francisco"]
    "an".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "Washington" "an" *)
  (* prefix "an" "Washington" = false *)
  (* contains_substring "ashington" "an" *)
  (* prefix "an" "ashington" = false *)
  (* contains_substring "shington" "an" ... false *)
  (* contains_substring "hington" "an" ... false *)
  (* contains_substring "ington" "an" ... false *)
  (* contains_substring "ngton" "an" ... false *)
  (* contains_substring "gton" "an" ... false *)
  (* contains_substring "ton" "an" ... false *)
  (* contains_substring "on" "an" ... false *)
  (* contains_substring "n" "an" ... false *)
  (* contains_substring "" "an" false *)
  (* so false *)
  (* so skip "Washington" *)

  (* contains_substring "DC" "an" *)
  (* prefix "an" "DC" = false *)
  (* contains_substring "C" "an" = false *)
  (* contains_substring "" "an" = false *)
  (* false *)
  (* skip *)

  (* "New York City" *)
  (* prefix "an" "New York City" false *)
  (* shift each char and no prefix "an" found *)
  (* false *)

  (* "Boston" *)
  (* prefix "an" "Boston" false *)
  (* false *)

  (* "Los Angeles" *)
  (* prefix "an" "Los Angeles" false *)
  (* contains_substring "os Angeles" "an" *)
  (* prefix "an" "os Angeles" false *)
  (* contains_substring "s Angeles" "an" false *)
  (* contains_substring " Angeles" "an" false *)
  (* contains_substring "Angeles" "an" *)
  (* prefix "an" "Angeles" false (case sensitive) *)
  (* Note: prefix uses case sensitive comparison, 'A' ≠ 'a' so false *)
  (* Thus no match *)

  (* "San Francisco" *)
  (* prefix "an" "San Francisco" false *)
  (* contains_substring "an Francisco" "an" *)
  (* prefix "an" "an Francisco" true *)
  (* so true *)

  (* So include "San Francisco" *)

  (* "Miami" *)
  (* no match *)

  (* "Washington" again no match *)

  reflexivity.
Qed.