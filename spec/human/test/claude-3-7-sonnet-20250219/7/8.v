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
  problem_7_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"] ["abc"; "bcd"; "dbc"] "bc".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "abc" "bc" *)
  (* prefix "bc" "abc" = false *)
  (* contains_substring "bc" "bc" *)
  (* prefix "bc" "bc" = true *)
  (* So contains_substring "abc" "bc" = true *)
  (* Next, contains_substring "bcd" "bc" *)
  (* prefix "bc" "bcd" = true *)
  (* contains_substring "cbd" "bc" *)
  (* prefix "bc" "cbd" = false *)
  (* contains_substring "bd" "bc" = false *)
  (* contains_substring "d" "bc" = false *)
  (* contains_substring "" "bc" = false *)
  (* So false *)
  (* contains_substring "dbc" "bc" *)
  (* prefix "bc" "dbc" = false *)
  (* contains_substring "bc" "bc" = true *)
  (* So true *)
  (* contains_substring "cda" "bc" *)
  (* prefix "bc" "cda" = false *)
  (* contains_substring "da" "bc" = false *)
  (* contains_substring "a" "bc" = false *)
  (* contains_substring "" "bc" = false *)
  (* So false *)
  reflexivity.
Qed.