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
    ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"; "dcbd"]
    []
    "bbc".
Proof.
  unfold problem_7_spec.
  simpl.
  (* For each element in input list:

     contains_substring "abc" "bbc":
       prefix "bbc" "abc" = false,
       then look for "bbc" in "bc" -> false,
       then "c" -> false,
       then "" -> false,
       result false.

     Similarly for "bcd":
       prefix "bbc" "bcd" false,
       then "cd" false,
       then "d" false,
       then "" false.

     For "cbd":
       prefix "bbc" "cbd" false,
       "bd" false,
       "d" false,
       "" false.

     For "dbc":
       prefix "bbc" "dbc" false,
       "bc" false,
       "c" false,
       "" false.

     For "cda":
       prefix "bbc" "cda" false, and similarly no match.

     For "cfloccinaucinihilipilificatilinionda":
       prefix "bbc" ... false, same logic no match.

     For "dcbd":
       prefix "bbc" "dcbd" false,
       "cbd" false,
       "bd" false,
       "d" false,
       "" false.

     Hence none contain substring "bbc", filter_by_substring_impl returns [].

  *)
  reflexivity.
Qed.