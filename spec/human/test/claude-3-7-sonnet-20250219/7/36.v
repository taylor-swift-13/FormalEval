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
  problem_7_spec ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"] ["San Francisco"] "an".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "Washington" "an" *)
  (* prefix "an" "Washington" = false *)
  (* contains_substring "ashington" "an" *)
  (* prefix "an" "ashington" = false *)
  (* contains_substring "shington" "an" false *)
  (* contains_substring "hington" "an" false *)
  (* contains_substring "ington" "an" false *)
  (* contains_substring "ngton" "an" false *)
  (* contains_substring "gton" "an" false *)
  (* contains_substring "ton" "an" false *)
  (* contains_substring "on" "an" false *)
  (* contains_substring "n" "an" false *)
  (* contains_substring "" "an" false *)
  (* So overall false, so exclude "Washington" *)
  (* contains_substring "DC" "an" *)
  (* prefix "an" "DC" false *)
  (* contains_substring "C" "an" false *)
  (* contains_substring "" "an" false *)
  (* exclude "DC" *)
  (* contains_substring "New York City" "an" *)
  (* prefix "an" "New York City" false *)
  (* .... none match "an" substring *)
  (* exclude "New York City" *)
  (* contains_substring "Boston" "an" *)
  (* prefix "an" "Boston" false *)
  (* contains_substring "oston" "an" false *)
  (* contains_substring "ston" "an" false *)
  (* contains_substring "ton" "an" false *)
  (* contains_substring "on" "an" false *)
  (* contains_substring "n" "an" false *)
  (* contains_substring "" "an" false *)
  (* exclude "Boston" *)
  (* contains_substring "Los Angeles" "an" *)
  (* prefix "an" "Los Angeles" false *)
  (* contains_substring "os Angeles" "an" false *)
  (* contains_substring "s Angeles" "an" false *)
  (* contains_substring " Angeles" "an" false *)
  (* contains_substring "Angeles" "an" *)
  (* prefix "an" "Angeles" false (case sensitive) *)
  (* prefix is case sensitive, 'A' vs 'a' not equal, so false *)
  (* contains_substring "ngeles" "an" *)
  (* prefix "an" "ngeles" false *)
  (* etc all false *)
  (* exclude "Los Angeles" *)
  (* contains_substring "San Francisco" "an" *)
  (* prefix "an" "San Francisco" false *)
  (* contains_substring "an Francisco" "an" *)
  (* prefix "an" "an Francisco" = true *)
  (* so included "San Francisco" *)
  (* then recurse on "Miami" *)
  (* contains_substring "Miami" "an" *)
  (* prefix "an" "Miami" false *)
  (* contains_substring "iami" "an" false *)
  (* contains_substring "ami" "an" false *)
  (* contains_substring "mi" "an" false *)
  (* contains_substring "i" "an" false *)
  (* contains_substring "" "an" false *)
  (* exclude "Miami" *)
  reflexivity.
Qed.