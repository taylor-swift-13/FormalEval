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
  problem_7_spec ["cat"; "dog"; "elephant"; "rhinoceros"; "seagull"] ["elephant"; "rhinoceros"; "seagull"] "e".
Proof.
  unfold problem_7_spec. simpl.
  (* contains_substring "cat" "e" *)
  (* prefix "e" "cat" = false *)
  (* contains_substring "at" "e" = false *)
  (* contains_substring "t" "e" = false *)
  (* contains_substring EmptyString "e" = false *)
  (* so "cat" excluded *)

  (* contains_substring "dog" "e" *)
  (* prefix "e" "dog" = false *)
  (* ... similarly false *)
  (* so "dog" excluded *)

  (* contains_substring "elephant" "e" *)
  (* prefix "e" "elephant" = true, included *)

  (* contains_substring "rhinoceros" "e" *)
  (* prefix "e" "rhinoceros" = false *)
  (* contains_substring "hinoceros" "e" *)
  (* prefix "e" "hinoceros" = false *)
  (* contains_substring "inoceros" "e" *)
  (* prefix "e" "inoceros" = false *)
  (* contains_substring "noceros" "e" *)
  (* prefix "e" "noceros" = false *)
  (* contains_substring "oceros" "e" *)
  (* prefix "e" "oceros" = false *)
  (* contains_substring "ceros" "e" *)
  (* prefix "e" "ceros" = false *)
  (* contains_substring "eros" "e" *)
  (* prefix "e" "eros" = true, included *)

  (* contains_substring "seagull" "e" *)
  (* prefix "e" "seagull" = false *)
  (* contains_substring "eagull" "e" *)
  (* prefix "e" "eagull" = true, included *)

  reflexivity.
Qed.