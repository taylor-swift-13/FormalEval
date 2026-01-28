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
  problem_7_spec ["hello"; "world"; "python"; "numpy"; "pandas"; "antidisestablishmentariasaturnnismpy"] [] "z".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "hello" "z" *)
  (* prefix "z" "hello" = false *)
  (* contains_substring "ello" "z" = false *)
  (* contains_substring "llo" "z" = false *)
  (* contains_substring "lo" "z" = false *)
  (* contains_substring "o" "z" = false *)
  (* contains_substring "" "z" = false *)
  (* so false *)

  (* similarly for "world", "python", "numpy", "pandas", "antidisestablishmentariasaturnnismpy" *)

  (* none contain "z" as substring *)

  reflexivity.
Qed.