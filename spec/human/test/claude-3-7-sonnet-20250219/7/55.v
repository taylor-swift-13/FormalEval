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
  problem_7_spec ["abcdefg"; "abcdefg"; "universally"] [] "z".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "abcdefg" "z" *)
  (* prefix "z" "abcdefg" = false *)
  (* check "bcdefg", "z" = false *)
  (* check "cdefg", "z" = false *)
  (* check "defg", "z" = false *)
  (* check "efg", "z" = false *)
  (* check "fg", "z" = false *)
  (* check "g", "z" = false *)
  (* check EmptyString "z" = false *)
  (* so it returns false for each "abcdefg" *)
  (* similarly for "universally" since 'z' is not prefix anywhere *)
  reflexivity.
Qed.