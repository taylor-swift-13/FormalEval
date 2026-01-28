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
  problem_7_spec ["abcdefg"; "universally"] [] "z".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "abcdefg" "z" *)
  (* prefix "z" "abcdefg" = false *)
  (* contains_substring "bcdefg" "z" *)
  (* prefix "z" "bcdefg" = false *)
  (* contains_substring "cdefg" "z" = false *)
  (* contains_substring "defg" "z" = false *)
  (* contains_substring "efg" "z" = false *)
  (* contains_substring "fg" "z" = false *)
  (* contains_substring "g" "z" = false *)
  (* contains_substring EmptyString "z" = false *)
  (* so first element excluded *)
  (* contains_substring "universally" "z" *)
  (* prefix "z" "universally" = false *)
  (* contains_substring "niversally" "z" = false *)
  (* contains_substring "iversally" "z" = false *)
  (* contains_substring "versally" "z" = false *)
  (* contains_substring "ersally" "z" = false *)
  (* contains_substring "rsally" "z" = false *)
  (* contains_substring "sally" "z" = false *)
  (* contains_substring "ally" "z" = false *)
  (* contains_substring "lly" "z" = false *)
  (* contains_substring "ly" "z" = false *)
  (* contains_substring "y" "z" = false *)
  (* contains_substring EmptyString "z" = false *)
  (* so second element excluded *)
  reflexivity.
Qed.