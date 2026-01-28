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
  problem_7_spec ["abcdefg"; EmptyString] ["abcdefg"] "a".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "abcdefg" "a" *)
  (* prefix "a" "abcdefg" = true *)
  (* so first element included *)
  (* contains_substring EmptyString "a" = false *)
  (* so second element excluded *)
  reflexivity.
Qed.