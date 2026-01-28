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
  problem_7_spec ["The cat in the hat"; "Green eggs and ham"; "One fish two fish"; "Red fish blue fish"]
                 ["One fish two fish"; "Red fish blue fish"]
                 "fish".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "The cat in the hat" "fish" *)
  (* prefix "fish" "The cat in the hat" = false *)
  (* contains_substring (rest of string) "fish" will be false *)
  (* so not included *)
  (* similarly for "Green eggs and ham" *)
  (* no prefix "fish" found anywhere, so false *)
  (* "One fish two fish" contains "fish" *)
  (* so included *)
  (* "Red fish blue fish" contains "fish" *)
  (* included *)
  reflexivity.
Qed.