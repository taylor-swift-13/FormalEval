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
  problem_7_spec ["123"; "456"; "789"; "101112"] [] "122".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "123" "122" *)
  (* prefix "122" "123" is false *)
  (* contains_substring "23" "122" false *)
  (* contains_substring "3" "122" false *)
  (* contains_substring EmptyString "122" false *)
  (* So false *)
  (* contains_substring "456" "122" similarly false *)
  (* contains_substring "789" "122" false *)
  (* contains_substring "101112" "122" *)
  (* prefix "122" "101112" is false *)
  (* contains_substring "01112" "122" false *)
  (* ... eventually false *)
  (* So no elements included, output = [] *)
  reflexivity.
Qed.