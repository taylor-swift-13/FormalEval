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
  problem_7_spec ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"] ["xxx"; "xxxAAA"; "xxx"] "xxx".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "xxx" "xxx" *)
  (* prefix "xxx" "xxx" = true *)
  (* contains_substring "asd" "xxx" *)
  (* prefix "xxx" "asd" = false *)
  (* contains_substring "sd" "xxx" = false *)
  (* ... eventually false *)
  (* contains_substring "xxy" "xxx" = false *)
  (* contains_substring "john doe" "xxx" = false *)
  (* contains_substring "xxxAAA" "xxx" *)
  (* prefix "xxx" "xxxAAA" = true *)
  (* contains_substring "xxx" "xxx" *)
  (* prefix "xxx" "xxx" = true *)
  reflexivity.
Qed.