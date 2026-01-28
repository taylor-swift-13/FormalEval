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
    ["supercalifragilisticexpialidocious"; "antidisestablishmentarianism"; "floccinaucinihilipilification"]
    ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"]
    "ili".
Proof.
  unfold problem_7_spec.
  simpl.
  unfold contains_substring.
  (* Evaluate contains_substring for each element with "ili" *)
  (* For "supercalifragilisticexpialidocious": *)
  (* Does it contain "ili"? Yes, substring "ili" appears in "supercalifragilisticexpialidocious" *)
  (* so first is included *)
  (* For "antidisestablishmentarianism": *)
  (* Check contains_substring "antidisestablishmentarianism" "ili" = false *)
  (* so excluded *)
  (* For "floccinaucinihilipilification": *)
  (* contains_substring returns true as "ili" is substring *)
  (* so included *)
  reflexivity.
Qed.