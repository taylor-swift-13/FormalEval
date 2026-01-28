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
    ["supercalifragilisticexpialidocious"; "antidisesshmentarianism"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"; "floccinaucinihilipilifi101112cation"]
    ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"; "floccinaucinihilipilifi101112cation"] "ili".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "supercalifragilisticexpialidocious" "ili" *)
  (* prefix "ili" "supercalifragilisticexpialidocious" = false *)
  (* contains_substring "upercalifragilisticexpialidocious" "ili" *)
  (* prefix "ili" "upercalifragilisticexpialidocious" = false *)
  (* ... recurse until the substring starting at "ili" is found *)
  (* At "iligilisticexpialidocious" prefix "ili" = true *)
  (* So contains_substring = true *)
  (* include "supercalifragilisticexpialidocious" *)

  (* contains_substring "antidisesshmentarianism" "ili" *)
  (* Does not contain "ili", so false *)
  (* exclude it *)

  (* contains_substring "floccinaucinihilipilification" "ili" *)
  (* contains substring "ili" at "ilipilification" prefix true *)
  (* include it *)

  (* contains_substring "floccinaucinihilipilificatnion" "ili" *)
  (* similarly contains "ili" substring *)
  (* include it *)

  (* contains_substring "floccinaucinihilipilificatilinion" "ili" *)
  (* includes "ili" *)
  (* include it *)

  (* contains_substring "floccinaucinihilipilifi101112cation" "ili" *)
  (* includes "ili" *)
  (* include it *)

  reflexivity.
Qed.