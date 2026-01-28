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
  problem_7_spec ["supercalifragilisticexpialidocious"; "sun"; "floccinaucinihilipilificatioearthn"] ["supercalifragilisticexpialidocious"; "floccinaucinihilipilificatioearthn"] "ili".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "supercalifragilisticexpialidocious" "ili" *)
  (* prefix "ili" "super..." is false *)
  (* contains_substring "upercalifragilisticexpialidocious" "ili" *)
  (* prefix "ili" "uper..." false *)
  (* ... eventually substring "ili" found at "filistic..." indexes *)
  (* So contains_substring "supercalifragilisticexpialidocious" "ili" = true *)
  (* contains_substring "sun" "ili" *)
  (* prefix "ili" "sun" false *)
  (* contains_substring "un" "ili" false *)
  (* contains_substring "n" "ili" false *)
  (* contains_substring "" "ili" false *)
  (* so "sun" is excluded *)
  (* contains_substring "floccinaucinihilipilificatioearthn" "ili" *)
  (* substring "ili" is found in "hilipilificatioearthn" *)
  (* so true *)
  reflexivity.
Qed.