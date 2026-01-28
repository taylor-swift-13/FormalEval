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
  problem_7_spec ["moon"; "stars"; "sun"; "planets"] ["stars"; "sun"; "planets"] "s".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "moon" "s" *)
  (* prefix "s" "moon" = false *)
  (* contains_substring "oon" "s": false *)
  (* contains_substring "on" "s": false *)
  (* contains_substring "n" "s": false *)
  (* contains_substring "" "s": false *)
  (* so "moon" not included *)
  (* contains_substring "stars" "s" *)
  (* prefix "s" "stars" = false *)
  (* contains_substring "tars" "s" *)
  (* prefix "s" "tars" = false *)
  (* contains_substring "ars" "s" *)
  (* prefix "s" "ars" = false *)
  (* contains_substring "rs" "s" *)
  (* prefix "s" "rs" = false *)
  (* contains_substring "s" "s" *)
  (* prefix "s" "s" = true *)
  (* contains_substring "stars" "s" = true *)
  (* included *)
  (* similarly "sun" contains "s" (prefix "s" "sun" = true) *)
  (* included *)
  (* "planets" contains "s"? *)
  (* prefix "s" "planets" = false *)
  (* substring "lanets" "s" ... finally substring "s" "s" true *)
  (* included *)
  reflexivity.
Qed.