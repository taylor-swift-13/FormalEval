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
  problem_7_spec ["abc(d)e"; "ba%cd"; "cde"; "array"; "12345"] ["abc(d)e"] "(d)".
Proof.
  unfold problem_7_spec.
  simpl.
  (* contains_substring "abc(d)e" "(d)" *)
  (* prefix "(d)" "abc(d)e" = false *)
  (* contains_substring "bc(d)e" "(d)" *)
  (* prefix "(d)" "bc(d)e" = false *)
  (* contains_substring "c(d)e" "(d)" *)
  (* prefix "(d)" "c(d)e" = false *)
  (* contains_substring "(d)e" "(d)" *)
  (* prefix "(d)" "(d)e" = true *)
  (* so contains_substring "abc(d)e" "(d)" = true *)
  (* "abc(d)e" included *)
  (* contains_substring "ba%cd" "(d)" *)
  (* prefix "(d)" "ba%cd" = false *)
  (* check "a%cd", "%cd", "cd", "d", "" all false *)
  (* no *)
  (* so excluded *)
  (* similarly "cde", "array", "12345" do not contain "(d)" as substring *)
  simpl.
  reflexivity.
Qed.