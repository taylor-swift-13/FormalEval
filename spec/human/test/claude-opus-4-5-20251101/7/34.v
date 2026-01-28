Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

(* 判断 s 是否包含子串 sub *)
Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
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

Definition problem_7_pre : Prop := True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  output = filter_by_substring_impl input sub.

Example test_filter_by_substring :
  problem_7_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"; "dcbd"; "cfloaccinaucinihilipilificatilinionda"] [] "bbc".
Proof.
  unfold problem_7_spec.
  simpl.
  reflexivity.
Qed.