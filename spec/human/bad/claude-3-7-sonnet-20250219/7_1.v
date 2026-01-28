Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

(* 判断 s 是否包含子串 sub *)
Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
  | String _ rest =>
      if String.prefix s sub then true
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

Example test_filter_by_substring_empty_john :
  problem_7_spec [""; "john"] [] "a".
Proof.
  unfold problem_7_spec.
  simpl.

  (* Evaluate contains_substring "" "a" *)
  unfold contains_substring.
  simpl.
  destruct (String.eqb "a" EmptyString) eqn:Hsub.
  - apply String.eqb_eq in Hsub. discriminate.
  - reflexivity.

  simpl.

  (* Evaluate contains_substring "john" "a" *)
  unfold contains_substring.
  simpl.
  destruct (String.prefix "john" "a") eqn:Hpref.
  - discriminate.
  - simpl.

    (* contains_substring "ohn" "a" *)
    remember (contains_substring "ohn" "a") as cs_ohn eqn:Ecs1.
    clear Ecs1.
    unfold contains_substring.
    simpl.
    destruct (String.prefix "ohn" "a") eqn:Hpref2.
    + discriminate.
    + simpl.

      remember (contains_substring "hn" "a") as cs_hn eqn:Ecs2.
      clear Ecs2.
      unfold contains_substring.
      simpl.
      destruct (String.prefix "hn" "a") eqn:Hpref3.
      * discriminate.
      * simpl.

        remember (contains_substring "n" "a") as cs_n eqn:Ecs3.
        clear Ecs3.
        unfold contains_substring.
        simpl.
        destruct (String.prefix "n" "a") eqn:Hpref4.
        -- discriminate.
        -- simpl.

           remember (String.eqb "a" EmptyString) as eqb_res eqn:Heqb.
           destruct eqb_res.
           ++ apply String.eqb_eq in Heqb. discriminate.
           ++ reflexivity.
Qed.