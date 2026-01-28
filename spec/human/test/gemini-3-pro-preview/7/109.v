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

Example test_problem_7: problem_7_spec
  [ "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America.";
    "To be or not to be, that is the question.";
    "It is a truth universally acknowledged, that a single man in possession of a good fortune, must be in want of a wife.";
    "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal.""";
    "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal.";
    "To be or not to be, that is the question." ]
  [ "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America." ]
  "ordain".
Proof.
  unfold problem_7_spec.
  reflexivity.
Qed.