Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition problem_12_pre (input : list string) : Prop := True.

Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s -> String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> String.length s < String.length out)
  ).

Example problem_12_test_cow : problem_12_spec [""; "a"; "cow"; "aaa"; "aa"] (Some "cow").
Proof.
  right.
  exists "cow". exists 2.
  split; [reflexivity | ].
  split; [simpl; auto with arith | ].
  split; [simpl; auto with arith | ].
  split; [simpl; reflexivity | ].
  split.
  - intros j Hj. exists "". intros _. simpl. auto with arith.
  - intros j Hj. exists "". intros _. simpl. auto with arith.
Qed.