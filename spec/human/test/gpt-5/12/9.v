Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
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

Example problem_12_test_case : problem_12_spec ["123"; "12"; "1234"; "1"; "12345"] (Some "12345").
Proof.
  right.
  exists "12345". exists 4.
  split. reflexivity.
  split. simpl; lia.
  split. simpl; lia.
  split. simpl; reflexivity.
  split. intros j Hj. exists "12345". intros _. simpl. lia.
  intros j Hj. exists "". intros _. simpl. lia.
Qed.