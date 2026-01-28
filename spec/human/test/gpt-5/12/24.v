Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Lia.
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

Example problem_12_test_case : problem_12_spec ["aa"; "bb"; "cc"; "aaa"; "1233"; "cccc"; "cccc"; "ccaaa"] (Some "ccaaa").
Proof.
  right.
  exists "ccaaa".
  exists 7.
  split; [reflexivity|].
  split; [simpl; lia|].
  split; [simpl; lia|].
  split; [simpl; reflexivity|].
  split.
  - intros j Hj.
    destruct j as [|j]; [exists "aa"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "bb"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cc"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "aaa"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "1233"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cccc"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cccc"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "ccaaa"; intros _; simpl; lia|].
    exfalso; simpl in Hj; lia.
  - intros j Hj.
    destruct j as [|j]; [exists "aa"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "bb"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cc"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "aaa"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "1233"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cccc"; intros _; simpl; lia|].
    destruct j as [|j]; [exists "cccc"; intros _; simpl; lia|].
    exfalso; simpl in Hj; lia.
Qed.