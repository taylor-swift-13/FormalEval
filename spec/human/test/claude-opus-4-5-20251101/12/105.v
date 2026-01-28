Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
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

Example test_problem_12 : problem_12_spec ["1"; "22"; "333"; "4444"; "55555"; "666666"; "7777777"; "88888888"; "999999999"; "10000000000"] (Some "10000000000").
Proof.
  unfold problem_12_spec.
  right.
  exists "10000000000", 9.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; simpl.
    + exists "1". intros _. simpl. lia.
    + exists "22". intros _. simpl. lia.
    + exists "333". intros _. simpl. lia.
    + exists "4444". intros _. simpl. lia.
    + exists "55555". intros _. simpl. lia.
    + exists "666666". intros _. simpl. lia.
    + exists "7777777". intros _. simpl. lia.
    + exists "88888888". intros _. simpl. lia.
    + exists "999999999". intros _. simpl. lia.
    + exists "10000000000". intros _. simpl. lia.
    + lia.
  - intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|[|]]]]]]]]]; simpl.
    + exists "1". intros _. simpl. lia.
    + exists "22". intros _. simpl. lia.
    + exists "333". intros _. simpl. lia.
    + exists "4444". intros _. simpl. lia.
    + exists "55555". intros _. simpl. lia.
    + exists "666666". intros _. simpl. lia.
    + exists "7777777". intros _. simpl. lia.
    + exists "88888888". intros _. simpl. lia.
    + exists "999999999". intros _. simpl. lia.
    + lia.
Qed.