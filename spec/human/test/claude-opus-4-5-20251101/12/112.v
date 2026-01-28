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

Example test_problem_12 : problem_12_spec ["aaaa"; "bbbbbb"; "cccccccc"; "ddddddddd"; "fffffffffff"; "ggggggggggggg"; "ggggggggMangoggggg"; "hhhhhhhhhhhhhhhh"; "iiiiiiiiiiiiiiiiiii"; "ggggggggggggg"; "hhhhhhhhhhhhhhhh"] (Some "iiiiiiiiiiiiiiiiiii").
Proof.
  unfold problem_12_spec.
  right.
  exists "iiiiiiiiiiiiiiiiiii", 8.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]].
    + exists "aaaa". intros _. simpl. lia.
    + exists "bbbbbb". intros _. simpl. lia.
    + exists "cccccccc". intros _. simpl. lia.
    + exists "ddddddddd". intros _. simpl. lia.
    + exists "fffffffffff". intros _. simpl. lia.
    + exists "ggggggggggggg". intros _. simpl. lia.
    + exists "ggggggggMangoggggg". intros _. simpl. lia.
    + exists "hhhhhhhhhhhhhhhh". intros _. simpl. lia.
    + exists "iiiiiiiiiiiiiiiiiii". intros _. simpl. lia.
    + exists "ggggggggggggg". intros _. simpl. lia.
    + exists "hhhhhhhhhhhhhhhh". intros _. simpl. lia.
    + lia.
  - intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|]]]]]]]].
    + exists "aaaa". intros _. simpl. lia.
    + exists "bbbbbb". intros _. simpl. lia.
    + exists "cccccccc". intros _. simpl. lia.
    + exists "ddddddddd". intros _. simpl. lia.
    + exists "fffffffffff". intros _. simpl. lia.
    + exists "ggggggggggggg". intros _. simpl. lia.
    + exists "ggggggggMangoggggg". intros _. simpl. lia.
    + exists "hhhhhhhhhhhhhhhh". intros _. simpl. lia.
    + lia.
Qed.