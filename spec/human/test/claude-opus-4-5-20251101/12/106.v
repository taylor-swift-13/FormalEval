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

Example test_problem_12 : problem_12_spec ["Apple"; "Avocado"; "Banana"; "Blueberry"; "Cherry"; "Durian"; "Fig"; "Grape"; "Kiwi"; "Lemon"; "Mango"; "Orange"]%string (Some "Blueberry"%string).
Proof.
  unfold problem_12_spec.
  right.
  exists "Blueberry"%string, 3.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]].
    + exists "Apple"%string. intros _. simpl. lia.
    + exists "Avocado"%string. intros _. simpl. lia.
    + exists "Banana"%string. intros _. simpl. lia.
    + exists "Blueberry"%string. intros _. simpl. lia.
    + exists "Cherry"%string. intros _. simpl. lia.
    + exists "Durian"%string. intros _. simpl. lia.
    + exists "Fig"%string. intros _. simpl. lia.
    + exists "Grape"%string. intros _. simpl. lia.
    + exists "Kiwi"%string. intros _. simpl. lia.
    + exists "Lemon"%string. intros _. simpl. lia.
    + exists "Mango"%string. intros _. simpl. lia.
    + exists "Orange"%string. intros _. simpl. lia.
    + lia.
  - intros j Hj.
    destruct j as [|[|[|]]].
    + exists "Apple"%string. intros _. simpl. lia.
    + exists "Avocado"%string. intros _. simpl. lia.
    + exists "Banana"%string. intros _. simpl. lia.
    + lia.
Qed.