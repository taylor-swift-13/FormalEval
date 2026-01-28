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

Example test_problem_12 : problem_12_spec ["aaa"%string; "aa"%string; "a"%string; "aaaa"%string] (Some "aaaa"%string).
Proof.
  unfold problem_12_spec.
  right.
  exists "aaaa"%string, 3.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|[|[|[|j']]]].
    + exists "aaa"%string. intros _. simpl. lia.
    + exists "aa"%string. intros _. simpl. lia.
    + exists "a"%string. intros _. simpl. lia.
    + exists "aaaa"%string. intros _. simpl. lia.
    + lia.
  - intros j Hj.
    destruct j as [|[|[|j']]].
    + exists "aaa"%string. intros _. simpl. lia.
    + exists "aa"%string. intros _. simpl. lia.
    + exists "a"%string. intros _. simpl. lia.
    + lia.
Qed.