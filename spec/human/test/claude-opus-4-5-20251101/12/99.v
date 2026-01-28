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

Example test_problem_12 : problem_12_spec [""%string; "öäü"%string; "ß"%string; "Ø"%string; "æ"%string; "œ"%string; ""%string] (Some "öäü"%string).
Proof.
  unfold problem_12_spec.
  right.
  exists "öäü"%string, 1.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|[|[|[|[|[|[|]]]]]]]; try lia.
    + exists ""%string. intros _. simpl. lia.
    + exists "öäü"%string. intros _. simpl. lia.
    + exists "ß"%string. intros _. simpl. lia.
    + exists "Ø"%string. intros _. simpl. lia.
    + exists "æ"%string. intros _. simpl. lia.
    + exists "œ"%string. intros _. simpl. lia.
    + exists ""%string. intros _. simpl. lia.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|]; try lia.
    exists ""%string. intros _. simpl. lia.
Qed.