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

Example test_problem_12 : problem_12_spec ["123456789"%string; "1234"%string; "12345"%string; "123"%string] (Some "123456789"%string).
Proof.
  unfold problem_12_spec.
  right.
  exists "123456789"%string, 0.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    destruct j as [|j'].
    + exists "123456789"%string. intros _. simpl. lia.
    + destruct j' as [|j''].
      * exists "1234"%string. intros _. simpl. lia.
      * destruct j'' as [|j'''].
        -- exists "12345"%string. intros _. simpl. lia.
        -- destruct j''' as [|j''''].
           ++ exists "123"%string. intros _. simpl. lia.
           ++ lia.
  - intros j Hj.
    lia.
Qed.