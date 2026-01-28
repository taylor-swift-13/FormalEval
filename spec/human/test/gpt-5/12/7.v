Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
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

Example problem_12_test_empty : problem_12_spec ["dog"; "cat"; "horse"; "cow"] (Some "horse").
Proof.
  right.
  exists "horse".
  exists 2.
  split.
  - reflexivity.
  - split.
    + simpl. unfold gt. unfold lt. apply le_S. apply le_S. apply le_S. apply le_n.
    + split.
      * simpl. unfold lt. apply le_S. apply le_n.
      * split.
        { simpl. reflexivity. }
        { split.
          - intros j Hj. exists "dog". intros _. simpl. apply le_S. apply le_S. apply le_n.
          - intros j Hj. exists "dog". intros _. simpl. unfold lt. apply le_S. apply le_n.
        }
Qed.