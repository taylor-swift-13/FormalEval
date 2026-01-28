Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

(* Pre: no specific requirements for `longest` — accept any list of strings by default *)
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

Example test_problem_12 : problem_12_spec ["apple"; "banana"; "pear"] (Some "banana").
Proof.
  unfold problem_12_spec.
  right.
  exists "banana", 1.
  repeat split.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - reflexivity.
  - intros j Hj.
    simpl in Hj.
    destruct j.
    + exists "apple". intros H. inversion H. simpl. lia.
    + destruct j.
      * exists "banana". intros H. inversion H. simpl. lia.
      * destruct j.
        -- exists "pear". intros H. inversion H. simpl. lia.
        -- lia.
  - intros j Hj.
    simpl in Hj.
    destruct j.
    + exists "apple". intros H. inversion H. simpl. lia.
    + lia.
Qed.