Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition problem_34_spec (input output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Definition example_input := [5; 3; 5; 2; 3; 3; 9; 0; 123].
Definition example_output := [0; 2; 3; 5; 9; 123].

(* Show that example_output is sorted *)
Lemma example_output_sorted : Sorted Z.le example_output.
Proof.
  repeat constructor; lia.
Qed.

(* Show that example_output has no duplicates *)
Lemma example_output_nodup : NoDup example_output.
Proof.
  repeat constructor; discriminate.
Qed.

(* All elements of input appear in output *)
Lemma example_input_in_output : forall z, In z example_input -> In z example_output.
Proof.
  intros z Hin.
  simpl in *.
  repeat (destruct Hin as [Heq | Hin];
          [subst z; simpl; auto
          |]).
  all: repeat (destruct Hin; auto; fail).
Qed.

(* All elements of output appear in input *)
Lemma example_output_in_input : forall z, In z example_output -> In z example_input.
Proof.
  intros z Hin.
  simpl in *.
  repeat (destruct Hin as [Heq | Hin];
          [subst z; simpl; auto
          |]).
  all: repeat (destruct Hin; auto; fail).
Qed.

Example problem_34_example :
  problem_34_spec example_input example_output.
Proof.
  unfold problem_34_spec.
  repeat split.
  - apply example_output_sorted.
  - apply example_output_nodup.
  - intro z; split.
    + apply example_input_in_output.
    + apply example_output_in_input.
Qed.