Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [-1; -2; -3; -4; 0; -2] 0.
Proof.
  unfold problem_35_spec.
  split.
  - simpl.
    tauto.
  - intros x H.
    simpl in H.
    repeat destruct H as [H|H]; try lia; try contradiction.
Qed.