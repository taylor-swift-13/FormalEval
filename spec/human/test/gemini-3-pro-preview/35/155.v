Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz. (* Imports lia tactic for integer arithmetic *)
Import ListNotations.
Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [-5; -10; -15; -20; -25; -30; -35; -40; -45; -104; -50; -55; -60; -65; -70; -75; -80; -85; -90; -95; -100; -105; -110; -115; -120; -125; -130; -135; -140; -145; -150; -80] (-5).
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [lia | ]).
    contradiction.
Qed.