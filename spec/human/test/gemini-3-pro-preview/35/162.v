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

Example test_case_35 : problem_35_spec [-34%Z; -1%Z; -5%Z; -10%Z; -15%Z; -20%Z; -25%Z; -30%Z; -35%Z; -40%Z; -45%Z; -50%Z; -55%Z; -60%Z; -65%Z; -70%Z; -75%Z; -80%Z; -85%Z; -90%Z; -95%Z; -100%Z; -105%Z; -110%Z; -115%Z; -120%Z; -125%Z; -130%Z; -135%Z; -140%Z; -145%Z; -150%Z] (-1%Z).
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [lia | ]).
    contradiction.
Qed.