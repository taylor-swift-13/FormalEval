Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [1%Z; 3%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 3%Z; 17%Z; 17%Z; 18%Z; 19%Z; -95%Z; 20%Z; 3%Z] 20%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [ subst; lia | ]).
    contradiction.
Qed.