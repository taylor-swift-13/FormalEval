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

Example test_case_35 : problem_35_spec [1000000; 999999; 999998; 999997; 999996; 999995; 999994; 999993; 999992; 999991; 999990; 999989; -150; 999987; 999986; 999985; 999984; 999983; 999982; 999980; 999979; 999978; 999977; 999976; 999975; 999974; 999973; 999972; 999971; 999970] 1000000.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lia | ]).
    contradiction.
Qed.