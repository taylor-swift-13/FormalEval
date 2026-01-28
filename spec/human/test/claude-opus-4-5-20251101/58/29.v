Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_58_pre (l1 l2 : list R) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list R) : Prop :=
  (forall x: R, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Rle l_out /\
  NoDup l_out.

Example test_common_1 :
  problem_58_spec [72.37521383648374; 75.77463522981091; (-68.50801238200772); (-16.457158264907306); (-14.710649879972792); (-50.826346308865425); 94.08151854781187; 62.25940015569594] 
                  [] 
                  [].
Proof.
  unfold problem_58_spec.
  split; [| split].
  - intro x.
    split.
    + intro H.
      simpl in H.
      contradiction.
    + intros [H1 H2].
      simpl in H2.
      contradiction.
  - constructor.
  - constructor.
Qed.