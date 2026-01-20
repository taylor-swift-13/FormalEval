Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [2000000; 8000001; 10000000; 9000000; 10; 8000000; 7000000; 2000000; 6000000; 2000000] 10000001 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]; subst; lia.
  - intros _.
    reflexivity.
Qed.