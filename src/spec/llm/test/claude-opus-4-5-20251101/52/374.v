Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (100 :: 200 :: 300 :: nil) 302 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
  - intros _. reflexivity.
Qed.