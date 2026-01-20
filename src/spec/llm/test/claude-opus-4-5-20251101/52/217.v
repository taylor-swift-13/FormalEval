Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (8000001 :: 10000000 :: 9000000 :: 10 :: 8000000 :: 7000000 :: 6000000 :: 2000000 :: nil) 10000001 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
  - intros _. reflexivity.
Qed.