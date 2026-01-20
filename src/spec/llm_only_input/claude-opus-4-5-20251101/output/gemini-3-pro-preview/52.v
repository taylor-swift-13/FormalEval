Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec [1%Z; 2%Z; 4%Z; 10%Z] 100%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x Hin.
    simpl in Hin.
    destruct Hin as [H | [H | [H | [H | H]]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
  - intros _. reflexivity.
Qed.