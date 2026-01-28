Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Lemma problem_90_example : problem_90_spec [1; 2; 3; 4; 5] (Some 2).
Proof.
  unfold problem_90_spec.
  exists 1%Z.
  split. { simpl; auto. }
  split.
  - intros x H.
    destruct H as [->|H].
    + lia.
    + destruct H as [->|H].
      * lia.
      * destruct H as [->|H].
        -- lia.
        -- destruct H as [->|H].
           ++ lia.
           ++ destruct H.
  - split.
    { simpl; right; left; auto. }
    split.
    + lia.
    + intros y H H0.
      destruct H as [->|H].
      * exfalso; lia.
      * destruct H as [->|H].
        -- lia.
        -- destruct H as [->|H].
           ++ lia.
           ++ destruct H as [->|H].
              ** lia.
              ** destruct H.
Qed.