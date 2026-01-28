Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 3; 10; 4] 5 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      inversion H; subst.
      inversion H2; subst.
      inversion H3; subst.
      lia.
  - split.
    + intros _.
      exists 10.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.