Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [-4; -3; -2; 4; -4] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate.
    + intros H.
      repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
      end.
      lia.
  - split.
    + intros _.
      exists 4.
      split.
      * simpl. tauto.
      * lia.
    + intros _. reflexivity.
Qed.