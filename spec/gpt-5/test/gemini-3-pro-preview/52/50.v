Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 4; 7; 9] 6 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove contradiction: Forall (< 6) [1; 4; 7; 9] implies False *)
      repeat match goal with
      | [ H : Forall _ _ |- _ ] => inversion H; subst; clear H
      end.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Prove exists x, In x l /\ 6 <= x. Witness is 7. *)
      exists 7.
      split.
      * simpl. right; right; left; reflexivity.
      * lia.
    + intros _.
      reflexivity.
Qed.