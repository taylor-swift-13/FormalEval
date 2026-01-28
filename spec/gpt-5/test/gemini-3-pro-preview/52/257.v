Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 6000001; -30; 40; -50] 13 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* Prove contradiction: Forall < 13 but 6000001 >= 13 is in list *)
      assert (In 6000001 [10; 6000001; -30; 40; -50]) as HIn.
      { simpl. right. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ HIn).
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Witness that violates the threshold *)
      exists 6000001.
      split.
      * simpl. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.