Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; 2000; -200; 0; 500; 300] 13 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove contradiction: First element 100 is not < 13 *)
      inversion H; subst.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Provide witness 100 which is >= 13 *)
      exists 100.
      split.
      * simpl. left. reflexivity.
      * lia.
    + intros _.
      reflexivity.
Qed.