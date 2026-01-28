Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 2; 5; 3; 4] 4 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* Contradiction: 5 is in the list and 5 < 4 is false *)
      inversion H as [|x l Hx Hl]; subst. (* 1 < 4 *)
      inversion Hl as [|x0 l0 Hx0 Hl0]; subst. (* 2 < 4 *)
      inversion Hl0 as [|x1 l1 Hx1 Hl1]; subst. (* 5 < 4 *)
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 5.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.