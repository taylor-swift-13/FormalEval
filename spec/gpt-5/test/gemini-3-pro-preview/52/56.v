Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [4; -4; 7; 10] 7 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate.
    + intros H.
      inversion H as [|x1 l1 H1 Hrest1]; subst.
      inversion Hrest1 as [|x2 l2 H2 Hrest2]; subst.
      inversion Hrest2 as [|x3 l3 H3 Hrest3]; subst.
      lia.
  - split.
    + intros _.
      exists 7.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.