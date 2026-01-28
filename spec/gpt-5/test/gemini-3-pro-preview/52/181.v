Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 20; -30; 40; 20; -50] 19 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      inversion H as [|? ? H1 H2]; subst.
      inversion H2 as [|? ? H3 H4]; subst.
      lia.
  - split.
    + intros _.
      exists 20.
      split.
      * simpl. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.