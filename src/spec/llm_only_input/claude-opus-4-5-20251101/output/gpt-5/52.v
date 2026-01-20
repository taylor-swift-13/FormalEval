Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros _.
      repeat constructor; lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros [x [Hin Hle]].
      simpl in Hin.
      destruct Hin as [H | [H | [H | [H | H]]]]; subst; lia.
Qed.