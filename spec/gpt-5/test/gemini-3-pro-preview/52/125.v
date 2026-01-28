Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10000000; 9000000; 10000001; 10; 8000000; 6000000; 2000000] 10000001 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* Prove that Forall implies contradiction because 10000001 is not < 10000001 *)
      repeat match goal with H : Forall _ _ |- _ => inversion H; subst; clear H end.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 10000001.
      split.
      * (* Prove In 10000001 l *)
        simpl. do 2 right. left. reflexivity.
      * (* Prove 10000001 <= 10000001 *)
        lia.
    + intros _. reflexivity.
Qed.