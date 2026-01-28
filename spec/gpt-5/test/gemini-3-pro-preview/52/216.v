Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; -400; 499; -600] 8000001 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros _.
      (* Prove that all elements in the list are < 8000001 *)
      repeat constructor; lia.
    + intros _.
      reflexivity.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros H.
      (* true = false is impossible *)
      discriminate H.
    + intros [x [HIn HLe]].
      (* Prove that no element in the list is >= 8000001 *)
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | H]]]]; subst; lia.
Qed.