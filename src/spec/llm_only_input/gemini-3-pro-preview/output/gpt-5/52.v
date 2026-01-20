Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Part 1: res = true <-> Forall ... *)
    split.
    + (* -> *)
      intros _.
      (* Prove that all elements in [1; 2; 4; 10] are < 100 *)
      repeat constructor; lia.
    + (* <- *)
      intros _.
      reflexivity.
  - (* Part 2: res = false <-> exists ... *)
    split.
    + (* -> *)
      intros H.
      (* true = false is a contradiction *)
      discriminate H.
    + (* <- *)
      intros [x [HIn HLe]].
      (* Prove that no element in the list is >= 100 *)
      simpl in HIn.
      repeat destruct HIn as [HEq | HIn]; subst; try lia.
Qed.