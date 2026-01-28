Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 20; -30; 40; 500; 20] 126 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove that Forall fails because 500 is not < 126 *)
      repeat match goal with
      | h : Forall _ (_ :: _) |- _ => inversion h; subst; clear h
      end.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 500.
      split.
      * (* Prove 500 is in the list *)
        simpl. do 4 right. left. reflexivity.
      * (* Prove 126 <= 500 *)
        lia.
    + intros _.
      reflexivity.
Qed.