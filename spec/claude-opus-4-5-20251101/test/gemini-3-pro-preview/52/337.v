Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2] 0 false.
Proof.
  (* Unfold the specification definition *)
  unfold below_threshold_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Direction: result = true -> (forall x, In x l -> x < t) *)
    intros H.
    (* result is false, so H implies False *)
    discriminate.
      
  - (* Direction: (forall x, In x l -> x < t) -> result = true *)
    intros H.
    (* We need to show false = true, which is impossible.
       We derive a contradiction from the hypothesis H.
       H states that all elements in the list are < 0.
       We show that 100 is in the list and 100 < 0 is false. *)
    assert (Hin : In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2]).
    { simpl. left. reflexivity. }
    specialize (H 100 Hin).
    lra.
Qed.