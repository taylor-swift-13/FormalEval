Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [2%Z; 4%Z; 6%Z; 8%Z] 6%Z false.
Proof.
  (* Unfold the specification definition *)
  unfold below_threshold_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Direction: false = true -> (forall x, In x l -> x < t) *)
    intros H.
    (* This direction is trivial because false = true is a contradiction *)
    discriminate.
      
  - (* Direction: (forall x, In x l -> x < t) -> false = true *)
    intros H.
    (* To prove False (implied by false = true), we find a counterexample in the list *)
    (* We claim that 6 is in the list and 6 < 6 is false *)
    specialize (H 6%Z).
    assert (In 6%Z [2%Z; 4%Z; 6%Z; 8%Z]).
    { simpl. right. right. left. reflexivity. }
    apply H in H0.
    (* Now we have 6 < 6, which is a contradiction *)
    lia.
Qed.