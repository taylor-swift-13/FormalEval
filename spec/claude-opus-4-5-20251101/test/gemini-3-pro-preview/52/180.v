Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [10%Z; 20%Z; -30%Z; 40%Z; -50%Z; 20%Z] 499%Z true.
Proof.
  (* Unfold the specification definition *)
  unfold below_threshold_spec.
  
  (* Split the bi-implication (<->) into two subgoals *)
  split.
  
  - (* Direction: result = true -> (forall x, In x l -> x < t) *)
    intros _ x HIn.
    (* Simplify the list membership hypothesis *)
    simpl in HIn.
    (* Destruct the disjunctions arising from the list membership *)
    destruct HIn as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case x = 10 *)
      subst. lia.
    + (* Case x = 20 *)
      subst. lia.
    + (* Case x = -30 *)
      subst. lia.
    + (* Case x = 40 *)
      subst. lia.
    + (* Case x = -50 *)
      subst. lia.
    + (* Case x = 20 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
      
  - (* Direction: (forall x, In x l -> x < t) -> result = true *)
    intros _.
    reflexivity.
Qed.