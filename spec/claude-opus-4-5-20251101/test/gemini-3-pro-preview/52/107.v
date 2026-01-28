Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [2000000%Z; 10000000%Z; 9000000%Z; 10%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z] 10000001%Z true.
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
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
    + (* Case x = 2000000 *)
      subst. lia.
    + (* Case x = 10000000 *)
      subst. lia.
    + (* Case x = 9000000 *)
      subst. lia.
    + (* Case x = 10 *)
      subst. lia.
    + (* Case x = 8000000 *)
      subst. lia.
    + (* Case x = 7000000 *)
      subst. lia.
    + (* Case x = 6000000 *)
      subst. lia.
    + (* Case x = 2000000 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
      
  - (* Direction: (forall x, In x l -> x < t) -> result = true *)
    intros _.
    reflexivity.
Qed.