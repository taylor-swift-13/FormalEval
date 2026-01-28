Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [9.263975784000001%R; 5.5%R; 6.2%R; 8.565673083320917%R; 6.2%R] 10%R true.
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
    destruct HIn as [H | [H | [H | [H | [H | H]]]]].
    + (* Case x = 9.263975784000001 *)
      subst. lra.
    + (* Case x = 5.5 *)
      subst. lra.
    + (* Case x = 6.2 *)
      subst. lra.
    + (* Case x = 8.565673083320917 *)
      subst. lra.
    + (* Case x = 6.2 *)
      subst. lra.
    + (* Case False (end of list) *)
      contradiction.
      
  - (* Direction: (forall x, In x l -> x < t) -> result = true *)
    intros _.
    reflexivity.
Qed.