Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 125; 62.5; 30.807804019985152] 2000 true.
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
    + (* Case x = 1000 *)
      subst. lra.
    + (* Case x = 500 *)
      subst. lra.
    + (* Case x = 250 *)
      subst. lra.
    + (* Case x = 125 *)
      subst. lra.
    + (* Case x = 62.5 *)
      subst. lra.
    + (* Case x = 30.807804019985152 *)
      subst. lra.
    + (* Case False (end of list) *)
      contradiction.
      
  - (* Direction: (forall x, In x l -> x < t) -> result = true *)
    intros _.
    reflexivity.
Qed.