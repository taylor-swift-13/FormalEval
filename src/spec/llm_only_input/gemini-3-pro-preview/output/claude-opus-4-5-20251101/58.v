Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Specification Definitions *)
Definition is_sorted (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    (Z.le (nth i l 0%Z) (nth j l 0%Z)).

Definition no_duplicates {A : Type} (l : list A) : Prop :=
  NoDup l.

Definition is_intersection {A : Type} (l1 l2 result : list A) : Prop :=
  forall x, In x result <-> (In x l1 /\ In x l2).

Definition common_spec (l1 l2 result : list Z) : Prop :=
  is_intersection l1 l2 result /\
  no_duplicates result /\
  is_sorted result.

(* Test Case Proof *)
Example test_common_spec : 
  common_spec 
    [1; 4; 3; 34; 653; 2; 5] 
    [5; 7; 1; 5; 9; 653; 121] 
    [1; 5; 653].
Proof.
  unfold common_spec.
  split.
  - (* Part 1: is_intersection *)
    unfold is_intersection.
    intros x.
    (* Simplify list membership to logical disjunctions *)
    simpl.
    (* Prove equivalence by exhaustion on the finite cases *)
    intuition; subst; try lia.
  - split.
    + (* Part 2: no_duplicates *)
      unfold no_duplicates.
      (* Construct the NoDup proof step-by-step *)
      repeat (constructor; simpl; intuition).
    + (* Part 3: is_sorted *)
      unfold is_sorted.
      intros i j H_idx H_len.
      simpl in H_len.
      (* Analyze indices i and j. Since length is 3, indices are small. *)
      (* We destruct i and j to handle concrete values (0, 1, 2) *)
      repeat (destruct i; try lia); 
      repeat (destruct j; try lia);
      (* Evaluate nth for the valid concrete indices and check inequality *)
      simpl; lia.
Qed.