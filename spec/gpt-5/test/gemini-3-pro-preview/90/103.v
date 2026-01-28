Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_min_of_list (m : Z) (l : list Z) : Prop :=
  In m l /\ forall x, In x l -> m <= x.

Definition next_smallest_spec (lst : list Z) (r : option Z) : Prop :=
  match r with
  | None =>
      lst = [] \/
      (exists m, is_min_of_list m lst /\ forall x, In x lst -> x = m)
  | Some s =>
      exists m, is_min_of_list m lst /\ In s lst /\ m < s /\
                forall y, In y lst -> m < y -> s <= y
  end.

Example test_next_smallest_example:
  next_smallest_spec [1; 2; -3; -4; 5] (Some (-3)).
Proof.
  (* Unfold the specification *)
  unfold next_smallest_spec.
  (* Instantiate the existential quantifier with the minimum value -4 *)
  exists (-4).
  
  (* Split the conjunctions manually to avoid 'split' tactic errors on non-inductive goals *)
  split.
  - (* Part 1: Prove is_min_of_list -4 [1; 2; -3; -4; 5] *)
    unfold is_min_of_list.
    split.
    + (* Prove -4 is in the list *)
      simpl. right. right. right. left. reflexivity.
    + (* Prove -4 <= x for all x in the list *)
      intros x H.
      simpl in H.
      (* Decompose list membership and solve linear inequalities *)
      repeat destruct H as [H | H]; subst; lia.
  
  - (* Part 2: Prove remaining properties *)
    split.
    + (* Prove -3 is in the list *)
      simpl. right. right. left. reflexivity.
    + split.
      * (* Prove -4 < -3 *)
        lia.
      * (* Prove that for any y > -4 in the list, -3 <= y *)
        intros y HIn HGt.
        simpl in HIn.
        (* Check every element in the list *)
        repeat destruct HIn as [HIn | HIn]; subst; try lia.
Qed.