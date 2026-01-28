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
  next_smallest_spec [2; 2; 2; 3; 3; 3] (Some 3).
Proof.
  (* Unfold the specification *)
  unfold next_smallest_spec.
  (* Instantiate the existential quantifier with the minimum value 2 *)
  exists 2.
  
  (* Split the conjunctions manually *)
  split.
  - (* Part 1: Prove is_min_of_list 2 [2; 2; 2; 3; 3; 3] *)
    unfold is_min_of_list.
    split.
    + (* Prove 2 is in the list *)
      simpl. left. reflexivity.
    + (* Prove 2 <= x for all x in the list *)
      intros x H.
      simpl in H.
      repeat destruct H as [H | H]; subst; lia.
  
  - (* Part 2: Prove remaining properties *)
    split.
    + (* Prove 3 is in the list *)
      simpl. right. right. right. left. reflexivity.
    + split.
      * (* Prove 2 < 3 *)
        lia.
      * (* Prove that for any y > 2 in the list, 3 <= y *)
        intros y HIn HGt.
        simpl in HIn.
        repeat destruct HIn as [HIn | HIn]; subst; try lia.
Qed.