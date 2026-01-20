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

Example test_next_smallest : next_smallest_spec [1; 2; 3; 4; 5] (Some 2).
Proof.
  unfold next_smallest_spec.
  exists 1.
  (* We avoid repeat split to prevent splitting non-conjunctions like 'In' or 'Z.lt' *)
  split.
  - (* Goal: is_min_of_list 1 ... *)
    unfold is_min_of_list.
    split.
    + (* Goal: In 1 ... *)
      simpl. left. reflexivity.
    + (* Goal: forall x, In x ... -> 1 <= x *)
      intros x H.
      simpl in H.
      destruct H as [H | [H | [H | [H | [H | H]]]]]; subst; lia.
  - (* Goal: In 2 ... /\ 1 < 2 /\ ... *)
    split.
    + (* Goal: In 2 ... *)
      simpl. right. left. reflexivity.
    + (* Goal: 1 < 2 /\ ... *)
      split.
      * (* Goal: 1 < 2 *)
        lia.
      * (* Goal: forall y, In y ... -> 1 < y -> 2 <= y *)
        intros y H_in H_gt.
        simpl in H_in.
        destruct H_in as [H | [H | [H | [H | [H | H]]]]]; subst.
        -- (* y = 1 *) lia.
        -- (* y = 2 *) lia.
        -- (* y = 3 *) lia.
        -- (* y = 4 *) lia.
        -- (* y = 5 *) lia.
        -- (* y in empty *) contradiction.
Qed.