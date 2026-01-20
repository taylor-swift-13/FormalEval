Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
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

Example test_next_smallest : next_smallest_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] (Some 2%Z).
Proof.
  unfold next_smallest_spec.
  exists 1%Z.
  split.
  - unfold is_min_of_list.
    split.
    + simpl. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | H]]]]];
        subst; lia.
  - split.
    + simpl. right. left. reflexivity.
    + split.
      * lia.
      * intros y Hy Hlt.
        simpl in Hy.
        destruct Hy as [H | [H | [H | [H | [H | H]]]]];
          subst; lia.
Qed.