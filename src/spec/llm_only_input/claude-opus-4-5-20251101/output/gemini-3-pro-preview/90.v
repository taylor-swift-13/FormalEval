Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition next_smallest_spec (lst : list Z) (res : option Z) : Prop :=
  match res with
  | None => 
      forall x y, In x lst -> In y lst -> x = y
  | Some z => 
      In z lst /\
      exists m, 
        In m lst /\ 
        (forall k, In k lst -> m <= k) /\ 
        m < z /\ 
        (forall x, In x lst -> m < x -> z <= x)
  end.

Example test_next_smallest : next_smallest_spec [1; 2; 3; 4; 5] (Some 2).
Proof.
  unfold next_smallest_spec.
  split.
  - (* In 2 [1; 2; 3; 4; 5] *)
    simpl. right. left. reflexivity.
  - (* exists m, ... *)
    exists 1.
    split.
    + (* In 1 [1; 2; 3; 4; 5] *)
      simpl. left. reflexivity.
    + split.
      * (* forall k, In k lst -> 1 <= k *)
        intros k Hk.
        simpl in Hk.
        destruct Hk as [H | [H | [H | [H | [H | H]]]]]; try lia; try contradiction.
      * split.
        -- (* 1 < 2 *)
           lia.
        -- (* forall x, In x lst -> 1 < x -> 2 <= x *)
           intros x Hx Hlt.
           simpl in Hx.
           destruct Hx as [H | [H | [H | [H | [H | H]]]]]; try lia; try contradiction.
Qed.