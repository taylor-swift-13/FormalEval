Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
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

Example test_case : next_smallest_spec [1%Z; 1%Z; 74%Z; 1%Z; 0%Z; 0%Z; -1%Z; -1%Z; -2%Z; -2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 7%Z; -20%Z; -2%Z] (Some (-2)%Z).
Proof.
  unfold next_smallest_spec.
  split.
  - simpl. repeat (try (left; reflexivity); right).
  - exists (-20).
    split.
    + simpl. repeat (try (left; reflexivity); right).
    + split.
      * intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- lia.
        -- intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.