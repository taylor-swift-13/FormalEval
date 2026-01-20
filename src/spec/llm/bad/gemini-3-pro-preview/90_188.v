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

Example test_case : next_smallest_spec [-10; -20; -51; -69; -30; -40; -50; 10; -70; -80; -90; -100; -90] (Some (-90)).
Proof.
  unfold next_smallest_spec.
  split.
  - simpl. repeat (left; reflexivity || right).
  - exists (-100).
    split.
    + simpl. repeat (left; reflexivity || right).
    + split.
      * intros k Hk.
        simpl in Hk.
        repeat (destruct Hk as [Hk | Hk] || destruct Hk); subst; try lia.
      * split.
        -- lia.
        -- intros x Hx Hgt.
           simpl in Hx.
           repeat (destruct Hx as [Hx | Hx] || destruct Hx); subst; try lia.
Qed.