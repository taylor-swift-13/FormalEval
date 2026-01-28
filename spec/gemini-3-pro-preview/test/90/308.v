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

Example test_case : next_smallest_spec [-5; 1; 3; 3; 5; 6; -11; 7; 9; 10; -1; -2; -3; -4; -5; -6; -7; -8; -10; 2; 1] (Some (-10)).
Proof.
  unfold next_smallest_spec.
  split.
  - simpl. do 18 right. left. reflexivity.
  - exists (-11).
    split.
    + simpl. do 6 right. left. reflexivity.
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