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

Example test_case : next_smallest_spec [11; 15; 12; -61; 16; 12; 14; 15; 15; 15] (Some 11).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove 11 is in the list *)
    simpl. tauto.
  - (* Prove existence of m=-61 *)
    exists (-61).
    split.
    + (* Prove -61 is in the list *)
      simpl. tauto.
    + split.
      * (* Prove -61 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -61 < 11 *)
           lia.
        -- (* Prove 11 is the next smallest after -61 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.