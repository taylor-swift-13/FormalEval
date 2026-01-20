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

Example test_case : next_smallest_spec [-10; -19; 46; -51; -30; -40; -50; -60; -70; -90; -100; -110; -10] (Some (-100)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -100 is in the list *)
    simpl. repeat (first [left; reflexivity | right]).
  - (* Prove existence of m=-110 *)
    exists (-110).
    split.
    + (* Prove -110 is in the list *)
      simpl. repeat (first [left; reflexivity | right]).
    + split.
      * (* Prove -110 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -110 < -100 *)
           lia.
        -- (* Prove -100 is the next smallest after -110 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.