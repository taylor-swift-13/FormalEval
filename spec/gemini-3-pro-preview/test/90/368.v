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

Example test_case : next_smallest_spec [11; 74; 13; 16; 15; 13; 14; 15; 15; 15; 15; 13] (Some 13).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove 13 is in the list *)
    simpl. right. right. left. reflexivity.
  - (* Prove existence of m=11 *)
    exists 11.
    split.
    + (* Prove 11 is in the list *)
      simpl. left. reflexivity.
    + split.
      * (* Prove 11 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove 11 < 13 *)
           lia.
        -- (* Prove 13 is the next smallest after 11 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.