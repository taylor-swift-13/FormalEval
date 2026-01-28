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

Example test_case : next_smallest_spec [23; 21; 19; 17; 15; 13; 5; 11; 9; 7; 5; 1; 5] (Some 5).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove 5 is in the list *)
    simpl. do 6 right. left. reflexivity.
  - (* Prove existence of m=1 *)
    exists 1.
    split.
    + (* Prove 1 is in the list *)
      simpl. do 11 right. left. reflexivity.
    + split.
      * (* Prove 1 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove 1 < 5 *)
           lia.
        -- (* Prove 5 is the next smallest after 1 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.