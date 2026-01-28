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

Example test_case : next_smallest_spec [0; -60; 2; 0; 0; -30; 12; 2; 1; -60] (Some (-30)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -30 is in the list *)
    simpl. do 5 right. left. reflexivity.
  - (* Prove existence of m=-60 *)
    exists (-60).
    split.
    + (* Prove -60 is in the list *)
      simpl. right. left. reflexivity.
    + split.
      * (* Prove -60 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -60 < -30 *)
           lia.
        -- (* Prove -30 is the next smallest after -60 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.