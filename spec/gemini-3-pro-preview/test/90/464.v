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

Example test_case : next_smallest_spec [-100; 1; 1; 0; 0; -1; -2; 16; 2; 3; 3; 4; 5; 13; 5; 6; 7; 7; 8; 6; 3; 7] (Some (-2)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -2 is in the list *)
    simpl. do 6 right. left. reflexivity.
  - (* Prove existence of m=-100 *)
    exists (-100).
    split.
    + (* Prove -100 is in the list *)
      simpl. left. reflexivity.
    + split.
      * (* Prove -100 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -100 < -2 *)
           lia.
        -- (* Prove -2 is the next smallest after -100 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.