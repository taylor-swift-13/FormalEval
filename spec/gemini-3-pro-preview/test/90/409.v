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

Example test_case : next_smallest_spec [1; 2; 3; 3; 5; 6; 7; 9; 10; 0; -1; -2; -3; -5; -6; -7; -6; -10; 2; 3] (Some (-7)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -7 is in the list *)
    simpl. do 15 right. left. reflexivity.
  - (* Prove existence of m=-10 *)
    exists (-10).
    split.
    + (* Prove -10 is in the list *)
      simpl. do 17 right. left. reflexivity.
    + split.
      * (* Prove -10 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -10 < -7 *)
           lia.
        -- (* Prove -7 is the next smallest after -10 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.