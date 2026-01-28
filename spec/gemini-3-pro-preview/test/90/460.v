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

Example test_case : next_smallest_spec [-69; 7; 9; -81; 2; 9; -1; -10] (Some (-69)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -69 is in the list *)
    simpl. left. reflexivity.
  - (* Prove existence of m=-81 *)
    exists (-81).
    split.
    + (* Prove -81 is in the list *)
      simpl. right. right. right. left. reflexivity.
    + split.
      * (* Prove -81 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -81 < -69 *)
           lia.
        -- (* Prove -69 is the next smallest after -81 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.