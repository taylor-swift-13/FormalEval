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

Example test_case : next_smallest_spec [1; 2; 3; 4; 5; 6; 7; 0; 10; -1; -2; -3; -4; -5; -6; -7; -8; 2] (Some (-7)).
Proof.
  unfold next_smallest_spec.
  split.
  - (* Prove -7 is in the list *)
    simpl.
    repeat (match goal with
            | |- ?x = ?x \/ _ => left; reflexivity
            | |- ?x = ?x => reflexivity
            | |- _ \/ _ => right
            end).
  - (* Prove existence of m=-8 *)
    exists (-8).
    split.
    + (* Prove -8 is in the list *)
      simpl.
      repeat (match goal with
              | |- ?x = ?x \/ _ => left; reflexivity
              | |- ?x = ?x => reflexivity
              | |- _ \/ _ => right
              end).
    + split.
      * (* Prove -8 is the minimum *)
        intros k Hk.
        simpl in Hk.
        repeat destruct Hk as [Hk | Hk]; subst; try lia.
      * split.
        -- (* Prove -8 < -7 *)
           lia.
        -- (* Prove -7 is the next smallest after -8 *)
           intros x Hx Hgt.
           simpl in Hx.
           repeat destruct Hx as [Hx | Hx]; subst; try lia.
Qed.