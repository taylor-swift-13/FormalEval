Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_min_of_list (m : Z) (l : list Z) : Prop :=
  In m l /\ forall x, In x l -> m <= x.

Definition next_smallest_spec (lst : list Z) (r : option Z) : Prop :=
  match r with
  | None =>
      lst = [] \/
      (exists m, is_min_of_list m lst /\ forall x, In x lst -> x = m)
  | Some s =>
      exists m, is_min_of_list m lst /\ In s lst /\ m < s /\
                forall y, In y lst -> m < y -> s <= y
  end.

Example next_smallest_spec_test_neg109_23_21_17_15_13_11_9_7_neg90_1_17_9 :
  next_smallest_spec [-109%Z; 23%Z; 21%Z; 17%Z; 15%Z; 13%Z; 11%Z; 9%Z; 7%Z; -90%Z; 1%Z; 17%Z; 9%Z] (Some (-90%Z)).
Proof.
  unfold next_smallest_spec.
  exists (-109%Z).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      inversion Hx.
  - split.
    + simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      right. simpl.
      left. reflexivity.
    + split.
      * lia.
      * intros y Hy Hylt.
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; exfalso; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        inversion Hy.
Qed.