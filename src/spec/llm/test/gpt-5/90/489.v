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

Example next_smallest_spec_test_case :
  next_smallest_spec [0%Z; -60%Z; 2%Z; 0%Z; -89%Z; 0%Z; -30%Z; 12%Z; 2%Z; 1%Z; -60%Z] (Some (-60%Z)).
Proof.
  unfold next_smallest_spec.
  exists (-89%Z).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. right. right. right. right. left. reflexivity.
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
      inversion Hx.
  - split.
    + simpl. right. left. reflexivity.
    + split.
      * lia.
      * intros y Hy Hylt.
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
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
        inversion Hy.
Qed.