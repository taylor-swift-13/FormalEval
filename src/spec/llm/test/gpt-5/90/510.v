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

Example next_smallest_spec_test_14_m100_m90_11_13_20_14_15_15_15 :
  next_smallest_spec [14%Z; -100%Z; -90%Z; 11%Z; 13%Z; 20%Z; 14%Z; 15%Z; 15%Z; 15%Z] (Some (-90%Z)).
Proof.
  unfold next_smallest_spec.
  exists (-100%Z).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. right. left. reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      destruct Hx as [Hx|Hx]; [subst; lia|].
      inversion Hx.
  - split.
    + simpl. right. right. left. reflexivity.
    + split.
      * lia.
      * intros y Hy Hylt.
        simpl in Hy.
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; exfalso; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        destruct Hy as [Hy|Hy]; [subst; lia|].
        inversion Hy.
Qed.