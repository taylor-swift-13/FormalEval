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

Example next_smallest_spec_test_negatives :
  next_smallest_spec [-10%Z; -30%Z; 8%Z; -60%Z; -80%Z; -7%Z; -90%Z; -100%Z; -110%Z; -20%Z; -20%Z] (Some (-100)%Z).
Proof.
  unfold next_smallest_spec.
  exists (-110%Z).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. left. reflexivity.
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
    + simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. left. reflexivity.
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
        inversion Hy.
Qed.