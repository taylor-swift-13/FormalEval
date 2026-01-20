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

Example next_smallest_spec_test_neg80_to_8 :
  next_smallest_spec [-80%Z; 1%Z; 1%Z; 0%Z; 0%Z; -1%Z; -1%Z; -2%Z; -2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 7%Z; -50%Z; 8%Z] (Some (-50%Z)).
Proof.
  unfold next_smallest_spec.
  exists (-80%Z).
  split.
  - unfold is_min_of_list.
    split.
    + simpl. left. reflexivity.
    + intros x Hx.
      repeat (simpl in Hx; destruct Hx as [Hx|Hx]; [subst; lia|]).
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
        repeat (simpl in Hy; destruct Hy as [Hy|Hy]; [subst; lia|]).
        inversion Hy.
Qed.