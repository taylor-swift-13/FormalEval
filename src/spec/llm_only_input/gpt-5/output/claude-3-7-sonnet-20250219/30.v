Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example get_positive_spec_test :
  get_positive_spec [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] [4%Z; 5%Z; 6%Z].
Proof.
  unfold get_positive_spec.
  split.
  - intros x HInRes.
    split.
    + simpl in HInRes.
      simpl.
      destruct HInRes as [Hx | HInRes]; [subst; right; simpl; right; simpl; left; reflexivity |].
      destruct HInRes as [Hx | HInRes]; [subst; right; simpl; right; simpl; right; simpl; left; reflexivity |].
      destruct HInRes as [Hx | HInRes]; [subst; right; simpl; right; simpl; right; simpl; right; simpl; left; reflexivity |].
      contradiction.
    + simpl in HInRes.
      destruct HInRes as [Hx | HInRes]; [subst; lia |].
      destruct HInRes as [Hx | HInRes]; [subst; lia |].
      destruct HInRes as [Hx | HInRes]; [subst; lia |].
      contradiction.
  - intros x HInL Hpos.
    simpl in HInL.
    destruct HInL as [Hx | HInL].
    { subst. exfalso. lia. }
    simpl in HInL.
    destruct HInL as [Hx | HInL].
    { subst. exfalso. lia. }
    simpl in HInL.
    destruct HInL as [Hx | HInL].
    { subst. simpl. left. reflexivity. }
    simpl in HInL.
    destruct HInL as [Hx | HInL].
    { subst. simpl. right. left. reflexivity. }
    simpl in HInL.
    destruct HInL as [Hx | HInL].
    { subst. simpl. right. right. left. reflexivity. }
    contradiction.
Qed.