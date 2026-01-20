Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [12%Z; 1%Z; 3%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z; 20%Z; 999997%Z] 999997%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - change (In 999997%Z ([12%Z; 1%Z; 3%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z; 20%Z] ++ [999997%Z])).
    apply in_or_app.
    right. simpl. left. reflexivity.
  - intros x H.
    change (In x ([12%Z; 1%Z; 3%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z; 20%Z] ++ [999997%Z])) in H.
    apply in_app_iff in H.
    destruct H as [H|H].
    + simpl in H.
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|H]; [subst; lia |].
      destruct H as [Hx|[]]; subst; lia.
    + simpl in H.
      destruct H as [Hx|[]]; subst; lia.
Qed.