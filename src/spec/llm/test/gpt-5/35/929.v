Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [1%Z; -30%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 6%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z; 20%Z; 9%Z] 20%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - set (prefix := [1%Z; -30%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 6%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z]).
    change (In 20%Z (prefix ++ [20%Z; 9%Z])).
    apply in_or_app. right. simpl. left. reflexivity.
  - intros x H.
    set (prefix := [1%Z; -30%Z; 3%Z; 5%Z; 6%Z; 6%Z; 6%Z; 8%Z; 8%Z; 9%Z; 9%Z; 6%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z]).
    change (In x (prefix ++ [20%Z; 9%Z])) in H.
    apply in_app_or in H.
    destruct H as [H|H].
    + assert (F : Forall (fun z => z <= 20%Z) prefix).
      { subst prefix. repeat (constructor; try lia). }
      eapply Forall_forall in F; eauto.
    + simpl in H. destruct H as [H|[H|[]]]; subst; lia.
Qed.