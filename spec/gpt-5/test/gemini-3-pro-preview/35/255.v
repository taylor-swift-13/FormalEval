Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [999990; 2; 3; 1; 3; 2; 2; 2; 2; -140; 2; 999971; 2] 999990.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.