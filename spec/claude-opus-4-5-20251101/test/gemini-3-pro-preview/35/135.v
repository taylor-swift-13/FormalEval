Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1; 3; 3; 5; 6; 6; 6; 8; 8; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 14; 15; 15; 15; 17; 17; 18; 19; 20; 999997] 999997.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    repeat (match goal with
            | [ |- ?x = ?x \/ _ ] => left; reflexivity
            | [ |- _ \/ _ ] => right
            end).
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [ subst; try lia | ]).
    contradiction.
Qed.