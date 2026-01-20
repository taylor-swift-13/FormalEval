Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [1; 2; 3] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right. right. left. reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | H4]]].
    + (* Case x = 1 *)
      (* Using lia handles the arithmetic and equality automatically, avoiding rewrite errors *)
      lia.
    + (* Case x = 2 *)
      lia.
    + (* Case x = 3 *)
      lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.