Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [50; 49; 49; 47; 49] 50.
Proof.
  unfold max_element_spec.
  split.
  - (* Prove that 50 is in the list [50; 49; 49; 47; 49] *)
    simpl.
    left. reflexivity.
  - (* Prove that for all x in [50; 49; 49; 47; 49], x <= 50 *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
    + (* Case x = 50 *)
      rewrite H1.
      lia.
    + (* Case x = 49 *)
      rewrite H2.
      lia.
    + (* Case x = 49 *)
      rewrite H3.
      lia.
    + (* Case x = 47 *)
      rewrite H4.
      lia.
    + (* Case x = 49 *)
      rewrite H5.
      lia.
    + (* Case False *)
      contradiction.
Qed.