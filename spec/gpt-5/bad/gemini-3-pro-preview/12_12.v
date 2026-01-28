Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Import ListNotations.

Definition longest_spec (strings : list string) (res : option string) : Prop :=
  match strings with
  | [] => res = None
  | _ =>
    exists l1 s l2,
      strings = l1 ++ s :: l2 /\
      res = Some s /\
      (forall t, In t strings -> String.length t <= String.length s) /\
      (forall t, In t l1 -> String.length t < String.length s)
  end.

Example test_longest_1 : longest_spec ["a"] (Some "a").
Proof.
  unfold longest_spec.
  exists [], "a", [].
  repeat split.
  - reflexivity.
  - reflexivity.
  - intros t H.
    simpl in H.
    destruct H as [H | H].
    + rewrite <- H. apply Le.le_n.
    + contradiction.
  - intros t H.
    inversion H.
Qed.