Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Import ListNotations.
Open Scope string_scope.

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

Example test_longest_simple : longest_spec ["aa"; "z"; "p"; "q"] (Some "aa").
Proof.
  unfold longest_spec.
  exists [], "aa", ["z"; "p"; "q"].
  repeat split.
  - reflexivity.
  - reflexivity.
  - intros t H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst; simpl; repeat constructor.
  - intros t H.
    inversion H.
Qed.