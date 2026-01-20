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

Example test_longest_spec_horse :
  longest_spec (["horse"%string]) (Some "horse"%string).
Proof.
  unfold longest_spec; simpl.
  exists ([] : list string). exists ("horse"%string). exists ([] : list string).
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - intros t Hin. simpl in Hin. destruct Hin as [H|H].
    + subst. apply le_n.
    + inversion H.
  - intros t Hin. inversion Hin.
Qed.