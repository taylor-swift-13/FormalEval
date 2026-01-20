Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

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

Example test_longest_spec_nonempty :
  longest_spec (["abc"%string; "defghijklmnop"%string; ""%string; "hello"%string; "defghijklmnop"%string; "defghijklmnop"%string]) (Some "defghijklmnop"%string).
Proof.
  unfold longest_spec; simpl.
  exists ["abc"%string].
  exists "defghijklmnop"%string.
  exists [""%string; "hello"%string; "defghijklmnop"%string; "defghijklmnop"%string].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intros t H.
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        contradiction.
      * intros t H.
        simpl in H.
        destruct H as [H|H].
        { subst; simpl; lia. }
        contradiction.
Qed.