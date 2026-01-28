Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  match strings with
  | [] => result = None
  | _ => 
      exists s, result = Some s /\
      exists prefix suffix,
        strings = prefix ++ [s] ++ suffix /\
        (forall x, In x prefix -> String.length x < String.length s) /\
        (forall x, In x strings -> String.length x <= String.length s)
  end.

Example test_longest_simple : longest_spec [""%string; "a"%string; "cow"%string; "aaa"%string; "aa"%string] (Some "cow"%string).
Proof.
  unfold longest_spec.
  exists "cow"%string.
  split.
  - reflexivity.
  - exists [""%string; "a"%string], ["aaa"%string; "aa"%string].
    split.
    + reflexivity.
    + split.
      * intros x H.
        simpl in H.
        repeat (destruct H as [H | H]; [subst; simpl; repeat constructor | idtac]).
        contradiction.
      * intros x H.
        simpl in H.
        repeat (destruct H as [H | H]; [subst; simpl; repeat constructor | idtac]).
        contradiction.
Qed.