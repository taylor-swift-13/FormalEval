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

Example test_longest_1 : longest_spec [""%string; "a"%string; "1234"%string; "dog"%string; "aa"%string] (Some "1234"%string).
Proof.
  unfold longest_spec.
  exists "1234"%string.
  split.
  - reflexivity.
  - exists [""%string; "a"%string], ["dog"%string; "aa"%string].
    split.
    + reflexivity.
    + split.
      * intros x H.
        simpl in H.
        destruct H as [H | [H | []]]; subst; simpl; repeat constructor.
      * intros x H.
        simpl in H.
        repeat (destruct H as [H | H]; [subst; simpl; repeat constructor | idtac]).
        contradiction.
Qed.