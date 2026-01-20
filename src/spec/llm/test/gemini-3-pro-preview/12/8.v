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

Example test_longest_simple : longest_spec ["apple"; "banana"; "pear"]%string (Some "banana"%string).
Proof.
  unfold longest_spec.
  exists "banana"%string.
  split.
  - reflexivity.
  - exists ["apple"%string], ["pear"%string].
    split.
    + reflexivity.
    + split.
      * intros x H.
        simpl in H. destruct H as [H | H].
        { rewrite <- H. simpl. repeat constructor. }
        { contradiction. }
      * intros x H.
        simpl in H.
        destruct H as [H | [H | [H | H]]].
        { rewrite <- H. simpl. repeat constructor. }
        { rewrite <- H. simpl. repeat constructor. }
        { rewrite <- H. simpl. repeat constructor. }
        { contradiction. }
Qed.