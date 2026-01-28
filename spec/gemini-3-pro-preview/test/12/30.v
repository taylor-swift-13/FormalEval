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

Example test_longest_simple : longest_spec ["aa"; "apple"; "p"; "qq"; "apple"; "p"; "p"; "aa"]%string (Some "apple"%string).
Proof.
  unfold longest_spec.
  exists "apple"%string.
  split.
  - reflexivity.
  - exists ["aa"%string], ["p"; "qq"; "apple"; "p"; "p"; "aa"]%string.
    split.
    + reflexivity.
    + split.
      * intros x H.
        simpl in H. destruct H as [H | H]; [subst; simpl; repeat constructor | contradiction].
      * intros x H.
        repeat (destruct H as [H | H]; [subst; simpl; repeat constructor | ]).
        contradiction.
Qed.