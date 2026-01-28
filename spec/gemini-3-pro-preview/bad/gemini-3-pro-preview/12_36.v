Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

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

Example test_longest_simple : longest_spec ["dog"; "cat"] (Some "dog").
Proof.
  unfold longest_spec.
  exists "dog".
  split.
  - reflexivity.
  - exists [], ["cat"].
    split.
    + reflexivity.
    + split.
      * intros x H. inversion H.
      * intros x H.
        simpl in H.
        destruct H as [H | [H | H]].
        -- subst. simpl. apply le_n.
        -- subst. simpl. apply le_n.
        -- contradiction.
Qed.