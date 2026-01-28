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

Example test_longest_xyz : longest_spec ["x"%string; "y"%string; "z"%string] (Some "x"%string).
Proof.
  unfold longest_spec.
  exists "x"%string.
  split.
  - reflexivity.
  - exists [], ["y"%string; "z"%string].
    split.
    + simpl. reflexivity.
    + split.
      * intros x H. inversion H.
      * intros x H.
        simpl in H.
        destruct H as [H | [H | [H | H]]]; subst; simpl; try apply le_n; contradiction.
Qed.