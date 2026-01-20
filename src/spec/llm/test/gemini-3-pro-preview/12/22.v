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

Example test_longest_simple : longest_spec ["dog"; "cat"; "horse"]%string (Some "horse")%string.
Proof.
  unfold longest_spec.
  exists "horse"%string.
  split.
  - reflexivity.
  - exists ["dog"; "cat"]%string, []%string.
    split.
    + reflexivity.
    + split.
      * intros x [H | [H | H]]; subst; simpl; repeat constructor; try contradiction.
      * intros x [H | [H | [H | H]]]; subst; simpl; repeat constructor; try contradiction.
Qed.