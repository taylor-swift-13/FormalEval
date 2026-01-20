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

Example test_longest_simple : longest_spec ["123456789"; "1234"; "12345"; "123"]%string (Some "123456789"%string).
Proof.
  unfold longest_spec.
  exists "123456789"%string.
  split.
  - reflexivity.
  - exists [], ["1234"; "12345"; "123"]%string.
    split.
    + reflexivity.
    + split.
      * intros x H. inversion H.
      * intros x H.
        simpl in H.
        destruct H as [H | [H | [H | [H | H]]]]; try contradiction; subst; simpl; repeat constructor.
Qed.