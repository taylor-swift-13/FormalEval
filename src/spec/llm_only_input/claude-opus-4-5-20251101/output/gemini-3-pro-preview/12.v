Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
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

Example test_longest_empty_string : longest_spec [""%string] (Some ""%string).
Proof.
  unfold longest_spec.
  exists ""%string.
  split.
  - reflexivity.
  - exists [], [].
    split.
    + simpl. reflexivity.
    + split.
      * intros x H. inversion H.
      * intros x H. simpl in H. destruct H as [H | H].
        -- rewrite <- H. simpl. apply le_n.
        -- inversion H.
Qed.