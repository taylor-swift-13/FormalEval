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

Example test_longest_mixed : longest_spec [""; "hore"; ""; "nWa"; "aaa"; "pear"; "wRQ"; "qq"]%string (Some "hore"%string).
Proof.
  unfold longest_spec.
  exists "hore"%string.
  split.
  - reflexivity.
  - exists [""]%string.
    exists [""; "nWa"; "aaa"; "pear"; "wRQ"; "qq"]%string.
    split.
    + reflexivity.
    + split.
      * intros x H.
        destruct H as [H | H].
        -- rewrite <- H. simpl. repeat constructor.
        -- contradiction.
      * intros x H.
        repeat (destruct H as [H | H]; [ rewrite <- H; simpl; repeat constructor | ]).
        contradiction.
Qed.