Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  match strings, result with
  | [], None => True
  | _, Some s =>
      In s strings /\
      (forall s', In s' strings -> String.length s' <= String.length s) /\
      (forall prefix, In prefix strings -> String.length prefix = String.length s -> s = prefix \/ 
        (exists after prefix', strings = prefix :: after /\ prefix' = s /\ In prefix after -> False))
  | _, None => strings = [] (* only None if input empty *)
  end.

Example test_longest_1 : longest_spec ["123456789"; "1234"; "12345"; "123"] (Some "123456789").
Proof.
  unfold longest_spec.
  split.
  - simpl. left. reflexivity.
  - split.
    + intros s' H.
      simpl in H.
      destruct H as [H | [H | [H | [H | H]]]].
      * subst. simpl. repeat constructor.
      * subst. simpl. repeat constructor.
      * subst. simpl. repeat constructor.
      * subst. simpl. repeat constructor.
      * contradiction.
    + intros prefix HIn HLen.
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | H]]]].
      * subst. left. reflexivity.
      * subst. simpl in HLen. discriminate.
      * subst. simpl in HLen. discriminate.
      * subst. simpl in HLen. discriminate.
      * contradiction.
Qed.