Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
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

Example test_longest_iiiiiiiiiiiiiiiiiii :
  longest_spec ["iiiiiiiiiiiiiiiiiii"; "  a  "; "bb"; "ccc"; "bb"; "bb"; "ccc"] (Some "iiiiiiiiiiiiiiiiiii").
Proof.
  unfold longest_spec.
  split.
  - simpl. left. reflexivity.
  - split.
    + intros s' H. simpl in H.
      destruct H as [H | [H | [H | [H | [H | [H | [H | []]]]]]]]; subst; simpl; auto with arith.
    + intros prefix H_in H_len.
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | [H | []]]]]]]]; subst; simpl in H_len; try discriminate.
      left. reflexivity.
Qed.