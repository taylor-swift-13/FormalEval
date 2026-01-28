Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

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

Example test_longest_1 : longest_spec ["aaa"; "aa"; "a"; "aaaa"] (Some "aaaa").
Proof.
  unfold longest_spec.
  split.
  - (* Prove In "aaaa" strings *)
    simpl. repeat (right; try left; try reflexivity). left. reflexivity.
  - split.
    + (* Prove length of any string in list <= length "aaaa" *)
      intros s' H. simpl in H.
      destruct H as [H | [H | [H | [H | H]]]]; subst; simpl; lia.
    + (* Prove uniqueness/first property *)
      intros prefix HIn HLen.
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | H]]]]; subst; simpl in HLen.
      * (* prefix = "aaa" *) discriminate.
      * (* prefix = "aa" *) discriminate.
      * (* prefix = "a" *) discriminate.
      * (* prefix = "aaaa" *) left. reflexivity.
      * (* False *) contradiction.
Qed.