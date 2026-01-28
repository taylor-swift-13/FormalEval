Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Import ListNotations.
Open Scope string_scope.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  (strings = nil -> result = None) /\
  (strings <> nil ->
    exists maxlen,
      maxlen = fold_right Nat.max 0 (map String.length strings) /\
      exists s,
        In s strings /\
        String.length s = maxlen /\
        result = Some s /\
        (forall t, In t strings -> String.length t = maxlen -> t = s)).

Example test_longest_spec:
  longest_spec ["aa"; "apple"; "p"; "qq"; "apple"; "p"; "p"; "aa"] (Some "apple").
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 5.
    split.
    + reflexivity.
    + exists "apple".
      split.
      * simpl. right. left. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t Hin Hlen.
              simpl in Hin.
              destruct Hin as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst; try (simpl in Hlen; discriminate Hlen); try reflexivity.
              contradiction.
Qed.