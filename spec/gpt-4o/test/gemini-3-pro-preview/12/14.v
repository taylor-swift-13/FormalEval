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

Example test_longest_spec_simple: longest_spec ["aa"; "bb"; "cc"; "aaa"; "123"; "cccc"; "cc"; "cccc"] (Some "cccc").
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 4.
    split.
    + reflexivity.
    + exists "cccc".
      split.
      * simpl. right. right. right. right. right. left. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t Hin Hlen.
              simpl in Hin.
              repeat (destruct Hin as [H | Hin]; [subst; simpl in Hlen; try discriminate; try reflexivity | ]).
              contradiction.
Qed.