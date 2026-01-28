Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Import ListNotations.

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

Example test_longest_spec_simple: longest_spec ["123"; "12"; "1234"; "1"; "12345"]%string (Some "12345"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate.
  - intros _.
    exists 5.
    split.
    + simpl. reflexivity.
    + exists "12345"%string.
      split.
      * simpl. right. right. right. right. left. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t Hin Hlen.
              simpl in Hin.
              destruct Hin as [H | [H | [H | [H | [H | H]]]]].
              ** rewrite <- H in Hlen. simpl in Hlen. discriminate.
              ** rewrite <- H in Hlen. simpl in Hlen. discriminate.
              ** rewrite <- H in Hlen. simpl in Hlen. discriminate.
              ** rewrite <- H in Hlen. simpl in Hlen. discriminate.
              ** rewrite <- H. reflexivity.
              ** contradiction.
Qed.