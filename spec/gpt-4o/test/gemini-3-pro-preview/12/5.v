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

Example test_longest_simple: longest_spec ["123456789"; "1234"; "12345"; "123"]%string (Some "123456789"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exists 9.
    split.
    + simpl. reflexivity.
    + exists "123456789"%string.
      split.
      * simpl. left. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t Hin Hlen.
              simpl in Hin.
              destruct Hin as [H1 | [H2 | [H3 | [H4 | H5]]]].
              ** symmetry. apply H1.
              ** rewrite <- H2 in Hlen. simpl in Hlen. inversion Hlen.
              ** rewrite <- H3 in Hlen. simpl in Hlen. inversion Hlen.
              ** rewrite <- H4 in Hlen. simpl in Hlen. inversion Hlen.
              ** contradiction.
Qed.