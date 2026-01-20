Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Local Open Scope string_scope.

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

Example longest_spec_nonempty_input :
  longest_spec ("123456789" :: "1234" :: "12345" :: "123" :: nil) (Some "123456789").
Proof.
  unfold longest_spec; simpl; split.
  - intros H; discriminate.
  - intros _. exists 9. split.
    + compute. reflexivity.
    + exists "123456789". split.
      * simpl. left. reflexivity.
      * split.
        { compute. reflexivity. }
        split.
        { reflexivity. }
        { intros t Hin Hlen.
          simpl in Hin.
          destruct Hin as [Ht | Hin].
          - subst. reflexivity.
          - simpl in Hin. destruct Hin as [Ht | Hin].
            + subst. simpl in Hlen. discriminate Hlen.
            + simpl in Hin. destruct Hin as [Ht | Hin].
              * subst. simpl in Hlen. discriminate Hlen.
              * simpl in Hin. destruct Hin as [Ht | Hin].
                -- subst. simpl in Hlen. discriminate Hlen.
                -- contradiction.
        }
Qed.