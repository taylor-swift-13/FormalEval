Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

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

Example longest_spec_dog_cat_horse_cow_q :
  longest_spec ("dog" :: "cat" :: "horse" :: "cow" :: "q" :: nil) (Some "horse").
Proof.
  unfold longest_spec; simpl; split.
  - intros H. discriminate H.
  - intros _. exists 5.
    split.
    + simpl. reflexivity.
    + exists "horse".
      split.
      * simpl. right. simpl. right. simpl. left. reflexivity.
      * split.
        { simpl. reflexivity. }
        split.
        { reflexivity. }
        { intros t Hin Hlen.
          simpl in Hin.
          destruct Hin as [Ht | Hin].
          - subst. exfalso. simpl in Hlen. discriminate Hlen.
          - simpl in Hin. destruct Hin as [Ht | Hin].
            + subst. exfalso. simpl in Hlen. discriminate Hlen.
            + simpl in Hin. destruct Hin as [Ht | Hin].
              * subst. reflexivity.
              * simpl in Hin. destruct Hin as [Ht | Hin].
                { subst. exfalso. simpl in Hlen. discriminate Hlen. }
                { simpl in Hin. destruct Hin as [Ht | Hin].
                  - subst. exfalso. simpl in Hlen. discriminate Hlen.
                  - contradiction Hin.
                }
        }
Qed.