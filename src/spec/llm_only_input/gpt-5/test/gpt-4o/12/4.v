Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

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

Example longest_spec_nonempty_aaa :
  longest_spec (""%string :: "a"%string :: "aa"%string :: "aaa"%string :: nil) (Some "aaa"%string).
Proof.
  unfold longest_spec; simpl; split.
  - intros H. inversion H.
  - intros _. exists 3. split.
    + simpl. reflexivity.
    + exists "aaa"%string. split.
      * right. right. right. left. reflexivity.
      * split.
        { simpl. reflexivity. }
        split.
        { reflexivity. }
        { intros t Hin Hlen.
          destruct Hin as [H0 | Hin].
          - subst. simpl in Hlen. exfalso. discriminate Hlen.
          - destruct Hin as [H1 | Hin].
            + subst. simpl in Hlen. exfalso. discriminate Hlen.
            + destruct Hin as [H2 | Hin].
              * subst. simpl in Hlen. exfalso. discriminate Hlen.
              * destruct Hin as [H3 | Hin].
                { subst. reflexivity. }
                { inversion Hin. } }
Qed.