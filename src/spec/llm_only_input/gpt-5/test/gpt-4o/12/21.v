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

Example longest_spec_nonempty_input :
  longest_spec ["aa"; "apple"; "p"; "qq"; "apple"] (Some "apple").
Proof.
  unfold longest_spec; split.
  - intros H; exfalso; discriminate H.
  - intros _. exists 5; split.
    + simpl. reflexivity.
    + exists "apple". split.
      * simpl. right. left. reflexivity.
      * split.
        { simpl. reflexivity. }
        split.
        { reflexivity. }
        intros t Hin Hlen.
        simpl in Hin.
        destruct Hin as [H | Hin].
        { subst. simpl in Hlen. discriminate. }
        destruct Hin as [H | Hin].
        { subst. reflexivity. }
        destruct Hin as [H | Hin].
        { subst. simpl in Hlen. discriminate. }
        destruct Hin as [H | Hin].
        { subst. simpl in Hlen. discriminate. }
        destruct Hin as [H | Hin].
        { subst. reflexivity. }
        { simpl in Hin. contradiction Hin. }
Qed.