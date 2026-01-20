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

Example longest_spec_banana_input :
  longest_spec ("apple" :: "banana" :: "banna" :: "banana" :: nil) (Some "banana").
Proof.
  unfold longest_spec; simpl; split.
  - intros H. inversion H.
  - intros _.
    set (xs := "apple" :: "banana" :: "banna" :: "banana" :: nil).
    exists (fold_right Nat.max 0 (map String.length xs)).
    split.
    + reflexivity.
    + exists "banana".
      split.
      * unfold xs; simpl; right; left; reflexivity.
      * split.
        { unfold xs; simpl; reflexivity. }
        split.
        { reflexivity. }
        intros t Hin Hlen.
        unfold xs in Hin.
        simpl in Hin.
        destruct Hin as [Ht | Hin1].
        { subst t.
          exfalso.
          unfold xs in Hlen; simpl in Hlen; discriminate.
        }
        destruct Hin1 as [Ht | Hin2].
        { subst t. reflexivity. }
        destruct Hin2 as [Ht | Hin3].
        { subst t.
          exfalso.
          unfold xs in Hlen; simpl in Hlen; discriminate.
        }
        simpl in Hin3.
        destruct Hin3 as [Ht | HinNil].
        { subst t. reflexivity. }
        contradiction HinNil.
Qed.