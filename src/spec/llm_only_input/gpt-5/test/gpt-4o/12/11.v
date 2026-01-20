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

Example longest_spec_case :
  longest_spec ("aaa"%string :: "aa"%string :: "a"%string :: "aaaa"%string :: nil) (Some "aaaa"%string).
Proof.
  unfold longest_spec; simpl; split.
  - intros H; exfalso; discriminate H.
  - intros _. exists 4. split.
    + simpl. reflexivity.
    + exists "aaaa"%string. split.
      * simpl. right. right. right. left. reflexivity.
      * split.
        { simpl. reflexivity. }
        { split.
          { reflexivity. }
          { intros t Hin Hlen.
            simpl in Hin.
            destruct Hin as [H|[H|[H|[H|[]]]]]; subst; simpl in Hlen; try discriminate; reflexivity.
          }
        }
Qed.