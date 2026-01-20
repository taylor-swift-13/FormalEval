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

Example longest_spec_input_1 :
  longest_spec ["123"; "12"; "1234"; "1"; "12345"] (Some "12345").
Proof.
  unfold longest_spec; simpl; split.
  - intros H. exfalso. discriminate H.
  - intros _. exists 5. split.
    + simpl. reflexivity.
    + exists "12345". split.
      * right. right. right. right. left. reflexivity.
      * split.
        { simpl. reflexivity. }
        { split.
          { reflexivity. }
          { intros t Hin Hlen.
            destruct Hin as [H1 | [H2 | [H3 | [H4 | [H5 | []]]]]].
            - subst t. simpl in Hlen. discriminate Hlen.
            - subst t. simpl in Hlen. discriminate Hlen.
            - subst t. simpl in Hlen. discriminate Hlen.
            - subst t. simpl in Hlen. discriminate Hlen.
            - subst t. reflexivity.
          }
        }
Qed.