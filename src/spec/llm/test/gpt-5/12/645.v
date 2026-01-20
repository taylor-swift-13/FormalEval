Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition longest_spec (strings : list string) (res : option string) : Prop :=
  match strings with
  | [] => res = None
  | _ =>
    exists l1 s l2,
      strings = l1 ++ s :: l2 /\
      res = Some s /\
      (forall t, In t strings -> String.length t <= String.length s) /\
      (forall t, In t l1 -> String.length t < String.length s)
  end.

Example test_longest_spec_nonempty :
  longest_spec
    ["1"%string; "22"%string; "333"%string; "4444"%string; "666666"%string; "7777777"%string; "88888888"%string; "999999999"%string; "10000000000"%string; "22"%string; "7777777"%string]
    (Some "10000000000"%string).
Proof.
  unfold longest_spec; simpl.
  exists ["1"%string; "22"%string; "333"%string; "4444"%string; "666666"%string; "7777777"%string; "88888888"%string; "999999999"%string].
  exists "10000000000"%string.
  exists ["22"%string; "7777777"%string].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intros t Hin.
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        simpl in Hin; contradiction.
      * intros t Hin.
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        destruct Hin as [H|Hin]; [subst; simpl; lia|].
        simpl in Hin; contradiction.
Qed.