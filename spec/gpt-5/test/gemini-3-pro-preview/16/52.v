Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition ascii_lower (a : ascii) : ascii :=
  let n := nat_of_ascii a in
  if (65 <=? n) && (n <=? 90) then ascii_of_nat (n + 32) else a.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a t => a :: list_of_string t
  end.

Definition count_distinct_characters_spec (s : string) (n : nat) : Prop :=
  let L := map ascii_lower (list_of_string s) in
  exists U : list ascii,
    NoDup U /\ (forall x, In x U <-> In x L) /\ length U = n.

Example test_count_distinct_complex : count_distinct_characters_spec "hello wo1,2,3 gog!rld" 14.
Proof.
  unfold count_distinct_characters_spec.
  exists (list_of_string "helo w1,23g!rd").
  split.
  - repeat constructor; simpl; intro H; repeat (destruct H as [H | H]; [ congruence | ]); contradiction.
  - split.
    + intros x. simpl. split; intro H.
      * repeat (destruct H as [H | H]; [ subst; simpl; tauto | ]); contradiction.
      * repeat (destruct H as [H | H]; [ subst; simpl; tauto | ]); contradiction.
    + reflexivity.
Qed.