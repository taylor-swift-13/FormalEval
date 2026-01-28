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

Example test_count_distinct_CdE : count_distinct_characters_spec "CdE" 3.
Proof.
  unfold count_distinct_characters_spec.
  simpl.
  exists [ascii_of_nat 99; ascii_of_nat 100; ascii_of_nat 101].
  split.
  - apply NoDup_cons.
    + intro H. simpl in H. destruct H as [H | [H | []]]; inversion H.
    + apply NoDup_cons.
      * intro H. simpl in H. destruct H as [H | []]; inversion H.
      * apply NoDup_cons.
        -- simpl. auto.
        -- apply NoDup_nil.
  - split.
    + intros x. split; intro H; apply H.
    + reflexivity.
Qed.