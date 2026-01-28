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

Example test_count_distinct_complex : 
  count_distinct_characters_spec "Cd1,2,3hellhelhellol.dloldold.hel,lold.. 2gog!E" 14.
Proof.
  unfold count_distinct_characters_spec.
  exists ["c"%char; "d"%char; "1"%char; ","%char; "2"%char; "3"%char; "h"%char; "e"%char; "l"%char; "o"%char; "."%char; " "%char; "g"%char; "!"%char].
  split.
  - repeat constructor; simpl; try (intro H; intuition; discriminate).
  - split.
    + intros x.
      let e := eval vm_compute in (map ascii_lower (list_of_string "Cd1,2,3hellhelhellol.dloldold.hel,lold.. 2gog!E")) in
      change (map ascii_lower (list_of_string "Cd1,2,3hellhelhellol.dloldold.hel,lold.. 2gog!E")) with e.
      split; intro H;
      repeat match goal with
      | [ H : In _ (_ :: _) |- _ ] => destruct H as [H | H]; [subst; simpl; tauto | ]
      | [ H : In _ [] |- _ ] => contradiction
      end.
    + reflexivity.
Qed.