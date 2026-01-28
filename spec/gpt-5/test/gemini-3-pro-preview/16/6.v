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

Example test_count_distinct_abcdefg : count_distinct_characters_spec "AbCdEfG" 7.
Proof.
  unfold count_distinct_characters_spec.
  simpl.
  exists ["a"; "b"; "c"; "d"; "e"; "f"; "g"]%char.
  split.
  - repeat constructor; simpl; intro H; 
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H; [ discriminate | ]
    end;
    contradiction.
  - split.
    + intros x. reflexivity.
    + reflexivity.
Qed.