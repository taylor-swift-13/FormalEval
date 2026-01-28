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

Example test_count_distinct_complex : count_distinct_characters_spec "hellr1,2,3... go!o world" 15.
Proof.
  unfold count_distinct_characters_spec.
  exists ["h"; "e"; "l"; "r"; "1"; ","; "2"; "3"; "."; " "; "g"; "o"; "!"; "w"; "d"]%char.
  split.
  - repeat constructor; intro H; simpl in H; repeat (destruct H as [H | H]; [ inversion H | ]); contradiction.
  - split.
    + intros x.
      compute.
      split; intro H.
      * repeat (destruct H as [H | H]; [ rewrite <- H; auto 50 | ]); contradiction.
      * repeat (destruct H as [H | H]; [ rewrite <- H; auto 50 | ]); contradiction.
    + reflexivity.
Qed.