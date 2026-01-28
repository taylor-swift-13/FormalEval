Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Arith.
Require Import PeanoNat.

Open Scope string_scope.
Open Scope nat_scope.

Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (forall i, In i indices -> match_at i input substring) /\
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    output = List.length indices.

Lemma test_case: problem_18_spec "" "x" 0.
Proof.
  unfold problem_18_spec.
  exists nil.
  split. 
  - constructor.
  - split.
    + intros i H. destruct H.
    + split.
      * intros i Hlen Hmatch.
        unfold match_at in Hmatch.
        destruct Hmatch as [Hlen_sub [Hbound _]].
        simpl in Hbound.
        simpl in Hlen.
        assert (String.length "x" > 0) by (simpl; apply Nat.lt_0_succ).
        contradiction.
      * reflexivity.
Qed.