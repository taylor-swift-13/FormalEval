Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope nat_scope.

Definition is_upper (a: ascii) : bool :=
  let n := nat_of_ascii a in
  (65 <=? n) && (n <=? 90).

Definition lower (a: ascii) : ascii :=
  if is_upper a then
    ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition Spec (s: list ascii) (output: nat) : Prop :=
  exists D: list ascii,
    NoDup D /\
    (forall i, i < length s -> In (lower (nth i s " "%char)) D) /\
    (forall d, In d D -> exists i, i < length s /\ d = lower (nth i s " "%char)) /\
    output = length D.

Example test_count_distinct_characters_empty :
  Spec [] 0.
Proof.
  unfold Spec.
  exists [].
  split.
  - constructor.
  - split.
    + intros i H.
      simpl in H.
      lia.
    + split.
      * intros d H.
        contradiction.
      * simpl.
        reflexivity.
Qed.