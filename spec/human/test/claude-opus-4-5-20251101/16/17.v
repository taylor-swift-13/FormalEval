Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope nat_scope.
Open Scope string_scope.

Definition is_upper (a: ascii) : bool :=
  let n := nat_of_ascii a in
  (65 <=? n)%nat && (n <=? 90)%nat.

Definition lower (a: ascii) : ascii :=
  if is_upper a then
    ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition problem_16_pre (s : string) : Prop := True.

Definition problem_16_spec (s: string) (output: nat) : Prop :=
  exists D: list ascii,
    NoDup D /\

    (forall i, i < String.length s -> 
      match String.get i s with
      | Some c => In (lower c) D
      | None => False
      end) /\

    (forall d, In d D -> exists i, i < String.length s /\ 
      match String.get i s with
      | Some c => d = lower c
      | None => False
      end) /\

    output = List.length D.

Example test_hellold : problem_16_spec "hellold" 5.
Proof.
  unfold problem_16_spec.
  exists ["h"%char; "e"%char; "l"%char; "o"%char; "d"%char].
  split.
  - repeat constructor; simpl; intuition; discriminate.
  - split.
    + intros i H.
      simpl in H.
      destruct i; simpl; try (left; reflexivity).
      destruct i; simpl; try (right; left; reflexivity).
      destruct i; simpl; try (right; right; left; reflexivity).
      destruct i; simpl; try (right; right; left; reflexivity).
      destruct i; simpl; try (right; right; right; left; reflexivity).
      destruct i; simpl; try (right; right; left; reflexivity).
      destruct i; simpl; try (right; right; right; right; left; reflexivity).
      lia.
    + split.
      * intros d H.
        simpl in H.
        destruct H as [H | [H | [H | [H | [H | H]]]]].
        -- exists 0. split. simpl. lia. simpl. rewrite <- H. reflexivity.
        -- exists 1. split. simpl. lia. simpl. rewrite <- H. reflexivity.
        -- exists 2. split. simpl. lia. simpl. rewrite <- H. reflexivity.
        -- exists 4. split. simpl. lia. simpl. rewrite <- H. reflexivity.
        -- exists 6. split. simpl. lia. simpl. rewrite <- H. reflexivity.
        -- contradiction.
      * reflexivity.
Qed.