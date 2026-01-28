Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
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

Lemma test_case_single_char_different_cases : problem_16_spec "aaaaAAAAaaaa" 1.
Proof.
  unfold problem_16_spec.
  exists [lower "a"%char].
  split.
  - apply NoDup_cons.
    + apply NoDup_singleton.
    + discriminate.
  - split.
    + intros i H.
      simpl in H.
      destruct i.
      * simpl.
        unfold lower.
        destruct (is_upper "a"%char).
        -- simpl.
           rewrite Nat.add_1_r.
           reflexivity.
        -- simpl.
           reflexivity.
      * intros d H_in.
        simpl in H_in.
        destruct H_in.
        -- subst d.
           simpl.
           unfold lower.
           destruct (is_upper "a"%char).
           ++ simpl.
              rewrite Nat.add_1_r.
              reflexivity.
           ++ simpl.
              reflexivity.
        -- contradiction.
  - split.
    + intros d H_in.
      destruct H_in.
      * exists 0.
        split.
        -- simpl.
           rewrite Nat.ltb_lt in H_in.
           lia.
        -- reflexivity.
      * contradiction.
  - reflexivity.
Qed.