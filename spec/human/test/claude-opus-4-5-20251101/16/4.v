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

Example test_aaaaAAAAaaaa : problem_16_spec "aaaaAAAAaaaa" 1.
Proof.
  unfold problem_16_spec.
  exists ["a"%char].
  split.
  - constructor.
    + simpl. tauto.
    + constructor.
  - split.
    + intros i H.
      simpl in H.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
      destruct H0 as [H0|[H0|[H0|[H0|[H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]]]]]];
      subst i; simpl; left; reflexivity.
    + split.
      * intros d H.
        simpl in H.
        destruct H as [H|H].
        -- subst d.
           exists 0.
           split.
           ++ simpl. lia.
           ++ simpl. reflexivity.
        -- contradiction.
      * reflexivity.
Qed.