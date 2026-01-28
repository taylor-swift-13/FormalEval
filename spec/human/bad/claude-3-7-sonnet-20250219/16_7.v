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

Example test_problem_16_banana : problem_16_spec "banana" 3.
Proof.
  unfold problem_16_spec.
  exists [ "b"%char; "a"%char; "n"%char ].
  split.
  - (* NoDup *)
    repeat constructor.
  - split.
    + intros i H.
      rewrite String.length_correct in H.
      assert (Hlen: String.length "banana" = 6) by reflexivity; rewrite Hlen in H.
      specialize (String.get i "banana") as get_i.
      simpl in get_i.
      destruct (lt_eq_lt_dec i 6) as [[Hlt|Heq]|Hgt]; try lia; try contradiction.
      clear Hgt Heq.
      destruct i; simpl.
      * (* i=0, char 'b' *)
        simpl.
        rewrite String.get_char.
        simpl.
        left. reflexivity.
      * destruct i; simpl.
        -- (* i=1, char 'a' *)
           simpl.
           right; left. reflexivity.
        -- destruct i; simpl.
           ++ (* i=2, char 'n' *)
              right; right; left. reflexivity.
           ++ destruct i; simpl.
              ** (* i=3, char 'a' *)
                 right; left. reflexivity.
              ** destruct i; simpl.
                 --- (* i=4, char 'n' *)
                     right; right; left. reflexivity.
                 --- destruct i; simpl.
                     +++ (* i=5, char 'a' *)
                         right; left. reflexivity.
                     +++ lia.
    + split.
      * intros d HIn.
        destruct HIn as [HIn | [HIn | [HIn | HFalse]]]; try contradiction.
        -- exists 0%nat. split; [lia|]. simpl. reflexivity.
        -- exists 1%nat. split; [lia|]. simpl. reflexivity.
        -- exists 2%nat. split; [lia|]. simpl. reflexivity.
      * simpl. reflexivity.
Qed.