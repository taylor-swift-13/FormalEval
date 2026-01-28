Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
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

Example example_0 :
  problem_16_spec "banana" 3.
Proof.
  unfold problem_16_spec.
  exists [ascii_of_nat 97; ascii_of_nat 98; ascii_of_nat 110].
  split.
  - repeat constructor; unfold not; intros; inversion H; subst; inversion H1.
  - split.
    + intros i Hi. 
      destruct i; simpl.
      * left. reflexivity.
      * destruct i; simpl.
        -- right. left. reflexivity.
        -- destruct i; simpl.
           ++ left. reflexivity.
           ++ destruct i; simpl.
              ** right. left. reflexivity.
              ** destruct i; simpl.
                 --- right. right. left. reflexivity.
                 --- apply Nat.nlt_0_r in Hi. contradiction.
    + split.
      * intros d Hin. 
        repeat (destruct Hin as [Hin | Hin]; [exists 0; simpl; auto |]).
        repeat (destruct Hin as [Hin | Hin]; [exists 1; simpl; auto |]).
        repeat (destruct Hin as [Hin | Hin]; [exists 2; simpl; auto |]).
        repeat (destruct Hin as [Hin | Hin]; [exists 3; simpl; auto |]).
        repeat (destruct Hin as [Hin | Hin]; [exists 4; simpl; auto |]).
        exists 5; simpl; auto.
      * reflexivity.
Qed.