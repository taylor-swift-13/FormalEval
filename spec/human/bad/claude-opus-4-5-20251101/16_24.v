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

Example test_hello_world : problem_16_spec "hello wThe quick brown fox jumps over the lazy doAbCdEfGgorld" 27.
Proof.
  unfold problem_16_spec.
  exists [
    "h"%char; "e"%char; "l"%char; "o"%char; " "%char; "w"%char; "t"%char;
    "q"%char; "u"%char; "i"%char; "c"%char; "k"%char; "b"%char; "r"%char;
    "n"%char; "f"%char; "x"%char; "j"%char; "m"%char; "p"%char; "s"%char;
    "v"%char; "y"%char; "z"%char; "d"%char; "a"%char; "g"%char
  ].
  split.
  - repeat (constructor; [simpl; intuition; try discriminate | ]).
    constructor.
  - split.
    + intros i H.
      do 61 (destruct i; [simpl; auto 30 | ]).
      simpl in H. lia.
    + split.
      * intros d H.
        simpl in H.
        repeat (destruct H as [H | H]; [subst; eexists; split; [simpl; lia | simpl; reflexivity] | ]).
        destruct H.
      * reflexivity.
Qed.