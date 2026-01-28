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

(* 判断字符是否是大写字母 *)
Definition is_upper (a: ascii) : bool :=
  let n := nat_of_ascii a in
  (65 <=? n)%nat && (n <=? 90)%nat.

(* 转换大写字符到小写 *)
Definition lower (a: ascii) : ascii :=
  if is_upper a then
    ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* Pre: no additional constraints for `count_distinct_characters` by default *)
Definition problem_16_pre (s : string) : Prop := True.

(* Spec定义 *)
Definition problem_16_spec (s: string) (output: nat) : Prop :=
  exists D: list ascii,
    NoDup D /\

    (* s中每个字符小写版都在D中 *)
    (forall i, i < String.length s -> 
      match String.get i s with
      | Some c => In (lower c) D
      | None => False
      end) /\

    (* D中每个字符都来源于s中某字符的小写版 *)
    (forall d, In d D -> exists i, i < String.length s /\ 
      match String.get i s with
      | Some c => d = lower c
      | None => False
      end) /\

    (* k等于D长度 *)
    output = List.length D.

Example test_case_lhello_wworld : problem_16_spec "lhello wworld" 8.
Proof.
  unfold problem_16_spec.
  exists ["l"; "h"; "e"; "o"; " "; "w"; "r"; "d"]%char.
  split.
  - (* NoDup *)
    repeat (constructor; [ simpl; intro H; repeat (destruct H as [H|H]; [ try discriminate | ]); try contradiction | ]).
    apply NoDup_nil.
  - split.
    + (* Forward *)
      intros i Hi.
      do 13 (destruct i; [ simpl; tauto | ]).
      simpl in Hi. lia.
    + split.
      * (* Backward *)
        intros d Hd.
        simpl in Hd.
        destruct Hd as [H|Hd]; [ subst; exists 0; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 1; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 2; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 5; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 6; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 7; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 10; split; [ simpl; lia | simpl; reflexivity ] | ].
        destruct Hd as [H|Hd]; [ subst; exists 12; split; [ simpl; lia | simpl; reflexivity ] | ].
        inversion Hd.
      * (* Length *)
        reflexivity.
Qed.