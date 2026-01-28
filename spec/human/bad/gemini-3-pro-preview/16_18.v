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
Open Scope char_scope.

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

(* Test case: input = "1,2,3... gog!", output = 9 *)
Example test_case_problem_16 : problem_16_spec "1,2,3... gog!" 9.
Proof.
  unfold problem_16_spec.
  (* Distinct characters in "1,2,3... gog!" are '1', ',', '2', '3', '.', ' ', 'g', 'o', '!' *)
  exists ["1"%char; ","%char; "2"%char; "3"%char; "."%char; " "%char; "g"%char; "o"%char; "!"%char].
  split.
  - (* NoDup *)
    repeat (apply NoDup_cons; [ simpl; intro H; repeat destruct H as [H|H]; discriminate | ]).
    apply NoDup_nil.
  - split.
    + (* Forward: s -> D *)
      intros i Hlen.
      (* String length is 13 *)
      do 13 (destruct i as [|i]; [ simpl; tauto | ]).
      simpl in Hlen. lia.
    + split.
      * (* Backward: D -> s *)
        intros d Hin.
        simpl in Hin.
        repeat destruct Hin as [<- | Hin];
        [ exists 0 | exists 1 | exists 2 | exists 4 | exists 5 | exists 8 | exists 9 | exists 10 | exists 12 | contradiction ];
        split; [ simpl; lia | simpl; reflexivity ].
      * (* Output length *)
        simpl. reflexivity.
Qed.