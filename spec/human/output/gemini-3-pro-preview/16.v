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

(* Test case: input = "", output = 0 *)
Example test_case_empty_string : problem_16_spec "" 0.
Proof.
  unfold problem_16_spec.
  (* For an empty string, the set of distinct characters D is empty *)
  exists [].
  
  (* We use explicit splits to handle the conjunctions safely *)
  split.
  - (* 1. NoDup [] *)
    apply NoDup_nil.
  - split.
    + (* 2. Forward condition: s characters in D *)
      intros i Hlen.
      simpl in Hlen.
      (* length "" is 0, so i < 0 is impossible *)
      lia.
    + split.
      * (* 3. Backward condition: D characters from s *)
        intros d Hin.
        (* In d [] is impossible *)
        inversion Hin.
      * (* 4. output = length D *)
        simpl.
        reflexivity.
Qed.