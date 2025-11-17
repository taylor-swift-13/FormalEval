(* def encode_cyclic(s: str):
"""
returns encoded string by cycling groups of three characters.
"""

def decode_cyclic(s: str):
"""
takes as input string encoded with encode_cyclic function. Returns decoded string.
"""
*)

(* 
  Spec(input ：string, output : string) :=

​	∃n， n = (length(input) / 3) *3 -1  /\
​		(∀i ∈ [0, length(input)),   i+1 % 3 = 0  → i ≤ n) /\
​		(∀i ∈ [0, n], i+1 % 3 = 2 → output[i] = input[i-1] /\ 
​							  i+1 % 3 = 1 → output[i] = input[i+2] /\ 
​							  i+1 % 3 =0 → output[i] = input[i-1]) /\
​		(∀i ∈ (n, length(input)), output[i] = input[i]) *)


Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.

(* 为了使用 nth 函数，我们需要一个默认的 ascii 字符 *)
Definition default_ascii : ascii := " "%char.

(* Pre: no additional constraints for `encode/decode_cyclic` by default *)
Definition Pre (input : list ascii) : Prop := True.

Definition Spec_logic (input output : list ascii) : Prop :=
  (* 1. 基础约束：长度相等 *)
  length input = length output /\
  (
    (* 2. 定义常量 *)
    let n := ((length input / 3) * 3 - 1)%nat in
    let L := length input in

    (* 3. 对于所有索引 i，必须满足以下由逻辑连接词构成的断言 *)
    forall i, (i < L)%nat ->
      let out_char := nth i output default_ascii in
      (
        (* 情况一: i <= n *)
        ( (i <= n)%nat /\
          (
            (* 子情况 1: (i+1)%3 = 1 *)
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = nth (i + 2) input default_ascii) ) \/

            (* 子情况 2: (i+1)%3 = 2 或 0 *)
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = nth (i - 1) input default_ascii) )
          )
        ) \/

        (* 情况二: i > n (等价于 not (i <= n)) *)
        ( (~(i <= n)%nat) /\
          (
            out_char = nth i input default_ascii
          )
        )
      )
  ).

