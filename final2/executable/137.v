(* def compare_one(a, b):
"""
Create a function that takes integers, floats, or strings representing
real numbers, and returns the larger variable in its given variable type.
Return None if the values are equal.
Note: If a real number is represented as a string, the floating point might be . or ,

compare_one(1, 2.5) ➞ 2.5
compare_one(1, "2,3") ➞ "2,3"
compare_one("5,1", "6") ➞ "6"
compare_one("1", 1) ➞ None
""" *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* 三种输入类型 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* 抽象函数：字符串 s 解析为实数 r。
   约定：s 可能使用 "." 或 "," 作为小数点。 *)
Parameter str_to_real : string -> R.

Definition value_of_impl (v : val) : R :=
  match v with
  | VInt z => IZR z
  | VFloat r => r
  | VStr s => str_to_real s
  end.

Definition Rlt_bool (x y : R) : bool :=
  match Rlt_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition compare_one_impl (a b : val) : option val :=
  let ra := value_of_impl a in
  let rb := value_of_impl b in
  if Rlt_bool ra rb then Some b
  else if Rlt_bool rb ra then Some a
  else None.

Definition compare_one_spec (a b : val) (res : option val) : Prop :=
  res = compare_one_impl a b.
Print IZR.
Print IPR.