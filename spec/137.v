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
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* 三种输入类型 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* 抽象谓词：字符串 s 能表示实数 r。
   约定：s 可能使用 "." 或 "," 作为小数点；该谓词在实现时需给出具体解析规则。
   在 Spec 中我们把它当作一个原子谓词（axiom-like）使用。 *)
Parameter str_represents : string -> R -> Prop.

(* 把 val 映射到对应的实数值（对字符串使用 str_represents） *)
Inductive value_of : val -> R -> Prop :=
| VO_int   : forall z, value_of (VInt z) (IZR z)
| VO_float : forall r, value_of (VFloat r) r
| VO_str   : forall s r, str_represents s r -> value_of (VStr s) r.

(* 最终 Spec：
   对输入 a, b 和输出 res（option val）成立当且仅当：
     存在 ra, rb 使 a 映射为 ra，b 映射为 rb，并且：
       - 若 ra = rb 则 res = None；
       - 若 ra < rb 则 res = Some b ;
       - 若 rb < ra 则 res = Some a. *)
Definition compare_one_spec (a b : val) (res : option val) : Prop :=
  exists ra rb,
    value_of a ra /\
    value_of b rb /\
    (
      (ra = rb /\ res = None) \/
      (ra < rb /\ res = Some b) \/
      (rb < ra /\ res = Some a)
    ).
Print IZR.
Print IPR.