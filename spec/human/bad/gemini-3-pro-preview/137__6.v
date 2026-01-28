Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Psatz. (* For lia and lra *)
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* 三种输入类型 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* 判断是否是十进制数字字符 *)
Definition is_digit (c : ascii) : bool :=
  ("0" <=? c)%char && (c <=? "9")%char.

(* 将数字字符转换为其数值（0..9） *)
Definition digit_val (c : ascii) : nat :=
  (nat_of_ascii c - nat_of_ascii "0")%nat.

(* 将一串数字字符转成 nat（按十进制），非数字字符导致 None *)
Fixpoint digits_to_nat (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: tl => if is_digit c then
                 digits_to_nat tl (acc * 10 + digit_val c)%nat
               else None
  end.

(* 判断是否为小数点分隔符 '.' (46) 或 ',' (44) *)
Definition is_sep (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 46 || Nat.eqb (nat_of_ascii c) 44.

(* 在首个分隔符处分割字符列表为整数部分和小数部分 *)
Fixpoint split_on_sep (l : list ascii) : (list ascii * list ascii) :=
  match l with
  | [] => ([], [])
  | c :: tl => if is_sep c then ([], tl)
               else let (pre, suf) := split_on_sep tl in (c :: pre, suf)
  end.

(* 10 的 nat 次幂 (作为 R) *)
Fixpoint pow10 (n : nat) : R :=
  match n with
  | 0%nat => 1%R
  | S n' => 10 * pow10 n'
  end.

(* Helper to convert string to list ascii if not in stdlib version *)
(* Usually available in Coq.Strings.String, but defined here for robustness if needed *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* 解析字符串：可选符号，整数部分（至少一位），可选小数部分 *)
Definition parse_string (s : string) : option (bool * nat * nat * nat) :=
  let l := list_ascii_of_string s in
  match l with
  | [] => None
  | c0 :: tl0 =>
    let (neg, rest) :=
      if Nat.eqb (nat_of_ascii c0) 45 then (true, tl0) (* '-' *)
      else if Nat.eqb (nat_of_ascii c0) 43 then (false, tl0) (* '+' *)
      else (false, l) in
    let (int_chars, frac_chars) := split_on_sep rest in
    match int_chars with
    | [] => None (* 需至少有一位整数数字 *)
    | _ =>
      match digits_to_nat int_chars 0 with
      | None => None
      | Some int_v =>
        match frac_chars with
        | [] => Some (neg, int_v, 0%nat, 0%nat)
        | _ => match digits_to_nat frac_chars 0 with
               | None => None
               | Some frac_v => Some (neg, int_v, frac_v, length frac_chars)
               end
        end
      end
    end
  end.

(* 最终谓词：字符串表示实数 r *)
Definition str_represents (s : string) (r : R) : Prop :=
  match parse_string s with
  | None => False
  | Some (neg, int_v, frac_v, k) =>
      let base := (INR int_v + (if (k =? 0)%nat then 0 else INR frac_v / pow10 k))%R in
      if neg then r = - base else r = base
  end.

Inductive value_of_rel : val -> R -> Prop :=
  | vor_int : forall z, value_of_rel (VInt z) (IZR z)
  | vor_float : forall r, value_of_rel (VFloat r) r
  | vor_str : forall s r, str_represents s r -> value_of_rel (VStr s) r.

Inductive Rlt_bool_rel : R -> R -> bool -> Prop :=
  | rbr_lt : forall x y, Rlt x y -> Rlt_bool_rel x y true
  | rbr_ge : forall x y, ~ Rlt x y -> Rlt_bool_rel x y false.

Definition problem_137_pre (a b : val) : Prop := True.

Definition problem_137_spec (a b : val) (res : option val) : Prop :=
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb true /\
     res = Some b) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel rb ra true /\
     res = Some a) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb false /\
     Rlt_bool_rel rb ra false /\
     res = None).

(* Test case: input = ["5,1"; "6"], output = "6" *)
Example test_problem_137 : problem_137_spec (VStr "5,1") (VStr "6") (Some (VStr "6")).
Proof.
  unfold problem_137_spec.
  left.
  exists (INR 5 + INR 1 / 10)%R, (INR 6)%R.
  split.
  - apply vor_str.
    unfold str_represents.
    replace (parse_string "5,1") with (Some (false, 5%nat, 1%nat, 1%nat)) by reflexivity.
    simpl.
    lra.
  - split.
    + apply vor_str.
      unfold str_represents.
      replace (parse_string "6") with (Some (false, 6%nat, 0%nat, 0%nat)) by reflexivity.
      simpl.
      lra.
    + split.
      * apply rbr_lt.
        lra.
      * reflexivity.
Qed.