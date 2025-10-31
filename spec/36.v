(* Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
>>> fizz_buzz(50)
0
>>> fizz_buzz(78)
2
>>> fizz_buzz(79)
3 *)

(* Spec(input : int, output : int) :=
  outout = $∑_{x=0}^{input-1}$ (if DivBy11Or13(x) then Num7sIn(x) else 0) *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.


Fixpoint count_digit_7_aux (k : nat) (fuel : nat) {struct fuel} : nat :=
  match fuel with
  | 0 => 0 (* 如果燃料耗尽，停止 *)
  | S fuel' =>
      match k with
      | 0 => 0 (* 如果数字本身是0，停止 *)
      | _ => (if Nat.eqb (k mod 10) 7 then 1 else 0) + count_digit_7_aux (k / 10) fuel'
      end
  end.

(*
  现在定义用户真正调用的函数。
  我们提供 k 本身作为初始燃料，这足以保证计算能够完成。
*)
Definition count_digit_7 (k : nat) : nat :=
  count_digit_7_aux k k.


Definition fizz_buzz_spec (n : nat) (result : nat) : Prop :=
  result =
  List.fold_left
    (fun accumulator i =>
       accumulator + if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
                       count_digit_7 i
                     else
                       0)
    (List.seq 0 n)
    0.