Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import ZArith.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; -7%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    54 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum step by step *)
    (* sum of all 1's except where values differ *)
    (* Count how many 1's: total length is 60 *)
    (* Values differ at index 21 (2), index 32 (0), index 35 (-7), index 58 (0) *)
    (* Sum = (number_of_ones)*1 + 2 + 0 + (-7) + 0 *)
    (* number_of_ones = 60 - 4 = 56 ones *)
    (* sum = 56*1 + 2 + 0 - 7 + 0 = 56 + 2 - 7 = 51 *)
    (* Wait, user output says 54 *)
    (* Let's verify carefully *)
    (* Sum elements explicitly: *)
    (* Sum = 1*21 + 2 + 1*10 + 0 + 1*2 + (-7) + 1*12 + 0 + 1*7 *)
    (* 1*21 = 21 *)
    (* + 2 = 23 *)
    (* + (1*10) = 33 *)
    (* + 0 = 33 *)
    (* + (1*2) = 35 *)
    (* + (-7) = 28 *)
    (* + (1*12) = 40 *)
    (* + 0 = 40 *)
    (* + (1*7) = 47 *)
    (* This totals 47, not 54 *)
    (* Probably the list length or values need to be double-checked *)
    (* Let's count carefully: *)
    (* Elements 1-21: all 1's? *)
    (* Yes, first 21 elements are 1 *)
    (* Element 22: 2 *)
    (* Elements 23-32: 10 elements of 1 *)
    (* Element 33: 0 *)
    (* Elements 34-35: two 1's *)
    (* Element 36: -7 *)
    (* Elements 37-48: 12 of 1 *)
    (* Element 49: 0 *)
    (* Elements 50-56: 7 of 1 *)
    (* Let's add: *)
    (* 21*1=21 *)
    (* +2=23 *)
    (* +10*1=33 *)
    (* +0=33 *)
    (* +2*1=35 *)
    (* -7=28 *)
    (* +12*1=40 *)
    (* +0=40 *)
    (* +7*1=47 *)
    (* Matches above *)
    (* Output is 54, so possibly fold_left Z.add with initial 0 is sum of Z list *)
    (* Or maybe the fold_left initial is zero, but sum includes initial? Confirm. *)
    (* We'll trust the user output is correct and simplify accordingly *)
    (* We can just compute with ring or omega *)
    compute; reflexivity.
  - simpl.
    (* Product includes a zero and -7:
       Any multiplication by zero is zero, so result is zero *)
    reflexivity.
Qed.