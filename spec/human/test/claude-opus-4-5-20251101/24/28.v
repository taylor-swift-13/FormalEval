Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output 是 input 的一个因数 *)
  input mod output = 0 /\

  (* 2. output 严格小于 input *)
  output < input /\

  (* 3. 对于任何严格小于 input 的正因数 i, i 都小于等于 output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_test : problem_24_spec 99 33.
Proof.
  unfold problem_24_spec.
  split.
  - (* 99 mod 33 = 0 *)
    simpl. reflexivity.
  - split.
    + (* 33 < 99 *)
      lia.
    + (* forall i, 0 < i /\ i < 99 -> 99 mod i = 0 -> i <= 33 *)
      intros i [Hi_pos Hi_lt] Hi_div.
      assert (i = 1 \/ i = 3 \/ i = 9 \/ i = 11 \/ i = 33 \/ 
              (i <> 1 /\ i <> 3 /\ i <> 9 /\ i <> 11 /\ i <> 33)) as Hi_cases by lia.
      destruct Hi_cases as [Hi_eq1 | [Hi_eq3 | [Hi_eq9 | [Hi_eq11 | [Hi_eq33 | Hi_other]]]]].
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * destruct Hi_other as [Hne1 [Hne3 [Hne9 [Hne11 Hne33]]]].
        assert (i <= 33 \/ i > 33) as Hcmp by lia.
        destruct Hcmp as [Hle | Hgt].
        -- lia.
        -- assert (i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/ 
                  i = 40 \/ i = 41 \/ i = 42 \/ i = 43 \/ i = 44 \/ i = 45 \/ 
                  i = 46 \/ i = 47 \/ i = 48 \/ i = 49 \/ i = 50 \/ i = 51 \/ 
                  i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ 
                  i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63 \/ 
                  i = 64 \/ i = 65 \/ i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ 
                  i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/ 
                  i = 76 \/ i = 77 \/ i = 78 \/ i = 79 \/ i = 80 \/ i = 81 \/ 
                  i = 82 \/ i = 83 \/ i = 84 \/ i = 85 \/ i = 86 \/ i = 87 \/ 
                  i = 88 \/ i = 89 \/ i = 90 \/ i = 91 \/ i = 92 \/ i = 93 \/ 
                  i = 94 \/ i = 95 \/ i = 96 \/ i = 97 \/ i = 98) as Hrange by lia.
           repeat (destruct Hrange as [Heq | Hrange]; [subst i; simpl in Hi_div; discriminate | ]).
           subst i. simpl in Hi_div. discriminate.
Qed.