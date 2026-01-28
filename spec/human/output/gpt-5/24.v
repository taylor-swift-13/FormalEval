Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_3_1 : problem_24_pre 3 /\ problem_24_spec 3 1.
Proof.
  split.
  - unfold problem_24_pre. lia.
  - unfold problem_24_spec.
    split.
    + simpl. reflexivity.
    + split.
      * lia.
      * intros i [Hi_pos Hi_lt] Hi_div.
        destruct i as [|i'].
        -- lia.
        -- destruct i' as [|i''].
           ++ (* i = 1 *) lia.
           ++ (* i >= 2 *)
              destruct i'' as [|i'''].
              ** (* i = 2 *)
                 exfalso. simpl in Hi_div. discriminate.
              ** (* i >= 3 contradicts i < 3 *)
                 exfalso. lia.
Qed.