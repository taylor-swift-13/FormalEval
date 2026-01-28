Require Import Arith.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_10_5 : problem_24_pre 10 /\ problem_24_spec 10 5.
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
           ++ lia.
           ++ destruct i'' as [|i'''].
              ** lia.
              ** destruct i''' as [|i''''].
                 --- exfalso. simpl in Hi_div. discriminate.
                 --- destruct i'''' as [|i'''''].
                     **** exfalso. simpl in Hi_div. discriminate.
                     **** destruct i''''' as [|i'''''' ].
                          ***** lia.
                          ***** destruct i'''''' as [|i'''''''].
                                ****** exfalso. simpl in Hi_div. discriminate.
                                ****** destruct i''''''' as [|i''''''''].
                                       ******* exfalso. simpl in Hi_div. discriminate.
                                       ******* destruct i'''''''' as [|i''''''''' ].
                                               ******** exfalso. simpl in Hi_div. discriminate.
                                               ******** destruct i''''''''' as [|i'''''''''' ].
                                                        ********* exfalso. simpl in Hi_div. discriminate.
                                                        ********* exfalso. lia.
Qed.