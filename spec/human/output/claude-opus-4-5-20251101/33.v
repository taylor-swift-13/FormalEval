Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Pre: no additional constraints for `sort_third` by default *)
Definition problem_33_pre (input : list Z) : Prop := True.

(* Spec 的定义 *)
Definition problem_33_spec (input output : list Z) : Prop :=
  (* 1. input 是 output 的排列 (Permutation) *)
  Permutation input output /\

  (* 2. 如果索引 i 不能被 3 整除，则 output[i] 必须等于 input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. output 中所有索引能被 3 整除的元素，必须是按索引顺序排好序的 (非递减) *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_33_test1 :
  problem_33_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold problem_33_spec.
  split.
  - (* Permutation *)
    apply Permutation_refl.
  - split.
    + (* Non-divisible by 3 indices preserved *)
      intros i Hi Hmod.
      reflexivity.
    + (* Sorted at indices divisible by 3 *)
      intros i j [Hij1 [Hij2 [Hij3 [Hij4 Hij5]]]].
      simpl in *.
      (* The only index divisible by 3 in range [0,3) is 0 *)
      (* If i mod 3 = 0 and j mod 3 = 0 and i < j < 3, then i = 0 and j must be >= 3, contradiction *)
      destruct i.
      * (* i = 0 *)
        destruct j.
        -- (* j = 0, but i < j is false *)
           lia.
        -- (* j = S j' *)
           destruct j.
           ++ (* j = 1, 1 mod 3 = 1 <> 0 *)
              simpl in Hij4. lia.
           ++ destruct j.
              ** (* j = 2, 2 mod 3 = 2 <> 0 *)
                 simpl in Hij4. lia.
              ** (* j >= 3, but length is 3, so j < 3, contradiction *)
                 simpl in Hij2. lia.
      * (* i = S i' *)
        destruct i.
        -- (* i = 1, 1 mod 3 = 1 <> 0 *)
           simpl in Hij3. lia.
        -- destruct i.
           ++ (* i = 2, 2 mod 3 = 2 <> 0 *)
              simpl in Hij3. lia.
           ++ (* i >= 3, but length is 3, so i < 3, contradiction *)
              simpl in Hij1. lia.
Qed.