Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.PeanoNat Coq.ZArith.ZArith.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left Nat.add well 0%nat.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let w := count_water well in
      acc + (w + bucket_capacity - 1%nat) / bucket_capacity)
    grid
    0%nat.

(* grid 非空；所有行长度一致且在 [1,100]；元素为 0 或 1；容量在 [1,10] *)
Definition problem_115_pre (grid : list (list nat)) (bucket_capacity : nat) : Prop :=
  grid <> [] /\
  bucket_capacity >= 1 /\ bucket_capacity <= 10 /\
  let len_first := length (hd [] grid) in
  len_first >= 1 /\ len_first <= 100 /\
  Forall (fun row => length row = len_first /\ Forall (fun x => x = 0 \/ x = 1) row) grid /\
  length grid >= 1 /\ length grid <= 100.
  
Definition problem_115_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.

Lemma required_trips_impl_example_val :
  required_trips_impl [[0;0;1;0]; [0;1;0;0]; [1;1;1;1]] 1%nat = 6%nat.
Proof.
  unfold required_trips_impl.
  simpl.
  replace (count_water [0; 0; 1; 0]) with 1%nat by (unfold count_water; simpl; reflexivity).
  simpl.
  replace (count_water [0; 1; 0; 0]) with 1%nat by (unfold count_water; simpl; reflexivity).
  simpl.
  replace (count_water [1; 1; 1; 1]) with 4%nat by (unfold count_water; simpl; reflexivity).
  simpl.
  reflexivity.
Qed.

Example problem_115_example_spec :
  problem_115_spec [[0;0;1;0]; [0;1;0;0]; [1;1;1;1]] 1%nat 6%nat.
Proof.
  unfold problem_115_spec.
  rewrite required_trips_impl_example_val.
  reflexivity.
Qed.

Example test_case_Z :
  Z.of_nat (required_trips_impl
              (map (map Z.to_nat)
                   [[0%Z; 0%Z; 1%Z; 0%Z];
                    [0%Z; 1%Z; 0%Z; 0%Z];
                    [1%Z; 1%Z; 1%Z; 1%Z]])
              (Z.to_nat 1%Z)) = 6%Z.
Proof.
  simpl.
  rewrite required_trips_impl_example_val.
  simpl.
  reflexivity.
Qed.