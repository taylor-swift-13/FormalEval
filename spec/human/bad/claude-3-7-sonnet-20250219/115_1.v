Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.Div2.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left Nat.add well 0.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
       let w := count_water well in
       acc + (w + bucket_capacity - 1) / bucket_capacity)
    grid
    0.

Definition problem_115_pre (grid : list (list nat)) (bucket_capacity : nat) : Prop :=
  grid <> [] /\
  bucket_capacity >= 1 /\ bucket_capacity <= 10 /\
  let len_first := length (hd [] grid) in
  len_first >= 1 /\ len_first <= 100 /\
  Forall (fun row => length row = len_first /\ Forall (fun x => x = 0 \/ x = 1) row) grid /\
  length grid >= 1 /\ length grid <= 100.

Definition problem_115_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.

(* Test case input and output *)
Definition input :=
  [[0; 0; 1; 0];
   [0; 1; 0; 0];
   [1; 1; 1; 1]].

Definition bucket_capacity := 1.

Definition output := 6.

Example problem_115_example1 :
  problem_115_spec input bucket_capacity output.
Proof.
  unfold problem_115_spec, required_trips_impl, count_water. simpl.

  (* Calculate water units per well *)
  assert (cw1: fold_left Nat.add [0;0;1;0] 0 = 1).
  { simpl. lia. }
  assert (cw2: fold_left Nat.add [0;1;0;0] 0 = 1).
  { simpl. lia. }
  assert (cw3: fold_left Nat.add [1;1;1;1] 0 = 4).
  { simpl. lia. }

  rewrite cw1 cw2 cw3.

  (* bucket_capacity = 1 *)
  unfold bucket_capacity.

  (* Compute (w + bucket_capacity - 1) / bucket_capacity for each well *)
  assert (t1: (1 + 1 - 1) / 1 = 1).
  { lia. }
  assert (t2: (1 + 1 - 1) / 1 = 1).
  { lia. }
  assert (t3: (4 + 1 - 1) / 1 = 4).
  { lia. }

  rewrite t1 t2 t3.

  (* Sum: 0 + 1 + 1 + 4 = 6 *)
  lia.
Qed.