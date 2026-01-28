Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (res : list nat) : Prop :=
  let lo := Nat.min a b in
  let hi := Nat.min (Nat.max a b) 9 in
  res =
    (if Nat.leb lo hi then
       List.filter (fun i => Nat.even i) (List.seq lo (S (Nat.sub hi lo)))
     else
       nil).

Example test_generate_integers : generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  (* Simplify the expression. This will compute Nat.min, Nat.max, 
     generate the sequence with List.seq, and filter it with Nat.even. *)
  simpl.
  (* The simplified goal is [2; 4; 6; 8] = [2; 4; 6; 8], which is reflexively true. *)
  reflexivity.
Qed.