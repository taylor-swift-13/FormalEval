Require Import Nat.
Require Import List.
Require Import Factorial.
Require Import Lia.
Import ListNotations.

Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).

Definition sum_nat (i : nat) := Nat.div (i * (i + 1)) 2.

Definition f (n : nat) : list nat :=
  map (fun i => if even i then fact i else sum_nat i) (seq 1 n).

Example f_5 : f 5 = [1; 2; 6; 24; 15].
Proof.
  unfold f, sum_nat.
  vm_compute. reflexivity.
Qed.

Example problem_106_test :
  problem_106_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold problem_106_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi Hle.
    destruct i as [|i1]; [lia|].
    destruct i1 as [|i2].
    + (* i = 1 *)
      vm_compute. reflexivity.
    + destruct i2 as [|i3].
      * (* i = 2 *)
        vm_compute. reflexivity.
      * destruct i3 as [|i4].
        -- (* i = 3 *)
           vm_compute. reflexivity.
        -- destruct i4 as [|i5].
           ** (* i = 4 *)
              vm_compute. reflexivity.
           ** (* i >= 6, but i <= 5 by Hle, contradiction *)
              exfalso; lia.
Qed.