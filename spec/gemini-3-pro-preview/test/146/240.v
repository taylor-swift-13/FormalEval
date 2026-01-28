Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint rev_nat (n acc fuel : nat) : nat :=
  match fuel with
  | 0%nat => acc
  | S f =>
    match n with
    | 0%nat => acc
    | _ => rev_nat (Nat.div n 10) (acc * 10 + (Nat.modulo n 10))%nat f
    end
  end.

Definition is_palindrome_nat (n : nat) : bool :=
  Nat.eqb n (rev_nat n 0 n).

Definition check (z : Z) : bool :=
  match z with
  | Zpos p => 
      let n := Pos.to_nat p in
      (Nat.leb 10 n) && (is_palindrome_nat n)
  | _ => false
  end.

Definition solve (l : list Z) : Z :=
  Z.of_nat (length (filter check l)).

Example test_case: solve [120; 121; 414; 214; 357; 8518; 21517; 2123; 918; 2123; 21517; 214] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.