Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  2 <= p /\ forall d, 2 <= d < p -> ~ Z.divide d p.

Fixpoint list_prod (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: xs => x * list_prod xs
  end.

Definition factorize_spec (n : Z) (fact : list Z) : Prop :=
  1 <= n /\ Sorted Z.le fact /\ Forall is_prime fact /\ list_prod fact = n.

Ltac solve_prime p :=
  unfold is_prime; split; [lia |
    intros d [Hmin Hmax] Hdiv;
    apply Z.mod_divide in Hdiv; [|lia];
    let rec loop i :=
      match eval compute in (Z.ltb i p) with
      | true =>
          destruct (Z.eq_dec d i) as [->|];
          [ vm_compute in Hdiv; discriminate
          | loop (Z.succ i) ]
      | false => idtac
      end
    in loop 2;
    lia
  ].

Example test_factorize_1023 : factorize_spec 1023 [3; 11; 31].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil); lia.
    + split.
      * apply Forall_cons. solve_prime 3.
        apply Forall_cons. solve_prime 11.
        apply Forall_cons. solve_prime 31.
        apply Forall_nil.
      * simpl. reflexivity.
Qed.