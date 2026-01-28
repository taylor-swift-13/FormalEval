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

Example test_factorize_185193 : factorize_spec 185193 [3; 3; 3; 19; 19; 19].
Proof.
  unfold factorize_spec.
  split.
  - lia.
  - split.
    + repeat (constructor; try lia).
    + split.
      * repeat (apply Forall_cons; [
          unfold is_prime; split; [lia |
            intros d Hrange Hdiv;
            apply Z.mod_divide in Hdiv; [|lia];
            repeat match goal with
            | [ H : ?L <= d < ?R |- False ] =>
                let l := eval compute in L in
                let r := eval compute in R in
                match l with
                | r => lia
                | _ =>
                    let Heq := fresh "Heq" in
                    let Hgt := fresh "Hgt" in
                    assert (Heq: d = l \/ l + 1 <= d < R) by lia;
                    destruct Heq as [? | Hgt];
                    [ subst; vm_compute in Hdiv; discriminate | clear H ]
                end
            end; lia
          ]
        | ]).
        apply Forall_nil.
      * simpl. reflexivity.
Qed.