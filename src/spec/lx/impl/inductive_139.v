(* HumanEval 139 - Inductive Spec *)
Require Import Coq.Lists.List Coq.Init.Nat.
Import ListNotations.

Inductive fact_rel : nat -> nat -> Prop :=
| fr_zero : fact_rel 0%nat 1%nat
| fr_step : forall n f f_prev, fact_rel (n - 1) f_prev -> f = n * f_prev ->
    fact_rel n f.

Inductive seq_from_one_rel : nat -> list nat -> Prop :=
| sfor_zero : seq_from_one_rel 0%nat nil
| sfor_one : seq_from_one_rel 1%nat (1%nat :: nil)
| sfor_step : forall n ns, seq_from_one_rel n ns -> seq_from_one_rel (S n) ((S n) :: ns).

Inductive product_list_rel : list nat -> nat -> Prop :=
| plr_nil : product_list_rel nil 1%nat
| plr_cons : forall h t p p_tail, product_list_rel t p_tail -> p = h * p_tail ->
    product_list_rel (h :: t) p.

Definition brazilian_factorial_spec (n : nat) (output : nat) : Prop :=
  exists nums facts, seq_from_one_rel n nums /\
   (forall i, In i nums -> exists f, fact_rel i f /\ In f facts) /\
   product_list_rel facts output.

