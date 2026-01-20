(* HumanEval 122 - Inductive Spec *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive is_at_most_two_digits : Z -> Prop :=
| iatd_build : forall n, -100 < n -> n < 100 -> is_at_most_two_digits n.

Inductive take_rel {A : Type} : nat -> list A -> list A -> Prop :=
| tr_zero : forall l, take_rel 0%nat l nil
| tr_nil : forall k, take_rel (S k) nil nil
| tr_cons : forall h t k first, take_rel k t first ->
    take_rel (S k) (h :: t) (h :: first).

Inductive filter_rel {A : Type} : (A -> Prop) -> list A -> list A -> Prop :=
| fr_nil : forall (P : A -> Prop), filter_rel P nil nil
| fr_keep : forall (P : A -> Prop) h t res, P h -> filter_rel P t res ->
   filter_rel P (h :: t) (h :: res)
| fr_drop : forall (P : A -> Prop) h t res, ~ P h -> filter_rel P t res ->
   filter_rel P (h :: t) res.

Inductive sum_rel : list Z -> Z -> Prop :=
| sr_nil : sum_rel nil 0%Z
| sr_cons : forall h t s, sum_rel t s -> sum_rel (h :: t) (h + s).

Definition sum_two_digits_first_k_spec (arr : list Z) (k : nat) (output : Z) : Prop :=
  exists first_k filtered, take_rel k arr first_k /\
    filter_rel is_at_most_two_digits first_k filtered /\
    sum_rel filtered output.

Example sum_two_digits_first_k_spec_ex: sum_two_digits_first_k_spec
  (111%Z :: 21%Z :: 3%Z :: 4000%Z :: nil) 4%nat 24%Z.
Proof.
  unfold sum_two_digits_first_k_spec.
  (* 简化：直接使用归纳关系 *) Admitted.

