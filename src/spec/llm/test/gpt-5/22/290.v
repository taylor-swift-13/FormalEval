Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.
Axiom isint_a1_10 : IsInt a1 10%Z.
Axiom isint_a5_9 : IsInt a5 9%Z.
Axiom isint_a6_9 : IsInt a6 9%Z.
Axiom notint_a2 : forall n, ~ IsInt a2 n.
Axiom notint_a3 : forall n, ~ IsInt a3 n.
Axiom notint_a4 : forall n, ~ IsInt a4 n.
Axiom notint_a7 : forall n, ~ IsInt a7 n.
Axiom notint_a8 : forall n, ~ IsInt a8 n.
Axiom notint_a9 : forall n, ~ IsInt a9 n.
Axiom notint_a10 : forall n, ~ IsInt a10 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [10%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (n := 10%Z).
  - exact isint_a1_10.
  - eapply fir_cons_nonint.
    + exact notint_a2.
    + eapply fir_cons_nonint.
      * exact notint_a3.
      * eapply fir_cons_nonint.
        -- exact notint_a4.
        -- eapply fir_cons_int with (n := 9%Z).
           ++ exact isint_a5_9.
           ++ eapply fir_cons_int with (n := 9%Z).
              ** exact isint_a6_9.
              ** eapply fir_cons_nonint.
                 --- exact notint_a7.
                 --- eapply fir_cons_nonint.
                     +++ exact notint_a8.
                     +++ eapply fir_cons_nonint.
                         **** exact notint_a9.
                         **** eapply fir_cons_nonint.
                              ----- exact notint_a10.
                              ----- apply fir_nil.
Qed.