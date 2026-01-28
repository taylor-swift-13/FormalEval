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

Parameter val_1 : Any.
Parameter val_8 : Any.
Parameter val_9 : Any.
Parameter val_empty : Any.
Parameter val_list78 : Any.

Axiom is_int_1 : IsInt val_1 1%Z.
Axiom is_int_8 : IsInt val_8 8%Z.
Axiom is_int_9 : IsInt val_9 9%Z.
Axiom not_int_empty : forall n, ~ IsInt val_empty n.
Axiom not_int_list78 : forall n, ~ IsInt val_list78 n.

Example test_filter_integers : 
  filter_integers_spec 
    [val_1; val_empty; val_empty; val_8; val_empty; val_list78; val_9; val_9; val_empty; val_empty; val_list78; val_empty] 
    [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - apply is_int_1.
  - apply fir_cons_nonint.
    + apply not_int_empty.
    + apply fir_cons_nonint.
      * apply not_int_empty.
      * apply fir_cons_int with (n := 8%Z).
        -- apply is_int_8.
        -- apply fir_cons_nonint.
           ++ apply not_int_empty.
           ++ apply fir_cons_nonint.
              ** apply not_int_list78.
              ** apply fir_cons_int with (n := 9%Z).
                 --- apply is_int_9.
                 --- apply fir_cons_int with (n := 9%Z).
                     +++ apply is_int_9.
                     +++ apply fir_cons_nonint.
                         *** apply not_int_empty.
                         *** apply fir_cons_nonint.
                             ---- apply not_int_empty.
                             ---- apply fir_cons_nonint.
                                  ++++ apply not_int_list78.
                                  ++++ apply fir_cons_nonint.
                                       **** apply not_int_empty.
                                       **** apply fir_nil.
Qed.