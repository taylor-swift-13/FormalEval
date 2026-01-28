Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter val_3 : Any.
Parameter val_c : Any.
Parameter val_a : Any.
Parameter val_b : Any.

Axiom is_int_3 : IsInt val_3 3.
Axiom not_int_c : forall n, ~ IsInt val_c n.
Axiom not_int_a : forall n, ~ IsInt val_a n.
Axiom not_int_b : forall n, ~ IsInt val_b n.

Example test_filter_integers : filter_integers_spec [val_3; val_c; val_3; val_3; val_a; val_b] [3; 3; 3].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 3).
  - exact is_int_3.
  - apply fir_cons_nonint.
    + exact not_int_c.
    + apply fir_cons_int with (n := 3).
      * exact is_int_3.
      * apply fir_cons_int with (n := 3).
        -- exact is_int_3.
        -- apply fir_cons_nonint.
           ++ exact not_int_a.
           ++ apply fir_cons_nonint.
              ** exact not_int_b.
              ** apply fir_nil.
Qed.