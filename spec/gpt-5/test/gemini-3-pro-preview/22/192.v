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

Parameter Any_nil : Any.
Parameter Any_8 : Any.
Axiom IsInt_Any_8 : IsInt Any_8 8.
Axiom Not_IsInt_Any_nil : forall n, ~ IsInt Any_nil n.

Example test_filter_integers_mixed : filter_integers_spec [Any_nil; Any_nil; Any_8; Any_8] [8; 8].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply Not_IsInt_Any_nil.
  - apply fir_cons_nonint.
    + apply Not_IsInt_Any_nil.
    + apply fir_cons_int with (n := 8).
      * apply IsInt_Any_8.
      * apply fir_cons_int with (n := 8).
        -- apply IsInt_Any_8.
        -- apply fir_nil.
Qed.