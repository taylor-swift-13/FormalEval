Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter v_list4 : Any.
Parameter v5 : Any.
Parameter v8 : Any.
Axiom NonInt_v_list4 : forall n, ~ IsInt v_list4 n.
Axiom IsInt_v5 : IsInt v5 (5%Z).
Axiom IsInt_v8 : IsInt v8 (8%Z).

Example test_case_nested: filter_integers_spec [v_list4; v5; v8; v_list4] [5%Z; 8%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact NonInt_v_list4.
  - eapply fir_cons_int.
    + exact IsInt_v5.
    + eapply fir_cons_int.
      * exact IsInt_v8.
      * eapply fir_cons_nonint.
        -- exact NonInt_v_list4.
        -- apply fir_nil.
Qed.