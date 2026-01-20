Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter v_non1 v_non2 v_int3 v_int4 : Any.
Parameter eight : int.
Notation "8%Z" := eight.
Axiom v_non1_nonint : forall n, ~ IsInt v_non1 n.
Axiom v_non2_nonint : forall n, ~ IsInt v_non2 n.
Axiom v_int3_is_eight : IsInt v_int3 eight.
Axiom v_int4_is_eight : IsInt v_int4 eight.

Example test_case_nested_lists_and_ints: filter_integers_spec [v_non1; v_non2; v_int3; v_int4] [8%Z; 8%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v_non1_nonint.
  - eapply fir_cons_nonint.
    + exact v_non2_nonint.
    + eapply fir_cons_int.
      * exact v_int3_is_eight.
      * eapply fir_cons_int.
        -- exact v_int4_is_eight.
        -- constructor.
Qed.