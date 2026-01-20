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

Parameter zero : int.
Notation "0%Z" := zero.

Parameters a0 s2 s22 obj l123 l123' l4 l4' : Any.

Axiom a0_is_int : IsInt a0 0%Z.
Axiom s2_not_int : forall n, ~ IsInt s2 n.
Axiom s22_not_int : forall n, ~ IsInt s22 n.
Axiom obj_not_int : forall n, ~ IsInt obj n.
Axiom l123_not_int : forall n, ~ IsInt l123 n.
Axiom l123'_not_int : forall n, ~ IsInt l123' n.
Axiom l4_not_int : forall n, ~ IsInt l4 n.
Axiom l4'_not_int : forall n, ~ IsInt l4' n.

Example test_case_new:
  filter_integers_spec [a0; s2; s22; obj; l123; l123'; l4; l4'] [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply a0_is_int.
  - eapply fir_cons_nonint; [apply s2_not_int |].
    eapply fir_cons_nonint; [apply s22_not_int |].
    eapply fir_cons_nonint; [apply obj_not_int |].
    eapply fir_cons_nonint; [apply l123_not_int |].
    eapply fir_cons_nonint; [apply l123'_not_int |].
    eapply fir_cons_nonint; [apply l4_not_int |].
    eapply fir_cons_nonint; [apply l4'_not_int |].
    constructor.
Qed.