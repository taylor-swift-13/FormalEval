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

Parameter v3 c a b : Any.
Parameter n3 : int.
Axiom IsInt_v3 : IsInt v3 n3.
Axiom NotInt_c : forall n, ~ IsInt c n.
Axiom NotInt_a : forall n, ~ IsInt a n.
Axiom NotInt_b : forall n, ~ IsInt b n.

Example test_case_mixed: filter_integers_spec [v3; c; v3; v3; a; b] [n3; n3; n3].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NotInt_c|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NotInt_a|].
  eapply fir_cons_nonint; [apply NotInt_b|].
  apply fir_nil.
Qed.